//! Reader for the DIMACS CNF format, which is what every SAT benchmark suite
//! (SATLIB, the DIMACS challenge sets, the SAT competition archives) speaks.
//!
//! A formula is returned as an `Expr` -- a conjunction of disjunctions of
//! (possibly negated) variables -- so the existing solvers can run on it
//! unchanged. Feeding such an `Expr` through `cnf::to_cnf` costs nothing: it is
//! already in CNF, so no `Disj` ever sits above a `Conj` and the distribution
//! step never fires.
//!
//! Variables are `Expr::Variable(u8)`, so instances may use at most 255
//! variables; anything larger is rejected rather than silently truncated. That
//! covers SATLIB's uf20/uf50/uf100/uf250 families (and `uf250` only just).
//!
//! This module is excluded from the Lean extraction, like `expr.rs`'s parser:
//! it is I/O plumbing around the verified core, not part of it.

use crate::expr::Expr;
use std::fmt;

/// The largest variable index `Expr::Variable(u8)` can hold.
pub const MAX_VAR: i64 = 255;

#[derive(Debug, Clone, PartialEq)]
pub enum DimacsError {
    /// No `p cnf <vars> <clauses>` line was found.
    MissingHeader,
    /// The `p` line was present but malformed.
    BadHeader(String),
    /// A token in the clause body was not an integer.
    BadToken(String),
    /// A variable index of 0 (DIMACS reserves it as the clause terminator) or
    /// one beyond what `u8` can hold.
    VarOutOfRange(i64),
    /// The file ended mid-clause (no terminating `0`).
    UnterminatedClause,
    /// The header's clause count disagrees with the body.
    ClauseCountMismatch { declared: usize, found: usize },
}

impl fmt::Display for DimacsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingHeader => write!(f, "missing `p cnf` header"),
            Self::BadHeader(l) => write!(f, "malformed header: {l:?}"),
            Self::BadToken(t) => write!(f, "not an integer: {t:?}"),
            Self::VarOutOfRange(n) => {
                write!(f, "variable {n} out of range (1..={MAX_VAR})")
            }
            Self::UnterminatedClause => write!(f, "file ends mid-clause"),
            Self::ClauseCountMismatch { declared, found } => {
                write!(f, "header declares {declared} clauses, found {found}")
            }
        }
    }
}

fn literal(n: i64) -> Result<Expr, DimacsError> {
    let var = n.abs();
    if var == 0 || var > MAX_VAR {
        return Err(DimacsError::VarOutOfRange(n));
    }
    let atom = Expr::Variable(var as u8);
    if n < 0 {
        Ok(Expr::Neg(Box::new(atom)))
    } else {
        Ok(atom)
    }
}

/// An empty disjunction is false, so an empty clause makes the formula
/// unsatisfiable -- exactly the DIMACS reading.
fn disjunction(literals: Vec<Expr>) -> Expr {
    let mut it = literals.into_iter();
    match it.next() {
        None => Expr::False,
        Some(first) => it.fold(first, |acc, lit| Expr::Disj(Box::new(acc), Box::new(lit))),
    }
}

/// An empty conjunction is true, so a clause-free formula is trivially
/// satisfiable.
fn conjunction(clauses: Vec<Expr>) -> Expr {
    let mut it = clauses.into_iter();
    match it.next() {
        None => Expr::True,
        Some(first) => it.fold(first, |acc, cl| Expr::Conj(Box::new(acc), Box::new(cl))),
    }
}

/// Parses a DIMACS CNF formula.
///
/// Tolerates the usual real-world sloppiness: `c` comment lines, extra
/// whitespace in the header, clauses spread over several lines or several
/// clauses on one line, and SATLIB's trailing `%` line (everything from `%`
/// onward is ignored -- those files end with `%` followed by a stray `0`, which
/// would otherwise read as an extra empty clause and turn every instance
/// unsatisfiable).
pub fn parse_dimacs(input: &str) -> Result<Expr, DimacsError> {
    let mut declared: Option<usize> = None;
    let mut clauses: Vec<Expr> = Vec::new();
    let mut current: Vec<Expr> = Vec::new();
    let mut in_clause = false;

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('%') {
            break;
        }
        if let Some(rest) = line.strip_prefix('p') {
            let mut fields = rest.split_whitespace();
            match (fields.next(), fields.next(), fields.next()) {
                (Some("cnf"), Some(vars), Some(nclauses)) => {
                    // The variable count is validated but not enforced: a file may
                    // legitimately declare more variables than it uses, and the
                    // `u8` bound is checked per literal instead.
                    vars.parse::<usize>()
                        .map_err(|_| DimacsError::BadHeader(line.to_string()))?;
                    declared = Some(
                        nclauses
                            .parse()
                            .map_err(|_| DimacsError::BadHeader(line.to_string()))?,
                    );
                }
                _ => return Err(DimacsError::BadHeader(line.to_string())),
            }
            continue;
        }

        for token in line.split_whitespace() {
            let n: i64 = token
                .parse()
                .map_err(|_| DimacsError::BadToken(token.to_string()))?;
            if n == 0 {
                clauses.push(disjunction(std::mem::take(&mut current)));
                in_clause = false;
            } else {
                current.push(literal(n)?);
                in_clause = true;
            }
        }
    }

    if in_clause {
        return Err(DimacsError::UnterminatedClause);
    }
    let declared = declared.ok_or(DimacsError::MissingHeader)?;
    if declared != clauses.len() {
        return Err(DimacsError::ClauseCountMismatch {
            declared,
            found: clauses.len(),
        });
    }

    Ok(conjunction(clauses))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{Map, evaluate};

    #[test]
    fn parses_a_minimal_formula() {
        // (1 ∨ ¬2) ∧ (2)
        let expr = parse_dimacs("p cnf 2 2\n1 -2 0\n2 0\n").unwrap();
        let mut val = Map::new();
        val.insert(1, true);
        val.insert(2, true);
        assert_eq!(evaluate(&expr, &val), Ok(true));
        val.insert(1, false);
        assert_eq!(evaluate(&expr, &val), Ok(false));
    }

    #[test]
    fn ignores_comments_and_tolerates_header_whitespace() {
        let expr = parse_dimacs("c generated by mcnf\nc\np cnf 1  1 \n1 0\n").unwrap();
        assert_eq!(expr, Expr::Variable(1));
    }

    #[test]
    fn accepts_clauses_split_across_lines_and_joined_on_one() {
        let split = parse_dimacs("p cnf 3 2\n1 2\n3 0 -1\n-2 0\n").unwrap();
        let joined = parse_dimacs("p cnf 3 2\n1 2 3 0 -1 -2 0\n").unwrap();
        assert_eq!(split, joined);
    }

    #[test]
    fn stops_at_the_satlib_percent_trailer() {
        // Without the `%` cutoff the trailing `0` would read as an empty clause
        // and make the formula unsatisfiable.
        let expr = parse_dimacs("p cnf 1 1\n1 0\n%\n0\n").unwrap();
        assert_eq!(expr, Expr::Variable(1));
    }

    #[test]
    fn an_empty_clause_is_false_and_no_clauses_is_true() {
        assert_eq!(parse_dimacs("p cnf 1 1\n0\n").unwrap(), Expr::False);
        assert_eq!(parse_dimacs("p cnf 0 0\n").unwrap(), Expr::True);
    }

    #[test]
    fn negative_literals_become_negations() {
        assert_eq!(
            parse_dimacs("p cnf 1 1\n-1 0\n").unwrap(),
            Expr::Neg(Box::new(Expr::Variable(1)))
        );
    }

    #[test]
    fn rejects_a_missing_header() {
        assert_eq!(parse_dimacs("1 -2 0\n"), Err(DimacsError::MissingHeader));
    }

    #[test]
    fn rejects_a_malformed_header() {
        assert!(matches!(
            parse_dimacs("p cnf two 1\n1 0\n"),
            Err(DimacsError::BadHeader(_))
        ));
        assert!(matches!(
            parse_dimacs("p wcnf 1 1\n1 0\n"),
            Err(DimacsError::BadHeader(_))
        ));
    }

    #[test]
    fn rejects_a_non_integer_token() {
        assert_eq!(
            parse_dimacs("p cnf 1 1\n1 x 0\n"),
            Err(DimacsError::BadToken("x".to_string()))
        );
    }

    #[test]
    fn rejects_variables_beyond_u8() {
        assert_eq!(
            parse_dimacs("p cnf 256 1\n256 0\n"),
            Err(DimacsError::VarOutOfRange(256))
        );
        assert_eq!(
            parse_dimacs("p cnf 256 1\n-300 0\n"),
            Err(DimacsError::VarOutOfRange(-300))
        );
    }

    #[test]
    fn rejects_an_unterminated_clause() {
        assert_eq!(
            parse_dimacs("p cnf 2 1\n1 2\n"),
            Err(DimacsError::UnterminatedClause)
        );
    }

    #[test]
    fn rejects_a_clause_count_mismatch() {
        assert_eq!(
            parse_dimacs("p cnf 2 3\n1 0\n2 0\n"),
            Err(DimacsError::ClauseCountMismatch {
                declared: 3,
                found: 2
            })
        );
    }
}
