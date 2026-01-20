#![allow(dead_code)]
use nom::{
    branch::alt,
    character::complete::{multispace0, one_of},
    combinator::map,
    sequence::{delimited, preceded, separated_pair},
    IResult, Parser,
};
use std::collections::{BTreeMap, HashSet};
use std::fmt;

pub type Map = BTreeMap<char, bool>;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    True,
    False,
    Variable(char),
    Conj(Box<Expr>, Box<Expr>),
    Disj(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Neg(e) => write!(f, "¬{}", *e),
            Self::True => write!(f, "⊤"),
            Self::False => write!(f, "⊥"),
            Self::Variable(v) => write!(f, "{}", v),
            Self::Conj(e1, e2) => write!(f, "({} ∧ {})", e1, e2),
            Self::Disj(e1, e2) => write!(f, "({} ∨ {})", e1, e2),
        }
    }
}

// PARSER for Expr

fn parse_bool(i: &str) -> IResult<&str, Expr> {
    let (i, t) = one_of("⊤⊥TF")(i)?;

    Ok((
        i,
        match t {
            'F' | '⊥' => Expr::False,
            '⊤' | 'T' => Expr::True,
            _ => unreachable!(),
        },
    ))
}

fn parse_var(i: &str) -> IResult<&str, Expr> {
    map(one_of("abcdefghijklmnopqrstuvwxyz"), Expr::Variable).parse(i)
}

fn parse_neg(i: &str) -> IResult<&str, Expr> {
    preceded(one_of("~¬"), parse_expr)
        .map(|e| Expr::Neg(Box::new(e)))
        .parse(i)
}

fn parse_conj(i: &str) -> IResult<&str, Expr> {
    delimited(
        one_of("("),
        separated_pair(parse_expr, one_of("∧&"), parse_expr),
        one_of(")"),
    )
    .map(|(e1, e2)| Expr::Conj(Box::new(e1), Box::new(e2)))
    .parse(i)
}

fn parse_disj(i: &str) -> IResult<&str, Expr> {
    delimited(
        one_of("("),
        separated_pair(parse_expr, one_of("∨v|"), parse_expr),
        one_of(")"),
    )
    .map(|(e1, e2)| Expr::Disj(Box::new(e1), Box::new(e2)))
    .parse(i)
}

pub fn parse_expr(i: &str) -> IResult<&str, Expr> {
    delimited(
        multispace0,
        alt([parse_conj, parse_disj, parse_neg, parse_var, parse_bool]),
        multispace0,
    )
    .parse(i)
}

pub fn example_expr_sat() -> Expr {
    parse_expr("((T & ~y) & (x | F))").unwrap().1
}

pub fn example_expr_unsat() -> Expr {
    parse_expr("(T & (~x & x))").unwrap().1
}

// Evaluation

pub fn evaluate(expr: &Expr, valuation: &Map) -> Result<bool, String> {
    match expr {
        Expr::True => Ok(true),
        Expr::False => Ok(false),
        Expr::Neg(e) => evaluate(e, valuation).map(|x| !x),
        Expr::Conj(e1, e2) => Ok(evaluate(e1, valuation)? && evaluate(e2, valuation)?),
        Expr::Disj(e1, e2) => Ok(evaluate(e1, valuation)? || evaluate(e2, valuation)?),
        Expr::Variable(s) => valuation
            .get(s)
            .copied()
            .ok_or(format!("Variable not found: {s}")),
    }
}

#[test]
fn example_eval_sat() {
    let expr = example_expr_sat();

    let mut valuation = Map::new();
    valuation.insert('x', true);
    valuation.insert('y', false);

    let res = evaluate(&expr, &valuation);
    assert!(res == Ok(true));
}

fn collect_vars_aux(expr: Expr) -> HashSet<char> {
    match expr {
        Expr::Variable(v) => vec![v].into_iter().collect(),
        Expr::Neg(e) => collect_vars_aux(*e),
        Expr::Disj(e1, e2) | Expr::Conj(e1, e2) => {
            let mut vs1 = collect_vars_aux(*e1);
            let vs2 = collect_vars_aux(*e2);
            vs1.extend(vs2);
            vs1
        }
        Expr::True | Expr::False => HashSet::new(),
    }
}

pub fn collect_vars(expr: Expr) -> Vec<char> {
    let vars = collect_vars_aux(expr);
    vars.into_iter().collect()
}
