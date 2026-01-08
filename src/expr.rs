#![allow(dead_code)]
use std::collections::BTreeMap;
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

pub fn evaluate(expr: Expr, valuation: &Map) -> Result<bool, String> {
    match expr {
        Expr::True => Ok(true),
        Expr::False => Ok(false),
        Expr::Neg(e) => evaluate(*e, valuation).map(|x| !x),
        Expr::Conj(e1, e2) => Ok(evaluate(*e1, valuation)? && evaluate(*e2, valuation)?),
        Expr::Disj(e1, e2) => Ok(evaluate(*e1, valuation)? || evaluate(*e2, valuation)?),
        Expr::Variable(s) => valuation
            .get(&s)
            .copied()
            .ok_or(format!("Variable not found: {s}")),
    }
}

#[test]
fn example_eval() {
    let expr = Expr::Conj(
        Box::new(Expr::True),
        Box::new(Expr::Disj(
            Box::new(Expr::Variable('X')),
            Box::new(Expr::False),
        )),
    );

    let mut valuation = Map::new();
    valuation.insert('X', true);
    valuation.insert('Y', false);

    let res = evaluate(expr, &valuation);
    assert!(res == Ok(true));
}

// TODO(performance): don't use Vec
pub fn collect_vars(expr: Expr) -> Vec<char> {
    match expr {
        Expr::Variable(v) => vec![v],
        Expr::Neg(e) => collect_vars(*e),
        Expr::Disj(e1, e2) | Expr::Conj(e1, e2) => {
            let mut vs1 = collect_vars(*e1);
            let vs2 = collect_vars(*e2);
            vs1.extend(vs2);
            vs1
        }
        Expr::True | Expr::False => Vec::new(),
    }
}
