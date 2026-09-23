#![allow(dead_code)]
use nom::{
    IResult, Parser,
    branch::alt,
    character::complete::{multispace0, one_of},
    combinator::map,
    sequence::{delimited, preceded, separated_pair},
};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
struct Entry {
    key: u16,
    value: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Map(Vec<Entry>);

impl Map {
    pub fn new() -> Self {
        Map(Vec::new())
    }

    pub fn insert(&mut self, key: u16, value: bool) -> Option<bool> {
        for entry in self.0.iter_mut() {
            if entry.key == key {
                return Some(std::mem::replace(&mut entry.value, value));
            }
        }
        self.0.push(Entry { key, value });
        None
    }

    pub fn get(&self, key: &u16) -> Option<&bool> {
        for entry in self.0.iter() {
            if entry.key == *key {
                return Some(&entry.value);
            }
        }
        None
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    True,
    False,
    Variable(u16),
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
            // The parser's variables are the letters `a`..`z`, and print as
            // themselves; DIMACS variables are plain indices with no letter to
            // print, so they get an `x`-prefixed number instead.
            Self::Variable(v) => match u8::try_from(*v) {
                Ok(b) if b.is_ascii_lowercase() => write!(f, "{}", b as char),
                _ => write!(f, "x{v}"),
            },
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
    map(one_of("abcdefghijklmnopqrstuvwxyz"), |c: char| {
        Expr::Variable(c as u16)
    })
    .parse(i)
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

pub fn evaluate(expr: &Expr, valuation: &Map) -> Result<bool, ()> {
    match expr {
        Expr::True => Ok(true),
        Expr::False => Ok(false),
        Expr::Neg(e) => evaluate(e, valuation).map(|x| !x),
        Expr::Conj(e1, e2) => Ok(evaluate(e1, valuation)? && evaluate(e2, valuation)?),
        Expr::Disj(e1, e2) => Ok(evaluate(e1, valuation)? || evaluate(e2, valuation)?),
        Expr::Variable(s) => match valuation.get(s) {
            Some(b) => Ok(*b),
            None => Err(()),
        },
    }
}

/// Tests name variables by the letters the parser accepts; `Variable` holds a
/// `u16` index, so the letter has to be widened rather than written as `b'x'`.
#[cfg(test)]
pub const fn letter(c: char) -> u16 {
    c as u16
}

#[test]
fn example_eval_sat() {
    let expr = example_expr_sat();

    let mut valuation = Map::new();
    valuation.insert(letter('x'), true);
    valuation.insert(letter('y'), false);

    let res = evaluate(&expr, &valuation);
    assert!(res == Ok(true));
}

fn contains_var(vars: &[u16], v: u16) -> bool {
    for x in vars.iter() {
        if *x == v {
            return true;
        }
    }
    false
}

fn merge_vars(dst: &mut Vec<u16>, src: &[u16]) {
    for v in src.iter() {
        if !contains_var(dst, *v) {
            dst.push(*v);
        }
    }
}

fn collect_vars_aux(expr: &Expr) -> Vec<u16> {
    match expr {
        Expr::Variable(v) => {
            let mut vars = Vec::new();
            vars.push(*v);
            vars
        }
        Expr::Neg(e) => collect_vars_aux(e),
        Expr::Disj(e1, e2) | Expr::Conj(e1, e2) => {
            let mut vs1 = collect_vars_aux(e1);
            let vs2 = collect_vars_aux(e2);
            merge_vars(&mut vs1, &vs2);
            vs1
        }
        Expr::True | Expr::False => Vec::new(),
    }
}

pub fn collect_vars(expr: &Expr) -> Vec<u16> {
    collect_vars_aux(expr)
}
