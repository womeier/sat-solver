#![allow(dead_code)]
use crate::expr::*;
use crate::sat_naive::SAT_SOLVER_NAIVE;

#[derive(Debug, Clone, PartialEq)]
enum State {
    Idle,
    AcceptingExpr,
    Ready(Expr),
    Done(Option<Map>),
}

#[derive(Debug, Clone)]
enum Command {
    Begin,
    GotExpr(Expr),
    Compute,
    End,
}

fn process_command(state: State, com: Command) -> Option<State> {
    match (state, com) {
        (State::Idle, Command::Begin) => Some(State::AcceptingExpr),
        (State::AcceptingExpr, Command::GotExpr(e)) => Some(State::Ready(e)),
        (State::Ready(e), Command::Compute) => Some(State::Done((SAT_SOLVER_NAIVE.solve)(&e))),
        (_, Command::End) => Some(State::Idle),
        (_, _) => None,
    }
}

fn process_commands(state: State, coms: &[Command]) -> Option<State> {
    if coms.is_empty() {
        return Some(state);
    }

    let c = &coms[0];
    let cs = &coms[1..];

    let new_state = process_command(state, c.clone())?;
    process_commands(new_state, cs)
}

#[test]
fn example_process_commands() {
    let expr = parse_expr("(T & (x | F))").unwrap().1;

    // State

    let initial_state = State::Idle;
    let comms = [
        Command::Begin,
        Command::End,
        Command::Begin,
        Command::GotExpr(expr),
        Command::Compute,
    ];

    let result_state = process_commands(initial_state, &comms);

    match &result_state {
        Some(succ) => println!("Resulting state: {succ:?}"),
        None => println!("Processing commands failed."),
    }

    assert!(format!("{result_state:?}") == "Some(Done(Some(Map([Entry { key: 120, value: true }]))))");
}
