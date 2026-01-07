use expr_eval_server::expr::*;
use expr_eval_server::sat::*;

#[derive(Debug, Clone, PartialEq)]
enum State {
    Idle,
    AcceptingExpr,
    AcceptingMap(Expr),
    Ready(Expr, Map),
    Done(Result<bool, String>),
}

#[derive(Debug, Clone)]
enum Command {
    Begin,
    GotExpr(Expr),
    GotMap(Map),
    Compute,
    End,
}

fn process_command(state: State, com: Command) -> Option<State> {
    match (state, com) {
        (State::Idle, Command::Begin) => Some(State::AcceptingExpr),
        (State::AcceptingExpr, Command::GotExpr(e)) => Some(State::AcceptingMap(e)),
        (State::AcceptingMap(e), Command::GotMap(m)) => Some(State::Ready(e, m)),
        (State::Ready(e, m), Command::Compute) => Some(State::Done(evaluate(e, &m))),
        (_, Command::End) => Some(State::Idle),
        (_, _) => None,
    }
}

fn process_commands(state: State, coms: Vec<Command>) -> Option<State> {
    match coms.as_slice() {
        [] => Some(state),
        [c, cs @ ..] => {
            let new_state = process_command(state, c.clone())?;
            process_commands(new_state, cs.to_vec().clone())
        }
    }
}

fn example_process_commands() {
    let expr = Expr::Conj(
        Box::new(Expr::True),
        Box::new(Expr::Disj(
            Box::new(Expr::Variable("X".to_string())),
            Box::new(Expr::False),
        )),
    );

    let mut valuation = Map::new();
    valuation.insert("X".to_string(), true);
    //  valuation.insert("X".to_string(), false);

    // State

    let initial_state = State::Idle;
    let comms = [
        Command::Begin,
        Command::End,
        Command::Begin,
        Command::GotExpr(expr),
        Command::GotMap(valuation),
        Command::Compute,
    ];

    let result_state = process_commands(initial_state, comms.to_vec());

    match &result_state {
        Some(succ) => println!("Resulting state: {succ:?}"),
        None => println!("Processing commands failed."),
    }

    assert!(result_state == Some(State::Done(Ok(true))));
}

fn main() {
    example_process_commands();
    example_naive_solve_sat();
}
