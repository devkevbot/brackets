mod brackets;

use crate::brackets::*;

fn main() {
    let num_players = 32;

    match Bracket::new(num_players) {
        Err(e) => {
            eprintln!("{}", e)
        }
        Ok(bracket) => {
            let results = bracket.simulate();
            println!("Total players: {}", results.num_players);
            println!("Total rounds: {}", results.num_rounds);
            println!("Winner: {}", results.winner);
        }
    }
}
