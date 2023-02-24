mod brackets;

use crate::brackets::*;

fn main() {
    let num_players = 32;

    match Bracket::new(num_players, RoundType::BestOfN(3)) {
        Err(e) => {
            eprintln!("{}", e)
        }
        Ok(mut bracket) => {
            let results = bracket.simulate();
            println!("Total players: {}", results.num_players);
            println!("Total rounds: {}", results.num_rounds);
            println!("Min games required: {}", bracket.min_games_required());
            println!("Total games: {}", results.num_games);
            println!("Winner: {}", results.winner);
        }
    }
}
