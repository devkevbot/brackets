mod brackets;

use crate::brackets::*;

fn main() {
    let bracket = Bracket::new(
        BracketType::SingleElimination(2),
        SeriesType::FixedLength(3),
    );
    // dbg!(bracket);
    bracket.simulate();
}

// fn main() {
//     let num_players = 32;

//     match Bracket::new(
//         num_players,
//         BracketType::SingleElimination(RoundType::BestOfN(3)),
//     ) {
//         Err(e) => {
//             eprintln!("{}", e)
//         }
//         Ok(mut bracket) => {
//             let results = bracket.simulate();
//             println!("Total players: {}", results.num_players);
//             println!("Total rounds: {}", results.num_rounds);
//             println!(
//                 "Min games required: {}",
//                 bracket.min_games_to_determine_winner()
//             );
//             println!("Total games: {}", results.num_games);
//             println!("Winner: {}", results.winner);
//         }
//     }
// }
