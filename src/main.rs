use rand::prelude::*;
use std::error::Error;
use std::fmt::Display;

fn main() {
    let num_players = 32;

    match Bracket::new(num_players) {
        Err(e) => {
            eprintln!("{}", e)
        }
        Ok(mut bracket) => bracket.simulate(),
    }
}

#[derive(Debug, Clone)]
struct Player {
    name: String,
    skill: f64,
}

impl Player {
    fn new() -> Self {
        let mut rng = rand::thread_rng();

        let skill_seed: f64 = rng.gen();
        let skill = 10f64 * skill_seed;

        let names = vec![
            "Alice", "Bob", "Charlie", "Dave", "Emily", "Filip", "George", "Helena",
        ];
        let index = rand::random::<u8>() as usize % names.len();
        let name = names[index];
        let name_suffix = rand::random::<u8>();

        Self {
            skill,
            name: format!("{}-{}", name, name_suffix),
        }
    }
}

#[derive(Debug, Clone)]
struct Game {
    players: Vec<Player>,
}

impl Game {
    fn new(players: Vec<Player>) -> Self {
        Self { players }
    }

    fn calculate_player_power(&self, skill: f64) -> f64 {
        let mut rng = rand::thread_rng();
        let boost_factor: f64 = 10.0;
        let boost_multiplier: f64 = rng.gen();
        skill + boost_factor * boost_multiplier
    }

    fn determine_winner(&self) -> Player {
        let player_one_power = self.calculate_player_power(self.players[0].skill);
        let player_two_power = self.calculate_player_power(self.players[1].skill);

        if player_one_power > player_two_power {
            return self.players[0].clone();
        }

        self.players[1].clone()
    }

    fn simulate(&self) -> Player {
        self.determine_winner()
    }
}

#[derive(Debug, Clone)]
struct Round {
    games: Vec<Game>,
    winners_player_pool: Vec<Player>,
}

impl Round {
    fn new(initial_player_pool: Vec<Player>) -> Self {
        Self {
            games: initial_player_pool
                .chunks(2)
                .map(|chunk| Game::new(chunk.to_vec()))
                .collect::<Vec<_>>(),
            winners_player_pool: vec![],
        }
    }

    fn determine_winner(&mut self) -> Vec<Player> {
        for game in &self.games {
            let winner = game.simulate();
            self.winners_player_pool.push(winner)
        }

        self.winners_player_pool.clone()
    }

    fn simulate(&mut self) -> Vec<Player> {
        self.determine_winner()
    }
}

#[derive(Debug)]
enum BracketError {
    InvalidNumPlayers(u8),
}

impl Display for BracketError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            BracketError::InvalidNumPlayers(num_players) => {
                write!(
                    f,
                    "expected number of players in the bracket to be a positive power of 2, got {}",
                    num_players
                )
            }
        }
    }
}

impl Error for BracketError {}

#[derive(Debug)]
struct Bracket {
    num_players: u8,
    rounds: Vec<Round>,
}

impl Bracket {
    fn new(num_players: u8) -> Result<Self, BracketError> {
        if !Self::is_positive_power_of_two(num_players) {
            return Err(BracketError::InvalidNumPlayers(num_players));
        }

        Ok(Self {
            num_players,
            rounds: vec![],
        })
    }

    fn is_positive_power_of_two(n: u8) -> bool {
        n > 0 && n & (n - 1) == 0
    }

    fn rounds_required(&self) -> u8 {
        (self.num_players as f32).log2().ceil() as u8
    }

    fn determine_winner(&mut self) -> Player {
        let mut next_round_player_pool = (1u8..=self.num_players)
            .map(|_| Player::new())
            .collect::<Vec<_>>();

        for round_number in 1..=self.rounds_required() {
            let mut round = Round::new(next_round_player_pool);

            next_round_player_pool = round.simulate();
            self.rounds.push(round.clone());

            println!("Round {round_number} winner(s):");
            println!("{:#?}", next_round_player_pool);
            println!();
        }

        next_round_player_pool[0].clone()
    }

    fn simulate(&mut self) {
        println!(
            "Simulation details: {} players, {} round(s) required\n",
            self.num_players,
            self.rounds_required()
        );

        let winner = self.determine_winner();
        println!("Winner: {:?}", winner);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_positive_power_of_two() {
        assert!(Bracket::is_positive_power_of_two(1));
        assert!(Bracket::is_positive_power_of_two(2));
        assert!(Bracket::is_positive_power_of_two(4));
        assert!(Bracket::is_positive_power_of_two(8));
        assert!(Bracket::is_positive_power_of_two(16));
        assert!(Bracket::is_positive_power_of_two(32));
        assert!(Bracket::is_positive_power_of_two(64));
        assert!(Bracket::is_positive_power_of_two(128));

        assert!(!Bracket::is_positive_power_of_two(0));
        assert!(!Bracket::is_positive_power_of_two(3));
        assert!(!Bracket::is_positive_power_of_two(69));
    }
}
