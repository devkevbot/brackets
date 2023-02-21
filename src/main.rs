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

const MAX_PLAYER_SKILL: u8 = 99;

#[derive(Debug, Clone)]
struct Player {
    name: String,
    skill: u8,
}

impl Player {
    fn new() -> Self {
        // Skill from 0-99
        let skill = rand::random::<u8>() % (MAX_PLAYER_SKILL + 1);

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

    fn calculate_player_power(skill: u8, apply_skill_boost: bool) -> u8 {
        let skill_boost: u8 = 5;

        if apply_skill_boost {
            return std::cmp::min(skill + skill_boost, MAX_PLAYER_SKILL);
        }

        skill
    }

    fn determine_winner(&self) -> Player {
        let player_one_power = Self::calculate_player_power(self.players[0].skill, rand::random());
        let player_two_power = Self::calculate_player_power(self.players[1].skill, rand::random());

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
        let players_in_match = 2;

        Self {
            games: initial_player_pool
                .chunks(players_in_match)
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

#[derive(Debug, PartialEq)]
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
    fn test_calculate_player_power() {
        assert_eq!(
            Game::calculate_player_power(MAX_PLAYER_SKILL, false),
            MAX_PLAYER_SKILL
        );
        assert_eq!(Game::calculate_player_power(0, false), 0);
        assert_eq!(
            Game::calculate_player_power(MAX_PLAYER_SKILL, true),
            MAX_PLAYER_SKILL
        );
        assert_eq!(Game::calculate_player_power(0, true), 5);
        assert_eq!(Game::calculate_player_power(94, true), MAX_PLAYER_SKILL);
    }

    #[test]
    fn test_bracket_creation() {
        let num_players = 2;
        let bracket = Bracket::new(num_players);
        assert!(bracket.is_ok());

        let num_players = 3;
        let bracket = Bracket::new(num_players);
        assert!(bracket.is_err());
        if let Err(error) = bracket {
            assert_eq!(error, BracketError::InvalidNumPlayers(num_players))
        };
    }

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

    #[test]
    fn test_rounds_required() {
        let bracket = Bracket::new(1).unwrap();
        assert_eq!(bracket.rounds_required(), 0);

        let bracket = Bracket::new(2).unwrap();
        assert_eq!(bracket.rounds_required(), 1);

        let bracket = Bracket::new(4).unwrap();
        assert_eq!(bracket.rounds_required(), 2);

        let bracket = Bracket::new(8).unwrap();
        assert_eq!(bracket.rounds_required(), 3);

        let bracket = Bracket::new(16).unwrap();
        assert_eq!(bracket.rounds_required(), 4);
    }
}
