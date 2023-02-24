//! # Brackets
//!
//! Brackets simulates the progression of a generic tournament bracket.
//!
//! ## Basic concepts
//!
//! - A **bracket** is created using a specified positive number of players.
//! - The bracket progresses players through a series of **rounds**, each of which is composed of **games**.
//! - A game is a competitive simulation between a pair of **players**.
//! - The winning player from each game is carried forward to the next round; the process repeats until a single player remains.
//!
//! ## Examples
//! ```
//! use brackets::*;
//!
//! let num_players = 32;
//!
//! match Bracket::new(num_players) {
//!     Err(e) => {
//!         eprintln!("{}", e)
//!     }
//!     Ok(bracket) => {
//!         let results = bracket.simulate();
//!         println!("Total players: {}", results.num_players);
//!         println!("Total rounds: {}", results.num_rounds);
//!         println!("Winner: {}", results.winner);
//!     }
//!  }
//! ```

use std::error::Error;
use std::fmt::Display;

/// A generic tournament product consisting of `num_players` number of
/// players.
#[derive(Debug)]
pub struct Bracket {
    /// The number of players that will play in the bracket. Must be a
    /// positive power of 2, such as 2, 4, 8, 16, etc.
    num_players: u8,
}

impl Bracket {
    /// Returns either a bracket set up with `num_players` number of
    /// players, or a `BracketError`.
    ///
    /// # Arguments
    ///
    /// * `num_players` - The number of players. Must be a positive
    ///   power of 2, such as 2, 4, 8, 16, etc.
    ///
    /// # Examples
    ///
    /// ## Good
    /// ```
    /// use brackets::Bracket;
    /// let bracket = Bracket::new(8).unwrap();
    /// ```
    ///
    /// ## Bad
    /// ```should_panic
    /// use brackets::Bracket;
    /// // Will panic because 9 is not a positive power of 2!
    /// let bracket = Bracket::new(9).unwrap();
    /// ```
    pub fn new(num_players: u8) -> Result<Self, BracketCreationError> {
        if !Self::is_positive_power_of_two(num_players) {
            return Err(BracketCreationError::InvalidNumPlayers(num_players));
        }

        Ok(Self { num_players })
    }

    fn is_positive_power_of_two(n: u8) -> bool {
        n > 0 && n & (n - 1) == 0
    }

    fn rounds_required(&self) -> u8 {
        (self.num_players as f32).log2().ceil() as u8
    }

    fn determine_winner(&self) -> Player {
        let mut next_round_player_pool = (1u8..=self.num_players)
            .map(|_| Player::new())
            .collect::<Vec<_>>();

        for _ in 1..=self.rounds_required() {
            let round = Round::new(next_round_player_pool);
            next_round_player_pool = round.simulate();
        }

        next_round_player_pool[0].clone()
    }

    /// Simulated the bracket and returns the results in the form of a `BracketSimulationResult`.
    ///
    /// # Examples
    ///
    /// ```
    /// use brackets::Bracket;
    /// let bracket = Bracket::new(8).unwrap();
    /// let results = bracket.simulate();
    /// println!("{:?}", results);
    /// ```
    pub fn simulate(&self) -> BracketSimulationResult {
        BracketSimulationResult {
            num_players: self.num_players,
            num_rounds: self.rounds_required(),
            winner: self.determine_winner().name,
        }
    }
}

/// Describes an error that occured during creation of the `Bracket`.
#[derive(Debug, PartialEq)]
pub enum BracketCreationError {
    /// Returned when the number of players supplied to the bracket is invalid.
    /// The number of players supplied to the bracket must always be a positive power of 2.
    InvalidNumPlayers(u8),
}

impl Display for BracketCreationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            BracketCreationError::InvalidNumPlayers(num_players) => {
                write!(
                    f,
                    "expected number of players in the bracket to be a positive power of 2, got {}",
                    num_players
                )
            }
        }
    }
}

impl Error for BracketCreationError {}

/// The result of the simulation of the bracket, providing details on
/// how the bracket progressed and which player won.
#[derive(Debug)]
pub struct BracketSimulationResult {
    pub num_players: u8,
    pub num_rounds: u8,
    pub winner: String,
}

#[derive(Debug, Clone)]
struct Round {
    games: Vec<Game>,
}

impl Round {
    fn new(initial_player_pool: Vec<Player>) -> Self {
        let players_in_match = 2;

        Self {
            games: initial_player_pool
                .chunks(players_in_match)
                .map(|chunk| {
                    let chunk_vec = chunk.to_vec();
                    let chunk_array: PlayerPair = [chunk_vec[0].clone(), chunk_vec[1].clone()];
                    Game::new(chunk_array)
                })
                .collect::<Vec<_>>(),
        }
    }

    fn determine_winner(&self) -> Vec<Player> {
        let mut winners_player_pool: Vec<Player> = vec![];

        for game in &self.games {
            let winner = game.simulate();
            winners_player_pool.push(winner)
        }

        winners_player_pool
    }

    fn simulate(&self) -> Vec<Player> {
        self.determine_winner()
    }
}

#[derive(Debug, Clone)]
struct Game {
    players: PlayerPair,
}

impl Game {
    fn new(players: PlayerPair) -> Self {
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

type PlayerPair = [Player; 2];

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
            assert_eq!(error, BracketCreationError::InvalidNumPlayers(num_players))
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
