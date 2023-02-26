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
//! match Bracket::new(num_players, BracketType::SingleElimination(RoundType::BestOfN(1))) {
//!     Err(e) => {
//!         eprintln!("{}", e)
//!     }
//!     Ok(mut bracket) => {
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
    num_games_played: u32,
    bracket_type: BracketType,
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
    /// use brackets::*;
    /// let bracket = Bracket::new(8, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
    /// ```
    ///
    /// ## Bad
    /// ```should_panic
    /// use brackets::*;
    /// // Will panic because 9 is not a positive power of 2!
    /// let bracket = Bracket::new(9, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
    /// ```
    pub fn new(num_players: u8, bracket_type: BracketType) -> Result<Self, BracketCreationError> {
        if !Self::is_positive_power_of_two(num_players) {
            return Err(BracketCreationError::InvalidNumPlayers(num_players));
        }

        match bracket_type {
            BracketType::SingleElimination(round_type) => match round_type {
                RoundType::BestOfN(n) => {
                    if n % 2 == 0 {
                        return Err(BracketCreationError::InvalidBestOfN(num_players));
                    }

                    Ok(Self {
                        num_players,
                        num_games_played: 0,
                        bracket_type,
                    })
                }
            },
        }
    }

    fn is_positive_power_of_two(n: u8) -> bool {
        n > 0 && n & (n - 1) == 0
    }

    fn rounds_required(&self) -> u8 {
        (self.num_players as f32).log2().ceil() as u8
    }

    pub fn min_games_to_determine_winner(&self) -> u32 {
        match &self.bracket_type {
            BracketType::SingleElimination(round_type) => match round_type {
                RoundType::BestOfN(_) => {
                    ((self.num_players - 1) * round_type.series_win_threshold()) as u32
                }
            },
        }
    }

    fn determine_winner(&mut self) -> Player {
        let mut next_round_player_pool = (1u8..=self.num_players)
            .map(|_| Player::new())
            .collect::<Vec<_>>();

        let BracketType::SingleElimination(round_type) = &self.bracket_type;

        // Simulate each round one at a time.
        for _ in 1..=self.rounds_required() {
            let round = Round::new(next_round_player_pool, *round_type);
            let sim_results = round.simulate();
            next_round_player_pool = sim_results.0;
            self.num_games_played += sim_results.1;
        }

        // After the final round, we're down to one last player: the winner.
        next_round_player_pool
            .pop()
            .expect("Expected to find a bracket winner")
    }

    /// Simulated the bracket and returns the results in the form of a `BracketSimulationResult`.
    ///
    /// # Examples
    ///
    /// ```
    /// use brackets::*;
    /// let mut bracket = Bracket::new(8, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
    /// let results = bracket.simulate();
    /// println!("{:?}", results);
    /// ```
    pub fn simulate(&mut self) -> BracketSimulationResult {
        let winner = self.determine_winner();

        BracketSimulationResult {
            num_players: self.num_players,
            num_rounds: self.rounds_required(),
            num_games: self.num_games_played,
            winner: winner.name,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum BracketType {
    SingleElimination(RoundType),
}

/// Describes an error that occured during creation of the `Bracket`.
#[derive(Debug, PartialEq)]
pub enum BracketCreationError {
    /// Returned when the number of players supplied to the bracket is invalid.
    /// The number of players supplied to the bracket must always be a positive power of 2.
    InvalidNumPlayers(u8),
    /// Returned when the 'n' in a 'Best of n' series is an even number.
    InvalidBestOfN(u8),
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
            BracketCreationError::InvalidBestOfN(n) => {
                write!(
                    f,
                    "A Best Of series must be played through an odd number of games, but got {} games instead",
                    n
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
    pub num_games: u32,
    pub winner: String,
}

#[derive(Debug, Clone)]
struct Round {
    matchups: Vec<PlayerPair>,
    round_type: RoundType,
}

#[derive(Debug, Copy, Clone)]
pub enum RoundType {
    BestOfN(u8),
}

impl RoundType {
    fn series_win_threshold(&self) -> u8 {
        match self {
            Self::BestOfN(n) => (n / 2) + 1,
        }
    }
}

impl Round {
    fn new(initial_player_pool: Vec<Player>, round_type: RoundType) -> Self {
        Self {
            matchups: initial_player_pool
                .chunks(PLAYERS_PER_MATCH)
                .map(|chunk| chunk.to_vec().try_into().unwrap())
                .collect::<Vec<PlayerPair>>(),
            round_type,
        }
    }

    fn simulate_series(&self, matchup: PlayerPair, num_games_in_series: u8) -> (Player, u32) {
        let series_win_threshold = self.round_type.series_win_threshold();

        let mut games_played: Vec<Game> = vec![];

        let mut player_wins_in_series: [u8; 2] = [0, 0];

        for _ in 1..=num_games_in_series {
            if player_wins_in_series[0] == series_win_threshold
                || player_wins_in_series[1] == series_win_threshold
            {
                break;
            }

            let game = Game::new(matchup.clone());

            let winner = game.simulate();
            if winner == matchup[0] {
                player_wins_in_series[0] += 1;
            } else {
                player_wins_in_series[1] += 1;
            }

            games_played.push(game);
        }

        let series_winner_index = if player_wins_in_series[0] > player_wins_in_series[1] {
            0
        } else {
            1
        };
        let series_winner = matchup[series_winner_index].clone();

        (series_winner, games_played.len() as u32)
    }

    fn determine_winner(&self) -> (Vec<Player>, u32) {
        let mut games_played_in_round: u32 = 0;
        let mut winners_player_pool: Vec<Player> = vec![];

        for matchup in &self.matchups {
            match self.round_type {
                RoundType::BestOfN(n) => {
                    let (winner, games_played_in_series) = self.simulate_series(matchup.clone(), n);
                    games_played_in_round += games_played_in_series;
                    winners_player_pool.push(winner);
                }
            }
        }

        (winners_player_pool, games_played_in_round)
    }

    fn simulate(&self) -> (Vec<Player>, u32) {
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
            return std::cmp::min(skill + skill_boost, Player::max_player_skill());
        }

        skill
    }

    fn determine_winner(&self) -> Player {
        let player_one = self.players[0].clone();
        let player_two = self.players[1].clone();

        let player_one_power = Self::calculate_player_power(player_one.skill, rand::random());
        let player_two_power = Self::calculate_player_power(player_two.skill, rand::random());

        if player_one_power > player_two_power {
            return player_one;
        }

        player_two
    }

    fn simulate(&self) -> Player {
        self.determine_winner()
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Player {
    name: String,
    skill: u8,
}

impl Player {
    fn new() -> Self {
        let skill = rand::random::<u8>() % (Self::max_player_skill() + 1);

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

    pub fn max_player_skill() -> u8 {
        99
    }
}

const PLAYERS_PER_MATCH: usize = 2;
type PlayerPair = [Player; PLAYERS_PER_MATCH];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_calculate_player_power() {
        assert_eq!(
            Game::calculate_player_power(Player::max_player_skill(), false),
            Player::max_player_skill()
        );
        assert_eq!(Game::calculate_player_power(0, false), 0);
        assert_eq!(
            Game::calculate_player_power(Player::max_player_skill(), true),
            Player::max_player_skill()
        );
        assert!(Game::calculate_player_power(0, true) > 0);
        assert_eq!(
            Game::calculate_player_power(Player::max_player_skill(), true),
            Player::max_player_skill()
        );
    }

    #[test]
    fn test_bracket_creation() {
        let num_players = 2;
        let bracket = Bracket::new(
            num_players,
            BracketType::SingleElimination(RoundType::BestOfN(1)),
        );
        assert!(bracket.is_ok());

        let num_players = 3;
        let bracket = Bracket::new(
            num_players,
            BracketType::SingleElimination(RoundType::BestOfN(1)),
        );
        assert!(bracket.is_err());
        if let Err(error) = bracket {
            assert_eq!(error, BracketCreationError::InvalidNumPlayers(num_players))
        };

        let num_players = 2;
        let n = 2;
        let bracket = Bracket::new(
            num_players,
            BracketType::SingleElimination(RoundType::BestOfN(n)),
        );
        assert!(bracket.is_err());
        if let Err(error) = bracket {
            assert_eq!(error, BracketCreationError::InvalidBestOfN(n))
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
        let bracket =
            Bracket::new(1, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
        assert_eq!(bracket.rounds_required(), 0);

        let bracket =
            Bracket::new(2, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
        assert_eq!(bracket.rounds_required(), 1);

        let bracket =
            Bracket::new(4, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
        assert_eq!(bracket.rounds_required(), 2);

        let bracket =
            Bracket::new(8, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
        assert_eq!(bracket.rounds_required(), 3);

        let bracket =
            Bracket::new(16, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
        assert_eq!(bracket.rounds_required(), 4);
    }

    #[test]
    fn test_min_games_required() {
        let bracket =
            Bracket::new(32, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
        assert_eq!(bracket.min_games_to_determine_winner(), 31);

        let bracket =
            Bracket::new(32, BracketType::SingleElimination(RoundType::BestOfN(3))).unwrap();
        assert_eq!(bracket.min_games_to_determine_winner(), 62);

        let bracket =
            Bracket::new(32, BracketType::SingleElimination(RoundType::BestOfN(5))).unwrap();
        assert_eq!(bracket.min_games_to_determine_winner(), 93);
    }
}
