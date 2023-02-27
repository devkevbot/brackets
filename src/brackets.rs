// Fundamental concepts:
//
// Bracket: a collection of round
// Round: a collection of series
// Series: consecutive games played between two teams within a round
// Game: played between two teams
// Team: one or more players
// Player: a competitor
//
// Two approaches:
// "Bottom up":
// - Create players, teams, games, series, rounds, and supply them to bracket, or
// "Top down":
// - Create bracket and generate players, teams, games, series, rounds, from there.

trait Simulate {
    type SimulationResult;

    fn simulate(&self) -> Self::SimulationResult;
}

#[derive(Debug, Clone, PartialEq)]
struct Player {
    name: String,
    skill: u8,
}

impl Player {
    const MAX_SKILL: u8 = 99;

    fn new() -> Self {
        let skill = rand::random::<u8>() % (Self::MAX_SKILL + 1);

        let names = vec![
            "Alice", "Bob", "Charlie", "Dave", "Emily", "Filip", "George", "Helena",
        ];
        let index = rand::random::<u8>() as usize % names.len();
        let name = names[index];
        let name_suffix = rand::random::<u8>();
        let name = format!("{}-{}", name, name_suffix);

        Self { name, skill }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Team {
    id: u64,
    players: Vec<Player>,
}

impl Team {
    const MAX_ROSTER_SIZE: u8 = 1;

    fn new(id: u64) -> Self {
        Self {
            id,
            players: (1..=Self::MAX_ROSTER_SIZE)
                .into_iter()
                .map(|_| Player::new())
                .collect::<Vec<_>>(),
        }
    }
}

#[derive(Debug, Clone)]
struct Game {
    id: u64,
    teams: [Team; 2],
}

impl Game {
    fn new(id: u64, teams: [Team; 2]) -> Self {
        Self { id, teams }
    }
}

impl Simulate for Game {
    type SimulationResult = GameResult;

    fn simulate(&self) -> GameResult {
        // TODO: do not hard code the result
        GameResult {
            winner: self.teams[0].clone(),
            score: [1, 0],
        }
    }
}

struct GameResult {
    winner: Team,
    score: [u8; 2],
}

#[derive(Debug, Clone)]
struct Series {
    series_type: SeriesType,
    teams: [Team; 2],
    games: Vec<Game>,
}

impl Series {
    fn new(series_type: SeriesType, teams: [Team; 2]) -> Self {
        let max_games = match series_type {
            SeriesType::BestOf(max_games) | SeriesType::FixedLength(max_games) => max_games as u64,
        };

        let games = (1u64..=max_games)
            .into_iter()
            .map(|id| Game::new(id, teams.clone()))
            .collect::<Vec<_>>();

        Self {
            series_type,
            teams,
            games,
        }
    }
}

impl Simulate for Series {
    type SimulationResult = SeriesResult;

    fn simulate(&self) -> Self::SimulationResult {
        let mut series_score: [u8; 2] = [0, 0];

        let wins_required = self.series_type.wins_required();

        for game in &self.games {
            if series_score[0] == wins_required || series_score[1] == wins_required {
                break;
            }

            let result = game.simulate();
            if result.winner == self.teams[0] {
                series_score[0] += 1;
            } else if result.winner == self.teams[1] {
                series_score[1] += 1;
            }
        }

        let winner = if series_score[0] > series_score[1] {
            self.teams[0].clone()
        } else {
            self.teams[1].clone()
        };

        Self::SimulationResult {
            winner,
            teams: self.teams.clone(),
            series_score,
        }
    }
}

#[derive(Debug)]
struct SeriesResult {
    winner: Team,
    teams: [Team; 2],
    series_score: [u8; 2],
}

#[derive(Debug, Clone, Copy)]
pub enum SeriesType {
    BestOf(u8),
    FixedLength(u8),
}

impl SeriesType {
    fn wins_required(&self) -> u8 {
        match &self {
            Self::BestOf(n) => (n / 2) + 1,
            Self::FixedLength(n) => *n,
        }
    }
}

#[derive(Debug)]
struct Round {
    series: Vec<Series>,
}

impl Round {
    fn new(series_type: SeriesType, teams: Vec<Team>) -> Self {
        let matchups = Self::organize_matchups(teams);

        let mut series = vec![];

        for matchup in matchups {
            series.push(Series::new(series_type, matchup));
        }

        Self { series }
    }

    fn organize_matchups(teams: Vec<Team>) -> Vec<[Team; 2]> {
        teams
            .chunks(2)
            .map(|chunk| chunk.to_vec().try_into().unwrap())
            .collect::<Vec<_>>()
    }
}

impl Simulate for Round {
    type SimulationResult = RoundResult;

    fn simulate(&self) -> Self::SimulationResult {
        let mut round_result = RoundResult::new();

        for series in &self.series {
            let result = series.simulate();
            round_result.winners.push(result.winner);
            round_result
                .scores
                .push((result.teams, result.series_score));
        }

        round_result
    }
}

#[derive(Debug, Clone)]
struct RoundResult {
    winners: Vec<Team>,
    scores: Vec<([Team; 2], [u8; 2])>,
}

impl RoundResult {
    fn new() -> Self {
        Self {
            winners: vec![],
            scores: vec![],
        }
    }
}

#[derive(Debug)]
pub struct Bracket {
    bracket_type: BracketType,
    series_type: SeriesType,
    rounds: Vec<Round>,
}

impl Bracket {
    pub fn new(bracket_type: BracketType, series_type: SeriesType) -> Self {
        let num_teams_in_bracket = match bracket_type {
            BracketType::SingleElimination(num_teams_in_bracket)
            | BracketType::RoundRobin(num_teams_in_bracket) => num_teams_in_bracket,
        };

        let teams = (1u64..=num_teams_in_bracket)
            .into_iter()
            .map(Team::new)
            .collect::<Vec<_>>();

        Self {
            bracket_type,
            series_type,
            rounds: vec![Round::new(series_type, teams)],
        }
    }

    pub fn simulate(&self) {
        let mut bracket_result = BracketResult::new();

        for (round_number, round) in self.rounds.iter().enumerate() {
            let round_result = round.simulate();
            bracket_result
                .round_winners
                .push((round_number as u8, round_result.winners));
            bracket_result
                .round_scores
                .push((round_number as u8, round_result.scores));
        }

        dbg!(bracket_result);
    }
}

impl Simulate for Bracket {
    type SimulationResult = BracketResult;

    fn simulate(&self) -> Self::SimulationResult {
        todo!()
    }
}

type RoundWinners = (u8, Vec<Team>);
type RoundScore = (u8, Vec<([Team; 2], [u8; 2])>);

#[derive(Debug)]
struct BracketResult {
    round_winners: Vec<RoundWinners>,
    round_scores: Vec<RoundScore>,
}

impl BracketResult {
    fn new() -> Self {
        Self {
            round_winners: vec![],
            round_scores: vec![],
        }
    }
}

#[derive(Debug)]
pub enum BracketType {
    SingleElimination(u64),
    RoundRobin(u64),
}

// //! # Brackets
// //!
// //! Brackets simulates the progression of a generic tournament bracket.
// //!
// //! ## Basic concepts
// //!
// //! - A **bracket** is created using a specified positive number of players.
// //! - The bracket progresses players through a series of **rounds**, each of which is composed of **games**.
// //! - A game is a competitive simulation between a pair of **players**.
// //! - The winning player from each game is carried forward to the next round; the process repeats until a single player remains.
// //!
// //! ## Examples
// //! ```
// //! use brackets::*;
// //!
// //! let num_players = 32;
// //!
// //! match Bracket::new(num_players, BracketType::SingleElimination(RoundType::BestOfN(1))) {
// //!     Err(e) => {
// //!         eprintln!("{}", e)
// //!     }
// //!     Ok(mut bracket) => {
// //!         let results = bracket.simulate();
// //!         println!("Total players: {}", results.num_players);
// //!         println!("Total rounds: {}", results.num_rounds);
// //!         println!("Winner: {}", results.winner);
// //!     }
// //!  }
// //! ```

// use std::error::Error;
// use std::fmt::Display;

// /// A generic tournament product consisting of `num_players` number of
// /// players.
// #[derive(Debug)]
// pub struct Bracket {
//     /// The number of players that will play in the bracket. Must be a
//     /// positive power of 2, such as 2, 4, 8, 16, etc.
//     num_players: u8,
//     num_games_played: u32,
//     bracket_type: BracketType,
// }

// impl Bracket {
//     /// Returns either a bracket set up with `num_players` number of
//     /// players, or a `BracketError`.
//     ///
//     /// # Arguments
//     ///
//     /// * `num_players` - The number of players. Must be a positive
//     ///   power of 2, such as 2, 4, 8, 16, etc.
//     ///
//     /// # Examples
//     ///
//     /// ## Good
//     /// ```
//     /// use brackets::*;
//     /// let bracket = Bracket::new(8, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
//     /// ```
//     ///
//     /// ## Bad
//     /// ```should_panic
//     /// use brackets::*;
//     /// // Will panic because 9 is not a positive power of 2!
//     /// let bracket = Bracket::new(9, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
//     /// ```
//     pub fn new(num_players: u8, bracket_type: BracketType) -> Result<Self, BracketCreationError> {
//         if !Self::is_positive_power_of_two(num_players) {
//             return Err(BracketCreationError::InvalidNumPlayers(num_players));
//         }

//         match bracket_type {
//             BracketType::SingleElimination(round_type) => match round_type {
//                 RoundType::BestOfN(n) => {
//                     if n % 2 == 0 {
//                         return Err(BracketCreationError::InvalidBestOfN(num_players));
//                     }

//                     Ok(Self {
//                         num_players,
//                         num_games_played: 0,
//                         bracket_type,
//                     })
//                 }
//             },
//         }
//     }

//     fn is_positive_power_of_two(n: u8) -> bool {
//         n > 0 && n & (n - 1) == 0
//     }

//     fn rounds_required(&self) -> u8 {
//         (self.num_players as f32).log2().ceil() as u8
//     }

//     pub fn min_games_to_determine_winner(&self) -> u32 {
//         match &self.bracket_type {
//             BracketType::SingleElimination(round_type) => match round_type {
//                 RoundType::BestOfN(_) => {
//                     ((self.num_players - 1) * round_type.series_win_threshold()) as u32
//                 }
//             },
//         }
//     }

//     fn determine_winner(&mut self) -> Player {
//         let mut next_round_player_pool = (1u8..=self.num_players)
//             .map(|_| Player::new())
//             .collect::<Vec<_>>();

//         let BracketType::SingleElimination(round_type) = &self.bracket_type;

//         // Simulate each round one at a time.
//         for _ in 1..=self.rounds_required() {
//             let round = Round::new(next_round_player_pool, *round_type);
//             let sim_results = round.simulate();
//             next_round_player_pool = sim_results.0;
//             self.num_games_played += sim_results.1;
//         }

//         // After the final round, we're down to one last player: the winner.
//         next_round_player_pool
//             .pop()
//             .expect("Expected to find a bracket winner")
//     }

//     /// Simulated the bracket and returns the results in the form of a `BracketSimulationResult`.
//     ///
//     /// # Examples
//     ///
//     /// ```
//     /// use brackets::*;
//     /// let mut bracket = Bracket::new(8, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
//     /// let results = bracket.simulate();
//     /// println!("{:?}", results);
//     /// ```
//     pub fn simulate(&mut self) -> BracketSimulationResult {
//         let winner = self.determine_winner();

//         BracketSimulationResult {
//             num_players: self.num_players,
//             num_rounds: self.rounds_required(),
//             num_games: self.num_games_played,
//             winner: winner.name,
//         }
//     }
// }

// #[derive(Debug, Copy, Clone)]
// pub enum BracketType {
//     SingleElimination(RoundType),
// }

// /// Describes an error that occured during creation of the `Bracket`.
// #[derive(Debug, PartialEq)]
// pub enum BracketCreationError {
//     /// Returned when the number of players supplied to the bracket is invalid.
//     /// The number of players supplied to the bracket must always be a positive power of 2.
//     InvalidNumPlayers(u8),
//     /// Returned when the 'n' in a 'Best of n' series is an even number.
//     InvalidBestOfN(u8),
// }

// impl Display for BracketCreationError {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match *self {
//             BracketCreationError::InvalidNumPlayers(num_players) => {
//                 write!(
//                     f,
//                     "expected number of players in the bracket to be a positive power of 2, got {}",
//                     num_players
//                 )
//             }
//             BracketCreationError::InvalidBestOfN(n) => {
//                 write!(
//                     f,
//                     "A Best Of series must be played through an odd number of games, but got {} games instead",
//                     n
//                 )
//             }
//         }
//     }
// }

// impl Error for BracketCreationError {}

// /// The result of the simulation of the bracket, providing details on
// /// how the bracket progressed and which player won.
// #[derive(Debug)]
// pub struct BracketSimulationResult {
//     pub num_players: u8,
//     pub num_rounds: u8,
//     pub num_games: u32,
//     pub winner: String,
// }

// #[derive(Debug, Clone)]
// struct Round {
//     matchups: Vec<PlayerPair>,
//     round_type: RoundType,
// }

// #[derive(Debug, Copy, Clone)]
// pub enum RoundType {
//     BestOfN(u8),
// }

// impl RoundType {
//     fn series_win_threshold(&self) -> u8 {
//         match self {
//             Self::BestOfN(n) => (n / 2) + 1,
//         }
//     }
// }

// impl Round {
//     fn new(initial_player_pool: Vec<Player>, round_type: RoundType) -> Self {
//         Self {
//             matchups: initial_player_pool
//                 .chunks(PLAYERS_PER_MATCH)
//                 .map(|chunk| chunk.to_vec().try_into().unwrap())
//                 .collect::<Vec<PlayerPair>>(),
//             round_type,
//         }
//     }

//     fn simulate_series(&self, matchup: PlayerPair, num_games_in_series: u8) -> (Player, u32) {
//         let series_win_threshold = self.round_type.series_win_threshold();

//         let mut games_played: Vec<Game> = vec![];

//         let mut player_wins_in_series: [u8; 2] = [0, 0];

//         for _ in 1..=num_games_in_series {
//             if player_wins_in_series[0] == series_win_threshold
//                 || player_wins_in_series[1] == series_win_threshold
//             {
//                 break;
//             }

//             let game = Game::new(matchup.clone());

//             let winner = game.simulate();
//             if winner == matchup[0] {
//                 player_wins_in_series[0] += 1;
//             } else {
//                 player_wins_in_series[1] += 1;
//             }

//             games_played.push(game);
//         }

//         let series_winner_index = if player_wins_in_series[0] > player_wins_in_series[1] {
//             0
//         } else {
//             1
//         };
//         let series_winner = matchup[series_winner_index].clone();

//         (series_winner, games_played.len() as u32)
//     }

//     fn determine_winner(&self) -> (Vec<Player>, u32) {
//         let mut games_played_in_round: u32 = 0;
//         let mut winners_player_pool: Vec<Player> = vec![];

//         for matchup in &self.matchups {
//             match self.round_type {
//                 RoundType::BestOfN(n) => {
//                     let (winner, games_played_in_series) = self.simulate_series(matchup.clone(), n);
//                     games_played_in_round += games_played_in_series;
//                     winners_player_pool.push(winner);
//                 }
//             }
//         }

//         (winners_player_pool, games_played_in_round)
//     }

//     fn simulate(&self) -> (Vec<Player>, u32) {
//         self.determine_winner()
//     }
// }

// #[derive(Debug, Clone)]
// struct Game {
//     players: PlayerPair,
// }

// impl Game {
//     fn new(players: PlayerPair) -> Self {
//         Self { players }
//     }

//     fn rng_player_skill_boost() -> u8 {
//         if rand::random() {
//             5
//         } else {
//             0
//         }
//     }

//     fn rng_calc_player_power(player_skill: u8) -> u8 {
//         std::cmp::min(
//             player_skill + Self::rng_player_skill_boost(),
//             Player::max_player_skill(),
//         )
//     }

//     fn determine_winner(&self) -> Player {
//         let player_one = self.players[0].clone();
//         let player_two = self.players[1].clone();

//         let player_one_power = Self::rng_calc_player_power(player_one.skill);
//         let player_two_power = Self::rng_calc_player_power(player_two.skill);

//         if player_one_power > player_two_power {
//             return player_one;
//         }

//         player_two
//     }

//     fn simulate(&self) -> Player {
//         self.determine_winner()
//     }
// }

// #[derive(Debug, Clone, PartialEq)]
// struct Player {
//     name: String,
//     skill: u8,
// }

// impl Player {
//     fn new() -> Self {
//         let skill = rand::random::<u8>() % (Self::max_player_skill() + 1);

//         let names = vec![
//             "Alice", "Bob", "Charlie", "Dave", "Emily", "Filip", "George", "Helena",
//         ];
//         let index = rand::random::<u8>() as usize % names.len();
//         let name = names[index];
//         let name_suffix = rand::random::<u8>();

//         Self {
//             skill,
//             name: format!("{}-{}", name, name_suffix),
//         }
//     }

//     pub fn max_player_skill() -> u8 {
//         99
//     }
// }

// const PLAYERS_PER_MATCH: usize = 2;
// type PlayerPair = [Player; PLAYERS_PER_MATCH];

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_calculate_player_power() {
//         assert!(
//             Game::rng_calc_player_power(Player::max_player_skill()) <= Player::max_player_skill()
//         );
//         assert_eq!(
//             Game::rng_calc_player_power(Player::max_player_skill()),
//             Player::max_player_skill()
//         );
//     }

//     #[test]
//     fn test_bracket_creation() {
//         let num_players = 2;
//         let bracket = Bracket::new(
//             num_players,
//             BracketType::SingleElimination(RoundType::BestOfN(1)),
//         );
//         assert!(bracket.is_ok());

//         let num_players = 3;
//         let bracket = Bracket::new(
//             num_players,
//             BracketType::SingleElimination(RoundType::BestOfN(1)),
//         );
//         assert!(bracket.is_err());
//         if let Err(error) = bracket {
//             assert_eq!(error, BracketCreationError::InvalidNumPlayers(num_players))
//         };

//         let num_players = 2;
//         let n = 2;
//         let bracket = Bracket::new(
//             num_players,
//             BracketType::SingleElimination(RoundType::BestOfN(n)),
//         );
//         assert!(bracket.is_err());
//         if let Err(error) = bracket {
//             assert_eq!(error, BracketCreationError::InvalidBestOfN(n))
//         };
//     }

//     #[test]
//     fn test_is_positive_power_of_two() {
//         assert!(Bracket::is_positive_power_of_two(1));
//         assert!(Bracket::is_positive_power_of_two(2));
//         assert!(Bracket::is_positive_power_of_two(4));
//         assert!(Bracket::is_positive_power_of_two(8));
//         assert!(Bracket::is_positive_power_of_two(16));
//         assert!(Bracket::is_positive_power_of_two(32));
//         assert!(Bracket::is_positive_power_of_two(64));
//         assert!(Bracket::is_positive_power_of_two(128));

//         assert!(!Bracket::is_positive_power_of_two(0));
//         assert!(!Bracket::is_positive_power_of_two(3));
//         assert!(!Bracket::is_positive_power_of_two(69));
//     }

//     #[test]
//     fn test_rounds_required() {
//         let bracket =
//             Bracket::new(1, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
//         assert_eq!(bracket.rounds_required(), 0);

//         let bracket =
//             Bracket::new(2, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
//         assert_eq!(bracket.rounds_required(), 1);

//         let bracket =
//             Bracket::new(4, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
//         assert_eq!(bracket.rounds_required(), 2);

//         let bracket =
//             Bracket::new(8, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
//         assert_eq!(bracket.rounds_required(), 3);

//         let bracket =
//             Bracket::new(16, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
//         assert_eq!(bracket.rounds_required(), 4);
//     }

//     #[test]
//     fn test_min_games_required() {
//         let bracket =
//             Bracket::new(32, BracketType::SingleElimination(RoundType::BestOfN(1))).unwrap();
//         assert_eq!(bracket.min_games_to_determine_winner(), 31);

//         let bracket =
//             Bracket::new(32, BracketType::SingleElimination(RoundType::BestOfN(3))).unwrap();
//         assert_eq!(bracket.min_games_to_determine_winner(), 62);

//         let bracket =
//             Bracket::new(32, BracketType::SingleElimination(RoundType::BestOfN(5))).unwrap();
//         assert_eq!(bracket.min_games_to_determine_winner(), 93);
//     }
// }
