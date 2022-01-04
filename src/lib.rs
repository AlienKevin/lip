//! # Lip Parsing Library
//!
//! Lip provides powerful parser combinators for you to
//! create reusable and flexible parsers.

#[macro_use]
mod tests;

use itertools::Itertools;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt::{Debug, Display};
use unicode_segmentation::UnicodeSegmentation as Uni;
use unicode_width::{UnicodeWidthChar, UnicodeWidthStr};

/// Add location information to any type.
///
/// Used by [located](fn.located.html) to add `from` and `to` locations to any captured values
/// for more precise error messages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Located<A> {
    pub value: A,
    pub from: Location,
    pub to: Location,
}

/// Records the location of a character within the source string.
///
/// Uses `row` and `col`. The first character of the source is
/// at row 1 and column 1. Column width aligns mostly with
/// displayed width of unicode characters and strings
/// according to the UAX#11 rules, with exceptions
/// made for compound emojis like 👩‍🔬. For example, most CJK characters
/// like 我 and 혇 occupies two column widths. And most emojis occupies
/// two column widths as well.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    pub row: usize,
    pub col: usize,
}

impl Ord for Location {
    fn cmp(&self, other: &Self) -> Ordering {
        self.row
            .cmp(&other.row)
            .then_with(|| self.col.cmp(&other.col))
    }
}

impl PartialOrd for Location {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Records the result of the parser.
///
/// Similar to the [`std::result::Result`](https://doc.rust-lang.org/std/result/enum.Result.html) type, outputs `ParseResult::Ok` if parsing succeeds
/// and `ParseResult::Err` if parsing fails.
///
/// `ParseResult::Ok` contains:
/// * input: the part of source string left after parsing finished
/// * location: the [Location](struct.Location.html) of the end of parse,
/// * output: the output of the parsing
/// * state: the final state of the parser
/// * committed: If committed is true, then the parser has succeeded and
/// has committed to this parse. If a parser after this fails,
/// other parser alternatives will not be attempted
///
/// `ParseResult::Err` contains:
/// * message: the message explaining what and why the parse failed
/// * from: the starting [Location](struct.Location.html) of the error
/// * to: the ending [Location](struct.Location.html) of the error
/// * state: the final state of the parser
///
/// A word about `state`:
/// Sometimes you want to keep track of extra information outside the current location
/// and the rest of the source string. For example, you may want to put
/// different symbols encountered into a symbol table as a replacement mapping
/// after parsing finished or keep track of the current instruction index.
/// This library uses `state` to capture any kind of extra information like the ones
/// we mentioned above during parsing. The only requirement on `state` is implementation
/// of the `Clone` trait. Here's an example `state`:
/// ```
/// # use std::collections::HashMap;
/// #[derive(Clone, Debug)]
/// pub struct State {
///   symbol_table: HashMap<String, usize>, // build up a symbol table
///   instruction_index: usize, // count which instruction we are at
///   variable_index: usize, // count how many variables we encountered
/// }
/// ```
/// To update `state` during and after parsing, use `update_state`.
#[derive(Debug, PartialEq, Eq)]
pub enum ParseResult<'a, Output, State> {
    Ok {
        input: &'a str,
        location: Location,
        output: Output,
        state: State,
        committed: bool,
    },
    Err {
        message: String,
        from: Location,
        to: Location,
        state: State,
        committed: bool,
    },
}

pub struct ParseOk<'a, Output, State> {
    input: &'a str,
    output: Output,
    location: Location,
    state: State,
    committed: bool,
}

pub struct ParseErr<State> {
    message: String,
    from: Location,
    to: Location,
    state: State,
    committed: bool,
}

pub type StdParseResult<'a, A, S> = Result<ParseOk<'a, A, S>, ParseErr<S>>;

impl<'a, A, S> Into<StdParseResult<'a, A, S>> for ParseResult<'a, A, S> {
    fn into(self) -> StdParseResult<'a, A, S> {
        match self {
            ParseResult::Ok {
                input,
                location,
                output,
                state,
                committed,
            } => Ok(ParseOk {
                input,
                location,
                output,
                state,
                committed,
            }),
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => Err(ParseErr {
                message,
                from,
                to,
                state,
                committed,
            }),
        }
    }
}

impl<'a, A, S> From<StdParseResult<'a, A, S>> for ParseResult<'a, A, S> {
    fn from(result: StdParseResult<'a, A, S>) -> ParseResult<'a, A, S> {
        match result {
            Ok(ParseOk {
                input,
                location,
                output,
                state,
                committed,
            }) => ParseResult::Ok {
                input,
                location,
                output,
                state,
                committed,
            },
            Err(ParseErr {
                message,
                from,
                to,
                state,
                committed,
            }) => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            },
        }
    }
}

impl<'a, T, S: Clone> ParseResult<'a, T, S> {
    /// Map the parse output to a new value if parse succeeds.
    /// Otherwise, return error as usual.
    pub fn map<U, F: FnOnce(T) -> U>(self, func: F) -> ParseResult<'a, U, S> {
        match self {
            ParseResult::Ok {
                input,
                location,
                output,
                state,
                committed,
            } => ParseResult::Ok {
                input,
                location,
                output: func(output),
                state,
                committed,
            },
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            },
        }
    }
    /// Map the parse output to a new value if parse succeeds.
    /// The map function is supplied both the output and the
    /// state of the parser.
    /// Otherwise, return error as usual.
    pub fn map_with_state<U, F: FnOnce(T, S) -> U>(self, func: F) -> ParseResult<'a, U, S> {
        match self {
            ParseResult::Ok {
                input,
                location,
                output,
                state,
                committed,
            } => ParseResult::Ok {
                input,
                location,
                output: func(output, state.clone()),
                state,
                committed,
            },
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            },
        }
    }
    /// Map the error message to a new message if parse fails.
    /// Otherwise, return output as usual.
    pub fn map_err<F: FnOnce(String) -> String>(self, func: F) -> ParseResult<'a, T, S> {
        match self {
            ParseResult::Ok {
                input,
                location,
                output,
                state,
                committed,
            } => ParseResult::Ok {
                input,
                location,
                output,
                state,
                committed,
            },
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => ParseResult::Err {
                message: func(message),
                from,
                to,
                state,
                committed,
            },
        }
    }
    /// Returns a new parser which is given the current output if parse succeeds.
    /// Otherwise, return error as usual.
    pub fn and_then<U, F: FnOnce(&'a str, T, Location, S) -> ParseResult<'a, U, S>>(
        self,
        func: F,
    ) -> ParseResult<'a, U, S> {
        match self {
            ParseResult::Ok {
                input,
                output,
                location,
                state,
                committed,
            } => match func(input, output, location, state) {
                ParseResult::Ok {
                    input,
                    output,
                    location,
                    state,
                    committed: cur_committed,
                } => ParseResult::Ok {
                    input,
                    output,
                    location,
                    state,
                    committed: committed || cur_committed,
                },
                ParseResult::Err {
                    message,
                    from,
                    to,
                    state,
                    committed: cur_committed,
                } => ParseResult::Err {
                    message,
                    from,
                    to,
                    state,
                    committed: committed || cur_committed,
                },
            },
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            },
        }
    }

    pub fn backtrackable(self) -> ParseResult<'a, T, S> {
        match self {
            ParseResult::Ok {
                input,
                location,
                output,
                state,
                ..
            } => ParseResult::Ok {
                input,
                location,
                output,
                state,
                committed: false,
            },
            ParseResult::Err {
                message,
                from,
                to,
                state,
                ..
            } => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed: false,
            },
        }
    }

    fn unwrap(self, source: &'a str) -> T {
        match self {
            ParseResult::Ok { output, .. } => output,
            ParseResult::Err {
                message, from, to, ..
            } => {
                println!("{}", display_error(source, message, from, to));
                panic!();
            }
        }
    }
    fn unwrap_err(self) -> String
    where
        T: Debug + 'a,
    {
        match self {
            ParseResult::Ok { output, .. } => panic!("{:#?}", output),
            ParseResult::Err { message, .. } => message,
        }
    }
}

pub struct Map<P, F>(P, F);

impl<'a, A, B, P, F> Parser<'a> for Map<P, F>
where
    P: Parser<'a, Output = A>,
    F: Fn(A) -> B,
{
    type Output = B;

    type State = P::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, B, Self::State> {
        self.0.parse(input, location, state).map(&self.1)
    }
}

pub struct MapWithState<P, F>(P, F);

impl<'a, A, B, P, F> Parser<'a> for MapWithState<P, F>
where
    P: Parser<'a, Output = A>,
    F: Fn(A, P::State) -> B,
{
    type Output = B;

    type State = P::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, B, Self::State> {
        match self.0.parse(input, location, state) {
            ParseResult::Ok {
                input,
                output,
                location,
                state,
                committed,
            } => ParseResult::Ok {
                input,
                output: self.1(output, state.clone()),
                location,
                state,
                committed,
            },
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            },
        }
    }
}

pub struct MapErr<P, F>(P, F);

impl<'a, P, F> Parser<'a> for MapErr<P, F>
where
    P: Parser<'a>,
    F: Fn(String) -> String,
{
    type Output = P::Output;

    type State = P::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        self.0.parse(input, location, state).map_err(&self.1)
    }
}

pub struct AndThen<P1, F>(P1, F);

impl<'a, P1, P2, F, S: Clone> Parser<'a> for AndThen<P1, F>
where
    P1: Parser<'a, State = S>,
    P2: Parser<'a, State = S>,
    F: Fn(P1::Output) -> P2,
{
    type Output = P2::Output;

    type State = S;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        self.0.parse(input, location, state).and_then(
            |cur_input, cur_output, cur_location, cur_state| {
                self.1(cur_output).parse(cur_input, cur_location, cur_state)
            },
        )
    }
}

pub struct Pred<'a, P, F>(P, F, &'a str);

impl<'a, P, F> Parser<'a> for Pred<'a, P, F>
where
    P: Parser<'a>,
    F: Fn(&P::Output) -> bool,
{
    type Output = P::Output;

    type State = P::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        match self.0.parse(input, location, state) {
            ParseResult::Ok {
                input: cur_input,
                output: content,
                location: cur_location,
                state: cur_state,
                committed: cur_committed,
            } => {
                if self.1(&content) {
                    ParseResult::Ok {
                        input: cur_input,
                        output: content,
                        location: cur_location,
                        state: cur_state,
                        committed: true,
                    }
                } else {
                    ParseResult::Err {
                        message: format!("I'm expecting {}", self.2),
                        from: location,
                        to: cur_location,
                        state: cur_state,
                        committed: cur_committed,
                    }
                }
            }
            ParseResult::Err {
                message,
                from,
                to,
                state,
                ..
            } => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed: false,
            },
        }
    }
}

pub struct End<P>(P);

impl<'a, P> Parser<'a> for End<P>
where
    P: Parser<'a>,
{
    type Output = P::Output;

    type State = P::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        match self.0.parse(input, location, state) {
            ParseResult::Ok {
                input,
                location,
                state,
                output,
                ..
            } => {
                if !input.is_empty() {
                    ParseResult::Err {
                        message: "I'm expecting the end of input.".to_string(),
                        from: location,
                        to: location,
                        state,
                        committed: false,
                    }
                } else {
                    ParseResult::Ok {
                        input,
                        output,
                        location,
                        state,
                        committed: false,
                    }
                }
            }
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            },
        }
    }
}

pub struct UpdateState<P, F>(P, F);

impl<'a, P, F> Parser<'a> for UpdateState<P, F>
where
    P: Parser<'a>,
    F: Fn(&P::Output, P::State) -> P::State,
{
    type Output = P::Output;

    type State = P::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        match self.0.parse(input, location, state) {
            ParseResult::Ok {
                input: cur_input,
                location: cur_location,
                state: cur_state,
                output,
                committed,
            } => {
                let new_state = self.1(&output, cur_state);
                ParseResult::Ok {
                    input: cur_input,
                    output,
                    location: cur_location,
                    state: new_state,
                    committed,
                }
            }
            err @ ParseResult::Err { .. } => err,
        }
    }
}

pub struct Update<P, F>(P, F);

impl<'a, P, A, F> Parser<'a> for Update<P, F>
where
    P: Parser<'a, Output = A>,
    F: Fn(&'a str, A, Location, P::State) -> ParseResult<'a, A, P::State>,
{
    type Output = P::Output;

    type State = P::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        match self.0.parse(input, location, state) {
            ParseResult::Ok {
                input: cur_input,
                location: cur_location,
                state: cur_state,
                output,
                ..
            } => self.1(cur_input, output, cur_location, cur_state),
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            },
        }
    }
}

pub struct Ignore<P>(P);

impl<'a, P> Parser<'a> for Ignore<P>
where
    P: Parser<'a>,
{
    type Output = ();

    type State = P::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        map(self, |_| ()).parse(input, location, state)
    }
}

pub struct Keep<P1, P2>(P1, P2);

impl<'a, P1, P2, A, B, F, S: Clone> Parser<'a> for Keep<P1, P2>
where
    F: FnOnce(A) -> B,
    P1: Parser<'a, Output = F, State = S>,
    P2: Parser<'a, Output = A, State = S>,
{
    type Output = B;

    type State = P1::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        self.0
            .parse(input, location, state)
            .and_then(|cur_input, func, cur_location, cur_state| {
                self.1
                    .parse(cur_input, cur_location, cur_state)
                    .map(|arg| func(arg))
            })
    }
}

pub struct Skip<P1, P2>(P1, P2);

impl<'a, P1, P2, S: Clone> Parser<'a> for Skip<P1, P2>
where
    P1: Parser<'a, State = S>,
    P2: Parser<'a, State = S>,
{
    type Output = P1::Output;

    type State = P1::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        self.0.parse(input, location, state).and_then(
            |cur_input, left_output, cur_location, cur_state| {
                self.1
                    .parse(cur_input, cur_location, cur_state)
                    .map(|_| left_output)
            },
        )
    }
}

pub struct Backtrackable<P>(P);

impl<'a, P> Parser<'a> for Backtrackable<P>
where
    P: Parser<'a>,
{
    type Output = P::Output;

    type State = P::State;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        self.0.parse(input, location, state).backtrackable()
    }
}

pub trait Parser<'a> {
    type Output;

    type State: Clone;

    /// Parse a given input, starting at
    /// a given location and state.
    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State>;
    /// Run the parser on a given input, starting at
    /// the first character.
    ///
    /// Exammple:
    ///
    /// Parse a (x, y) position pair.
    /// ```
    /// # use lip::*;
    /// // Parse an (x, y) position pair
    /// let position = succeed!(|x, y| (x, y))
    ///   .keep(int())
    ///   .skip(token(","))
    ///   .keep(int())
    ///   .run("2, 3", ()); // position == (2, 3)
    /// ```
    fn run(
        &self,
        input: &'a str,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        self.parse(input, Location { row: 1, col: 1 }, state)
    }
    /// Map the output to a new output if parse succeeds.
    /// Otherwise, return error as usual.
    ///
    /// The only difference from the `map` on `ParseResult`
    /// is that this `map` turns one `Parser` into another while the `map`
    /// on `ParseResult` turns one `ParseResult` into another.
    fn map<F, NewOutput>(self, map_fn: F) -> Map<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Output) -> NewOutput,
    {
        map(self, map_fn)
    }
    /// The map function is supplied both the output and the
    /// state of the parser.
    /// Otherwise, return error as usual.
    ///
    /// The only difference from the `map_with_state` on `ParseResult`
    /// is that this `map_with_state` turns one `Parser` into another while the `map_with_state`
    /// on `ParseResult` turns one `ParseResult` into another.
    fn map_with_state<F, NewOutput>(self, map_fn: F) -> MapWithState<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Output, Self::State) -> NewOutput,
    {
        map_with_state(self, map_fn)
    }
    /// Map the error message to a new message if parse fails.
    /// Otherwise, return output as usual.
    ///
    /// The only difference from the `map_err` on `ParseResult`
    /// is that this `map_err` turns one `Parser` into another while the `map_err`
    /// on `ParseResult` turns one `ParseResult` into another.
    fn map_err<F>(self, map_fn: F) -> MapErr<Self, F>
    where
        Self: Sized,
        F: Fn(String) -> String,
    {
        map_err(self, map_fn)
    }
    /// Returns a new parser which is given the current output if parse succeeds.
    /// Otherwise, return error as usual.
    ///
    /// The only difference from the `and_then` on `ParseResult`
    /// is that this `and_then` turns one `Parser` into another while the `and_then`
    /// on `ParseResult` turns one `ParseResult` into another.
    fn and_then<F, P2, B>(self, f: F) -> AndThen<Self, F>
    where
        Self: Sized,
        P2: Parser<'a, Output = B>,
        F: Fn(Self::Output) -> P2,
    {
        and_then(self, f)
    }
    /// Judge if the output meets the requirement using a predicate function
    /// if the parse succeeds. Otherwise, return error as usual.
    fn pred<F>(self, predicate: F, expecting: &'a str) -> Pred<Self, F>
    where
        Self: Sized,
        F: Fn(&Self::Output) -> bool,
    {
        pred(self, predicate, expecting)
    }
    /// Ignore the parse output and return `()` (emtpy tuple)
    fn ignore(self) -> Ignore<Self>
    where
        Self: Sized,
    {
        Ignore(self)
    }
    /// Update the state given the new output and state of the parse if parse succeeds.
    /// Otherwise, return error as usual.
    fn update_state<F>(self, f: F) -> UpdateState<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Output, Self::State) -> Self::State,
    {
        update_state(self, f)
    }
    /// Update the result of the parser if parse succeeds.
    /// Otherwise, return error as usual.
    ///
    /// This is the most general and powerful method of the parser.
    /// Think about using simpler methods like `map` and `map_err` before
    /// choosing `update`.
    fn update<F, B>(self, f: F) -> Update<Self, F>
    where
        Self: Sized,
        F: Fn(&'a str, Self::Output, Location, Self::State) -> ParseResult<'a, B, Self::State>,
    {
        update(self, f)
    }
    /// Check if you have reached the end of the input you are parsing.
    ///
    /// If you want to parse an input containing only "abc":
    /// ```
    /// # use lip::*;
    /// assert_succeed(
    ///  token("abc").end(),
    ///  "abc", "abc",
    /// );
    /// assert_fail(
    ///   token("abc").end(),
    ///   "abcd", "I'm expecting the end of input.",
    /// );
    /// ```
    fn end(self) -> End<Self>
    where
        Self: Sized,
    {
        end(self)
    }
    /// Keep values in a parser pipeline.
    ///
    /// Exammple:
    ///
    /// Parse a (x, y) position pair.
    /// ```
    /// # use lip::*;
    /// // Parse an (x, y) position pair
    /// let position = succeed!(|x, y| (x, y))
    ///   .keep(int())
    ///   .skip(token(","))
    ///   .keep(int())
    ///   .run("2, 3", ()); // position == (2, 3)
    /// ```
    fn keep<A, B, P2>(self, arg_parser: P2) -> Keep<Self, P2>
    where
        Self: Sized,
        Self::Output: FnOnce(A) -> B,
        P2: Parser<'a, Output = A>,
    {
        keep(self, arg_parser)
    }
    /// Skip values in a parser pipeline.
    ///
    /// Exammple:
    ///
    /// Parse a (x, y) position pair.
    /// ```
    /// # use lip::*;
    /// // Parse an (x, y) position pair
    /// let position = succeed!(|x, y| (x, y))
    ///   .keep(int())
    ///   .skip(token(","))
    ///   .keep(int())
    ///   .run("2, 3", ()); // position == (2, 3)
    /// ```
    fn skip<P2>(self, ignored_parser: P2) -> Skip<Self, P2>
    where
        Self: Sized,
        P2: Parser<'a>,
    {
        Skip(self, ignored_parser)
    }

    fn backtrackable(self) -> Backtrackable<Self>
    where
        Self: Sized,
    {
        backtrackable(self)
    }

    fn first_of_two<T2>(self) -> OneOfTwo<Self, T2>
    where
        Self: Sized,
        T2: Parser<'a, Output = Self::Output, State = Self::State>,
    {
        OneOfTwo::First(self)
    }

    fn second_of_two<T1>(self) -> OneOfTwo<T1, Self>
    where
        Self: Sized,
        T1: Parser<'a, Output = Self::Output, State = Self::State>,
    {
        OneOfTwo::Second(self)
    }

    fn first_of_three<T2, T3>(self) -> OneOfThree<Self, T2, T3>
    where
        Self: Sized,
        T2: Parser<'a, Output = Self::Output, State = Self::State>,
        T3: Parser<'a, Output = Self::Output, State = Self::State>,
    {
        OneOfThree::First(self)
    }

    fn second_of_three<T1, T3>(self) -> OneOfThree<T1, Self, T3>
    where
        Self: Sized,
        T1: Parser<'a, Output = Self::Output, State = Self::State>,
        T3: Parser<'a, Output = Self::Output, State = Self::State>,
    {
        OneOfThree::Second(self)
    }

    fn third_of_three<T1, T2>(self) -> OneOfThree<T1, T2, Self>
    where
        Self: Sized,
        T1: Parser<'a, Output = Self::Output, State = Self::State>,
        T2: Parser<'a, Output = Self::Output, State = Self::State>,
    {
        OneOfThree::Third(self)
    }
}

fn and_then<'a, P1, P2, F>(parser: P1, f: F) -> AndThen<P1, F>
where
    P1: Parser<'a>,
    P2: Parser<'a>,
    F: Fn(P1::Output) -> P2,
{
    AndThen(parser, f)
}

use std::marker::PhantomData;

#[derive(Copy, Clone)]
pub struct FnParser<F, A, S>(F, PhantomData<A>, PhantomData<S>);

pub fn fn_parser<'a, A, S: Clone, F>(f: F) -> FnParser<F, A, S>
where
    F: Fn(&'a str, Location, S) -> ParseResult<'a, A, S>,
{
    FnParser(f, PhantomData, PhantomData)
}

impl<'a, A, S: Clone, F> Parser<'a> for FnParser<F, A, S>
where
    F: Fn(&'a str, Location, S) -> ParseResult<'a, A, S>,
{
    type Output = A;
    type State = S;

    fn parse(&self, input: &'a str, location: Location, state: S) -> ParseResult<'a, A, S> {
        (self.0)(input, location, state)
    }
}

/// Parse a given token string.
///
/// ⚠️ Newlines are not allowed in tokens.
pub fn token<'a, S: Clone>(expected: &'a str) -> impl Parser<'a, Output = &'a str, State = S> {
    fn_parser(move |input: &'a str, location: Location, state: S| {
        let peek = input.get(0..expected.len());
        if peek == Some(expected) {
            ParseResult::Ok {
                input: &input[expected.len()..],
                output: expected,
                location: increment_col(unicode_column_width(expected), location),
                state,
                committed: true,
            }
        } else {
            let expected_len = expected.graphemes(true).count();
            let peek_str = &input.graphemes(true).take(expected_len).join("");
            ParseResult::Err {
                message: format!(
                    "I'm expecting a `{}` but found {}.",
                    expected,
                    display_token(peek_str)
                ),
                from: location,
                to: Location {
                    col: location.col + unicode_column_width(peek_str),
                    ..location
                },
                state,
                committed: false,
            }
        }
    })
}

fn increment_col(additional_col: usize, location: Location) -> Location {
    Location {
        col: location.col + additional_col,
        ..location
    }
}

fn increment_row(additional_row: usize, location: Location) -> Location {
    Location {
        row: location.row + additional_row,
        col: 1,
    }
}

fn display_token<T: Display>(token: T) -> String {
    let token_str = &token.to_string();
    if unicode_column_width(token_str) == 0 {
        "nothing".to_string()
    } else {
        format!("`{}`", token_str.replace("\n", "\\n"))
    }
}

impl<'a, A, S: Clone, T: Parser<'a, Output = A, State = S>> Parser<'a> for &T {
    type Output = A;
    type State = S;

    fn parse(&self, input: &'a str, location: Location, state: S) -> ParseResult<'a, A, S> {
        (*self).parse(input, location, state)
    }
}

/// Pair up two parsers. Run the left parser, then the right,
/// and last combine both outputs into a tuple.
fn pair<'a, P1, P2, R1, R2, S: Clone>(
    parser1: P1,
    parser2: P2,
) -> impl Parser<'a, Output = (R1, R2), State = S>
where
    P1: Parser<'a, Output = R1, State = S>,
    P2: Parser<'a, Output = R2, State = S>,
{
    fn_parser(move |input, location, state| {
        parser1.parse(input, location, state).and_then(
            |cur_input, first_output, cur_location, cur_state| {
                parser2
                    .parse(cur_input, cur_location, cur_state)
                    .map(|second_output| (first_output, second_output))
            },
        )
    })
}

fn map<'a, P, F, B>(parser: P, map_fn: F) -> Map<P, F>
where
    P: Parser<'a>,
    F: Fn(P::Output) -> B,
{
    Map(parser, map_fn)
}

fn map_with_state<'a, P, F, A, B>(parser: P, map_fn: F) -> MapWithState<P, F>
where
    P: Parser<'a, Output = A>,
    F: Fn(P::Output, P::State) -> B,
{
    MapWithState(parser, map_fn)
}

fn map_err<'a, P, F>(parser: P, map_fn: F) -> MapErr<P, F>
where
    P: Parser<'a>,
    F: Fn(String) -> String,
{
    MapErr(parser, map_fn)
}

fn backtrackable<'a, P>(parser: P) -> Backtrackable<P>
where
    P: Parser<'a>,
{
    Backtrackable(parser)
}

/// Run the left parser, then the right, last keep the left result and discard the right.
fn left<'a, P1, P2, R1, R2, S: Clone>(
    parser1: P1,
    parser2: P2,
) -> impl Parser<'a, Output = R1, State = S>
where
    P1: Parser<'a, Output = R1, State = S>,
    P2: Parser<'a, Output = R2, State = S>,
{
    map(pair(parser1, parser2), |(left, _right)| left)
}

fn keep<'a, P1, P2, F, A, B>(parser1: P1, parser2: P2) -> Keep<P1, P2>
where
    F: FnOnce(A) -> B,
    P1: Parser<'a, Output = F>,
    P2: Parser<'a, Output = A>,
{
    Keep(parser1, parser2)
}

#[doc(hidden)]
pub fn succeed_helper<'a, A: Clone, S: Clone>(output: A) -> impl Parser<'a, Output = A, State = S> {
    fn_parser(move |input, location, state: S| ParseResult::Ok {
        input,
        location,
        state,
        output: output.clone(),
        committed: false,
    })
}

/// A parser that succeeds without chomping any characters.
///
/// Seems weird on its own, but it is very useful in combination with other functions.
/// The docs for [keep](trait.Parser.html#method.keep) and [and_then](trait.Parser.html#method.and_then) have some neat examples.
#[macro_export]
macro_rules! succeed {
  (|$first_arg:ident $(, $arg:ident )*| $function_body:expr) => {
    succeed_helper(move |$first_arg| $(move |$arg|)* {
      $function_body
    })
  };
  (|$first_arg:ident:$first_arg_type:ty $(, $arg:ident:$arg_type:ty )*| $function_body:expr) => {
    succeed_helper(move |$first_arg:$first_arg_type| $(move |$arg:$arg_type|)* {
      $function_body
    })
  };
  ($value:expr) => {
    succeed_helper($value)
  };
}

fn end<'a, P>(parser: P) -> End<P>
where
    P: Parser<'a>,
{
    End(parser)
}

/// Indicate that a parser has reached a dead end.
///
/// "Everything was going fine until I ran into this problem."
pub fn problem<'a, F1, F2, A, S: Clone>(
    message: String,
    from: F1,
    to: F2,
) -> impl Parser<'a, Output = A>
where
    F1: Fn(Location) -> Location,
    F2: Fn(Location) -> Location,
{
    fn_parser(move |_input, location, state: S| ParseResult::Err {
        message: message.clone(),
        from: from(location),
        to: to(location),
        state,
        committed: false,
    })
}

/// Run the left parser, then the right, last keep the right result and discard the left.
fn right<'a, P1, P2, R1, R2, S: Clone>(
    parser1: P1,
    parser2: P2,
) -> impl Parser<'a, Output = R2, State = S>
where
    P1: Parser<'a, Output = R1, State = S>,
    P2: Parser<'a, Output = R2, State = S>,
{
    map(pair(parser1, parser2), |(_left, right)| right)
}

/// Run the parser one or more times and combine each output into a vector of outputs.
pub fn one_or_more<'a, P, A, S: Clone>(parser: P) -> impl Parser<'a, Output = Vec<A>, State = S>
where
    P: Parser<'a, Output = A, State = S>,
{
    fn_parser(move |mut input, mut location, mut state| {
        let mut output = Vec::new();
        let mut committed = false;

        match parser.parse(input, location, state) {
            ParseResult::Ok {
                input: cur_input,
                output: first_item,
                location: cur_location,
                state: cur_state,
                committed: cur_committed,
            } => {
                input = cur_input;
                location = cur_location;
                state = cur_state;
                committed |= cur_committed;
                output.push(first_item);
            }
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => {
                return ParseResult::Err {
                    message,
                    from,
                    to,
                    state,
                    committed,
                };
            }
        }

        loop {
            match parser.parse(input, location, state.clone()) {
                ParseResult::Ok {
                    input: cur_input,
                    output: cur_item,
                    location: cur_location,
                    state: cur_state,
                    committed: cur_committed,
                    ..
                } => {
                    input = cur_input;
                    location = cur_location;
                    state = cur_state;
                    committed |= cur_committed;
                    output.push(cur_item);
                }
                ParseResult::Err {
                    message,
                    from,
                    to,
                    state,
                    committed,
                } => {
                    if committed {
                        return ParseResult::Err {
                            message,
                            from,
                            to,
                            state,
                            committed,
                        };
                    } else {
                        break;
                    }
                }
            }
        }

        ParseResult::Ok {
            input,
            output,
            location,
            state,
            committed,
        }
    })
}

/// Run the parser zero or more times until an end delimiter (or end of input) and combine each output into a vector of outputs.
pub fn zero_or_more_until<'a, P, A, E, B, S: Clone>(
    item_name: &'static str,
    parser: P,
    end_name: &'static str,
    end_parser: E,
) -> impl Parser<'a, Output = Vec<A>, State = S>
where
    P: Parser<'a, Output = A, State = S>,
    E: Parser<'a, Output = B, State = ()>,
{
    fn_parser(move |mut input, mut location, mut state| {
        let mut output = Vec::new();
        let mut committed = false;

        // end_parser must run first
        // because the language of parser may be a superset of end_parser
        match end_parser.parse(input, location, ()) {
            ParseResult::Ok {
                committed: cur_committed,
                ..
            } => {
                committed |= cur_committed;
                return ParseResult::Ok {
                    input,
                    output,
                    location,
                    state,
                    committed,
                };
            }
            ParseResult::Err {
                message,
                from,
                to,
                committed,
                ..
            } => {
                if committed {
                    return ParseResult::Err {
                        message,
                        from,
                        to,
                        state,
                        committed,
                    };
                }
            } // no big deal, continue parsing
        }

        match parser.parse(input, location, state) {
            ParseResult::Ok {
                input: cur_input,
                output: first_item,
                location: cur_location,
                state: cur_state,
                committed: cur_committed,
            } => {
                input = cur_input;
                location = cur_location;
                state = cur_state;
                committed |= cur_committed;
                output.push(first_item);
            }
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed: cur_committed,
            } => {
                committed |= cur_committed;
                // end_parser must have failed as well
                // because we only run parser if end_parser fails at first
                if input.is_empty() {
                    // reached the end of input
                    return ParseResult::Ok {
                        input,
                        output,
                        location,
                        state,
                        committed,
                    };
                } else {
                    return ParseResult::Err {
                        message,
                        from,
                        to,
                        state,
                        committed,
                    };
                }
            }
        }

        loop {
            match end_parser.parse(input, location, ()) {
                ParseResult::Ok {
                    committed: cur_committed,
                    ..
                } => {
                    committed |= cur_committed;
                    return ParseResult::Ok {
                        input,
                        output,
                        location,
                        state,
                        committed,
                    };
                }
                ParseResult::Err {
                    message,
                    from,
                    to,
                    committed: err_committed,
                    ..
                } => {
                    if err_committed {
                        return ParseResult::Err {
                            message,
                            from,
                            to,
                            state,
                            committed: err_committed,
                        };
                    }
                    match parser.parse(input, location, state.clone()) {
                        ParseResult::Ok {
                            input: cur_input,
                            output: cur_item,
                            location: cur_location,
                            state: cur_state,
                            committed: cur_committed,
                        } => {
                            input = cur_input;
                            location = cur_location;
                            state = cur_state;
                            committed |= cur_committed;
                            output.push(cur_item);
                        }
                        ParseResult::Err {
                            from: end_from,
                            to: end_to,
                            committed: cur_committed,
                            ..
                        } => {
                            committed |= cur_committed;
                            if input.is_empty() {
                                // reached the end of input
                                return ParseResult::Ok {
                                    input,
                                    output,
                                    location,
                                    state,
                                    committed,
                                };
                            } else {
                                return ParseResult::Err {
                                    message: format!("I'm expecting either {} or {}. However, neither was found.", item_name, end_name),
                                    from: end_from,
                                    to: end_to,
                                    state,
                                    committed,
                                };
                            }
                        }
                    }
                }
            }
        }
    })
}

/// Run the parser one or more times until an end delimiter (or end of input) and combine each output into a vector of outputs.
pub fn one_or_more_until<'a, P, A, E, B, S: Clone>(
    item_name: &'static str,
    parser: P,
    end_name: &'static str,
    end_parser: E,
) -> impl Parser<'a, Output = Vec<A>, State = S>
where
    P: Parser<'a, Output = A, State = S>,
    E: Parser<'a, Output = B, State = ()>,
{
    fn_parser(move |mut input, mut location, mut state| {
        let mut output = Vec::new();
        let mut committed = false;

        match end_parser.parse(input, location, ()) {
            ParseResult::Ok {
                location: end_location,
                committed: cur_committed,
                ..
            } => {
                committed |= cur_committed;
                return ParseResult::Err {
                    message: format!(
                        "I'm expecting at least one occurrence of {} but reached {}.",
                        item_name, end_name
                    ),
                    from: location,
                    to: end_location,
                    state,
                    committed,
                };
            }
            ParseResult::Err {
                message,
                from,
                to,
                committed: err_committed,
                ..
            } => {
                if err_committed {
                    return ParseResult::Err {
                        message,
                        from,
                        to,
                        state,
                        committed: err_committed,
                    };
                }
                match parser.parse(input, location, state) {
                    ParseResult::Ok {
                        input: cur_input,
                        output: first_item,
                        location: cur_location,
                        state: cur_state,
                        committed: cur_committed,
                    } => {
                        input = cur_input;
                        location = cur_location;
                        state = cur_state;
                        committed |= cur_committed;
                        output.push(first_item);
                    }
                    ParseResult::Err {
                        message,
                        from,
                        to,
                        state,
                        committed: cur_committed,
                    } => {
                        committed |= cur_committed;
                        return ParseResult::Err {
                            message,
                            from,
                            to,
                            state,
                            committed,
                        };
                    }
                }
            }
        }

        loop {
            match end_parser.parse(input, location, ()) {
                ParseResult::Ok { .. } => {
                    return ParseResult::Ok {
                        input,
                        output,
                        location,
                        state,
                        committed,
                    };
                }
                ParseResult::Err {
                    message,
                    from,
                    to,
                    committed: err_committed,
                    ..
                } => {
                    if err_committed {
                        return ParseResult::Err {
                            message,
                            from,
                            to,
                            state,
                            committed: err_committed,
                        };
                    }
                    match parser.parse(input, location, state.clone()) {
                        ParseResult::Ok {
                            input: cur_input,
                            output: cur_item,
                            location: cur_location,
                            state: cur_state,
                            committed: cur_committed,
                        } => {
                            input = cur_input;
                            location = cur_location;
                            state = cur_state;
                            committed |= cur_committed;
                            output.push(cur_item);
                        }
                        ParseResult::Err {
                            from: end_from,
                            to: end_to,
                            committed: cur_committed,
                            ..
                        } => {
                            committed |= cur_committed;
                            if input.is_empty() {
                                // reached the end of input
                                return ParseResult::Ok {
                                    input,
                                    output,
                                    location,
                                    state,
                                    committed,
                                };
                            } else {
                                return ParseResult::Err {
                                message: format!("I'm expecting either {} or {}. However, neither was found.", item_name, end_name),
                                from: end_from,
                                to: end_to,
                                state,
                                committed,
                            };
                            }
                        }
                    }
                }
            }
        }
    })
}

/// Run the parser zero or more times and combine each output into a vector of outputs.
pub fn zero_or_more<'a, P, A, S: Clone>(parser: P) -> impl Parser<'a, Output = Vec<A>, State = S>
where
    P: Parser<'a, Output = A, State = S>,
{
    fn_parser(move |mut input, mut location, mut state: S| {
        let mut output = Vec::new();
        let mut committed = false;

        loop {
            match parser.parse(input, location, state.clone()) {
                ParseResult::Ok {
                    input: cur_input,
                    output: cur_item,
                    location: cur_location,
                    state: cur_state,
                    committed: cur_committed,
                } => {
                    input = cur_input;
                    location = cur_location;
                    state = cur_state;
                    committed |= cur_committed;
                    output.push(cur_item);
                }
                ParseResult::Err {
                    message,
                    from,
                    to,
                    state,
                    committed,
                } => {
                    if committed {
                        return ParseResult::Err {
                            message,
                            from,
                            to,
                            state,
                            committed,
                        };
                    } else {
                        break;
                    }
                }
            }
        }

        ParseResult::Ok {
            input,
            output,
            location,
            state,
            committed,
        }
    })
}

/// Match any single unicode grapheme, internally used together with `pred`.
fn any_grapheme<'a, S: Clone>(expecting: &'a str) -> impl Parser<'a, Output = &'a str, State = S> {
    fn_parser(move |input: &'a str, location: Location, state| {
        match Uni::graphemes(input, true).next() {
            Some(c) => match c {
                "\n" | "\r\n" => ParseResult::Ok {
                    input: &input[c.len()..],
                    output: c,
                    location: increment_row(1, location),
                    state,
                    committed: false,
                },
                _ => ParseResult::Ok {
                    input: &input[c.len()..],
                    output: c,
                    location: increment_col(grapheme_column_width(c), location),
                    state,
                    committed: false,
                },
            },
            _ => ParseResult::Err {
                message: format!("I'm expecting {} but reached the end of input.", expecting),
                from: location,
                to: location,
                state,
                committed: false,
            },
        }
    })
}

/// Match any single character, internally used together with `pred`.
fn any_char<'a, S: Clone>(expecting: &'a str) -> impl Parser<'a, Output = char, State = S> {
    fn_parser(
        move |input: &str, location: Location, state| match input.chars().next() {
            Some(c) => match c {
                '\n' => ParseResult::Ok {
                    input: &input[c.len_utf8()..],
                    output: c,
                    location: increment_row(1, location),
                    state,
                    committed: false,
                },
                _ => ParseResult::Ok {
                    input: &input[c.len_utf8()..],
                    output: c,
                    location: increment_col(char_column_width(c), location),
                    state,
                    committed: false,
                },
            },
            _ => ParseResult::Err {
                message: format!("I'm expecting {} but reached the end of input.", expecting),
                from: location,
                to: location,
                state,
                committed: false,
            },
        },
    )
}

/// Chomp one grapheme if it passes the test.
pub fn chomp_if<'a, F, S: Clone>(
    predicate: F,
    expecting: &'a str,
) -> impl Parser<'a, Output = (), State = S>
where
    F: Fn(&str) -> bool,
{
    any_grapheme(expecting)
        .pred(move |output| predicate(*output), expecting)
        .ignore()
}

/// Chomp one character if it passes the test.
pub fn chomp_ifc<'a, F, S: Clone>(
    predicate: F,
    expecting: &'a str,
) -> impl Parser<'a, Output = (), State = S>
where
    F: Fn(char) -> bool,
{
    any_char(expecting)
        .pred(move |output| predicate(*output), expecting)
        .ignore()
}

/// Chomp zero or more graphemes if they pass the test.
pub fn chomp_while0<'a, F, S: Clone>(
    predicate: F,
    expecting: &'a str,
) -> impl Parser<'a, Output = (), State = S>
where
    F: Fn(&str) -> bool,
{
    zero_or_more(chomp_if(predicate, expecting)).ignore()
}

/// Chomp zero or more characters if they pass the test.
///
/// This is commonly useful for chomping whiespaces and variable names:
/// ```
/// # use lip::*;
/// fn space0<'a, S>() -> impl Parser<'a, (), S> {
///   chomp_while0c(|c: &char| *c == ' ', "a whitespace")
/// }
/// ```
/// See [variable](fn.variable.html) for how this can be used to chomp variable names.
pub fn chomp_while0c<'a, F, S: Clone>(
    predicate: F,
    expecting: &'a str,
) -> impl Parser<'a, Output = (), State = S>
where
    F: Fn(char) -> bool,
{
    zero_or_more(chomp_ifc(predicate, expecting)).ignore()
}

/// Chomp one or more graphemes if they pass the test.
pub fn chomp_while1<'a, F, S: Clone>(
    predicate: F,
    expecting: &'a str,
) -> impl Parser<'a, Output = (), State = S>
where
    F: Fn(&str) -> bool,
{
    one_or_more(chomp_if(predicate, expecting)).ignore()
}

/// Chomp one or more characters if they pass the test.
///
/// This can be used to chomp digits:
/// ```
/// # use lip::*;
/// fn digits<'a, S>() -> impl Parser<'a, String, S> {
///   take_chomped(chomp_while1c(
///     &(| character: &char | character.is_digit(10)),
///     "decimal digits"
///   ))
/// }
/// ```
/// See [digits](fn.digits.html) for a more complete digits parser with leading zero checks.
pub fn chomp_while1c<'a, F, S: Clone>(
    predicate: F,
    expecting: &'a str,
) -> impl Parser<'a, Output = (), State = S>
where
    F: Fn(char) -> bool,
{
    one_or_more(chomp_ifc(predicate, expecting)).ignore()
}
/// Take the chomped string from a bunch of chompers.
///
/// Sometimes parsers like `int` or `variable` cannot do exactly what you need.
/// The "chomping" family of functions is meant for that case!
/// Maybe you need to parse valid [PHP variables](https://www.w3schools.com/php/php_variables.asp) like `$x` and `$txt`:
/// ```
/// # use lip::*;
/// fn php_variable<'a, S>() -> impl Parser<'a, String, S> {
///   take_chomped(succeed!(())
///     .skip(chomp_ifc(|c: &char| *c == '$', "a '$'"))
///     .skip(chomp_ifc(|c: &char| c.is_alphabetic() || *c == '_', "a letter or a '_'"))
///     .skip(chomp_while0c(|c: &char| c.is_alphanumeric() || *c == '_', "a letter, digit, or '_'"))
///   )
/// }
/// ```
pub fn take_chomped<'a, P, S: Clone>(parser: P) -> impl Parser<'a, Output = String, State = S>
where
    P: Parser<'a, State = S>,
{
    fn_parser(
        move |input, location, state| match parser.parse(input, location, state) {
            ParseResult::Ok {
                input: cur_input,
                location: cur_location,
                state: cur_state,
                committed: cur_committed,
                ..
            } => ParseResult::Ok {
                input: cur_input,
                output: get_difference(input, cur_input).to_string(),
                location: cur_location,
                state: cur_state,
                committed: cur_committed,
            },
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            },
        },
    )
}

fn get_difference<'a>(whole_str: &'a str, substr: &'a str) -> &'a str {
    &whole_str[..whole_str.len() - substr.len()]
}

fn pred<'a, P, F>(parser: P, predicate: F, expecting: &'a str) -> Pred<'a, P, F>
where
    P: Parser<'a>,
    F: Fn(&P::Output) -> bool,
{
    Pred(parser, predicate, expecting)
}

/// Parse a single space character.
fn space_char<'a, S: Clone>() -> impl Parser<'a, Output = (), State = S> {
    chomp_if(&(|c: &str| c == " "), "a whitespace")
}

/// Parse a single newline character.
///
/// Handles `\r\n` in Windows and `\n` on other platforms.
fn newline_char<'a, S: Clone>() -> impl Parser<'a, Output = (), State = S> {
    fn_parser(move |input, location, state: S| {
        let mut cur_input: &str = input;
        let mut cur_location: Location = location;
        let mut cur_state: S = state.clone();
        let result1 =
            chomp_ifc(&(|c: char| c == '\r'), "a carriage return").parse(input, location, state);
        if let ParseResult::Ok {
            input,
            location,
            state,
            ..
        } = result1
        {
            cur_input = input;
            cur_location = location;
            cur_state = state;
        }
        let result = chomp_ifc(&(|c: char| c == '\n'), "a newline").parse(
            cur_input,
            cur_location,
            cur_state,
        );
        match result {
            ParseResult::Ok {
                input,
                output,
                location,
                state,
                committed,
            } => ParseResult::Ok {
                input,
                output,
                state,
                committed,
                location: increment_row(1, location),
            },
            err @ ParseResult::Err { .. } => err,
        }
    })
    .ignore()
}

/// Parsers zero or more newline characters, each with indentations in front.
///
/// Indentation can also be `""` (no indentation)
pub fn newline0<'a, P, S: Clone>(indent_parser: P) -> impl Parser<'a, Output = (), State = S>
where
    P: Parser<'a, Output = (), State = S>,
{
    zero_or_more(pair(indent_parser, newline_char())).ignore()
}

/// Parsers one or more newline characters, each with indentations in front.
///
/// Indentation can also be `""` (no indentation)
pub fn newline1<'a, P>(indent_parser: P) -> impl Parser<'a, Output = ()>
where
    P: Parser<'a, Output = ()>,
{
    pair(newline_char(), newline0(indent_parser)).ignore()
}

/// Parse zero or more space characters.
pub fn space0<'a, S: Clone>() -> impl Parser<'a, Output = (), State = S> {
    zero_or_more(space_char()).ignore()
}

/// Parse one or more space characters.
pub fn space1<'a, S: Clone>() -> impl Parser<'a, Output = (), State = S> {
    one_or_more(space_char()).ignore()
}

/// Parse an indentation specified the number of spaces.
pub fn indent<'a, S: Clone>(number_of_spaces: usize) -> impl Parser<'a, Output = (), State = S> {
    repeat(number_of_spaces, space_char())
        .ignore()
        .map_err(move |_| {
            format!(
                "I'm expecting an indentation.\nAll indentations should be {} spaces.",
                number_of_spaces
            )
        })
}

/// Parse a given number of indentations specified the number of spaces.
pub fn indents<'a, S: Clone>(
    number_of_spaces: usize,
    number_of_indents: usize,
) -> impl Parser<'a, Output = (), State = S> {
    repeat(number_of_indents, indent(number_of_spaces))
        .map_err(move |_| {
            format!(
                "I'm expecting {} indentation{}.\nAll indentations should be {} spaces.",
                number_of_indents,
                plural_suffix(number_of_indents),
                number_of_spaces,
            )
        })
        .ignore()
}

fn plural_suffix(count: usize) -> &'static str {
    if count > 1 {
        "s"
    } else {
        ""
    }
}

/// Repeat a parser n times
pub fn repeat<'a, A, P, S: Clone>(
    times: usize,
    parser: P,
) -> impl Parser<'a, Output = Vec<A>, State = S>
where
    P: Parser<'a, Output = A, State = S>,
{
    fn_parser(move |mut input, mut location, mut state: S| {
        let mut output = Vec::new();
        let mut committed = false;

        if times == 0 {
            return ParseResult::Ok {
                input,
                location,
                output,
                state,
                committed,
            };
        }

        let mut counter = 0;

        while let ParseResult::Ok {
            input: cur_input,
            output: cur_item,
            location: cur_location,
            state: cur_state,
            committed: cur_committed,
        } = parser.parse(input, location, state.clone())
        {
            if counter >= times {
                break;
            }
            input = cur_input;
            location = cur_location;
            state = cur_state;
            output.push(cur_item);
            counter += 1;
            committed |= cur_committed;
        }

        ParseResult::Ok {
            input,
            output,
            location,
            state,
            committed,
        }
    })
}

/// Parse one of many things.
///
/// Parser goes through each one option in order until one succeeds.
/// If none succeeds, return error.
#[macro_export]
macro_rules! one_of {
  ($single_parser:expr) => { $single_parser };
  ($first_parser:expr, $($parsers:expr),+) => {
    either($first_parser, one_of!($($parsers),*))
  };
}

/// Choose either the left parser or the right parser to parse.
///
/// For choosing between more than two parsers, use [`one_of!`](macro.one_of!.html)
#[doc(hidden)]
pub fn either<'a, P1, P2, A, S: Clone>(
    parser1: P1,
    parser2: P2,
) -> impl Parser<'a, Output = A, State = S>
where
    P1: Parser<'a, Output = A, State = S>,
    P2: Parser<'a, Output = A, State = S>,
{
    fn_parser(move |input, location, state| {
        let result = match parser1.parse(input, location, state) {
            ok @ ParseResult::Ok { .. } => ok,
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => {
                if committed {
                    ParseResult::Err {
                        message,
                        from,
                        to,
                        state,
                        committed,
                    }
                } else {
                    parser2.parse(input, location, state)
                }
            }
        };
        result
    })
}

/// Optionally parse something. Returns supplied default value if parse failed.
pub fn optional_with_default<'a, A: Clone, P, S: Clone>(
    default: A,
    parser: P,
) -> impl Parser<'a, Output = A, State = S>
where
    P: Parser<'a, Output = A, State = S>,
{
    either(
        parser,
        fn_parser(move |input, location, state| ParseResult::Ok {
            input,
            location,
            output: default.clone(),
            state,
            committed: false,
        }),
    )
}

/// Optionally parse something.
pub fn optional<'a, A, P, S: Clone>(parser: P) -> impl Parser<'a, Output = Option<A>, State = S>
where
    P: Parser<'a, Output = A, State = S>,
{
    either(
        parser.map(Some),
        fn_parser(move |input, location, state| ParseResult::Ok {
            input,
            location,
            output: None,
            state,
            committed: false,
        }),
    )
}

/// Parse a newline that maybe preceeded by a comment started with `comment_symbol`.
pub fn newline_with_comment<'a, S: Clone>(
    comment_symbol: &'a str,
) -> impl Parser<'a, Output = (), State = S> {
    succeed!(())
        .skip(space0())
        .skip(either(newline_char(), line_comment(comment_symbol)))
}

/// Parse a line comment started with `comment_symbol`.
pub fn line_comment<'a, S: Clone>(
    comment_symbol: &'a str,
) -> impl Parser<'a, Output = (), State = S> {
    succeed!(())
        .skip(token(comment_symbol))
        .skip(zero_or_more(chomp_ifc(
            &(|c: char| c != '\n' && c != '\r'),
            "any character",
        )))
        .skip(newline_char())
}

/// Parses a decimal integer, excluding the sign in front.
///
/// run int "1"    == Ok 1
///
/// run int "1234" == Ok 1234
///
/// run int "-789" == Err ...
///
/// run int "0123" == Err ...
///
/// run int "1.34" == Err ...
///
/// run int "1e31" == Err ...
///
/// run int "123a" == Err ...
///
/// run int "0x1A" == Err ...
pub fn int<'a, S: Clone>() -> impl Parser<'a, Output = usize, State = S> {
    digits("an integer", false).map(|int_str| int_str.parse().unwrap())
}

/// Parses a floating point number, excluding the sign in front.
///
/// run float "123"       == Ok 123
///
/// run float "3.1415"    == Ok 3.1415
///
/// run float "0.1234"    == Ok 0.1234
///
/// run float ".1234"     == Err ...
///
/// run float "1e-42"     == Ok 1e-42
///
/// run float "6.022e23"  == Ok 6.022e23
///
/// run float "6.022E23"  == Ok 6.022e23
///
/// run float "6.022e+23" == Ok 6.022e23
pub fn float<'a, S: Clone>() -> impl Parser<'a, Output = f64, State = S> {
    let expecting = "a floating point number";
    succeed!(
        |whole: String, fraction: Option<String>, exponent: Option<String>| (whole
            + &fraction.unwrap_or_default()
            + &exponent.unwrap_or_default())
            .parse()
            .unwrap()
    )
    .keep(digits(expecting, false))
    .keep(optional(
        right(token("."), digits(expecting, true)).map(|digits| ".".to_owned() + &digits),
    ))
    .keep(optional(
        succeed!(|sign: Option<&'a str>, exponent: String| "e".to_string()
            + sign.unwrap_or_default()
            + &exponent)
        .skip(either(token("e"), token("E")))
        .keep(optional(either(token("+"), token("-"))))
        .keep(digits(expecting, false)),
    ))
}

fn digits<'a, S: Clone>(
    name: &'a str,
    allow_leading_zeroes: bool,
) -> impl Parser<'a, Output = String, State = S> {
    take_chomped(chomp_while1c(&(|c: char| c.is_digit(10)), name)).update(
        move |input, digits: String, location: Location, state: S| {
            if !allow_leading_zeroes && digits.starts_with('0') && digits.len() > 1 {
                ParseResult::Err {
                    message: format!("You can't have leading zeroes in {}.", name),
                    from: Location {
                        col: location.col - digits.len(),
                        ..location
                    },
                    to: location,
                    state,
                    committed: false,
                }
            } else {
                ParseResult::Ok {
                    input,
                    output: digits,
                    location,
                    state,
                    committed: true,
                }
            }
        },
    )
}

/// Parse a variable.
///
/// If we want to parse a PascalCase variable excluding three reserved words, we can try something like:
/// ```
/// # use lip::*;
/// let reserved = &([ "Func", "Import", "Export" ].iter().cloned().map(| element | element.to_string()).collect());
/// assert_succeed(
///   variable(&(|c| c.is_uppercase()), &(|c| c.is_lowercase()), &(|_| false), reserved, "a PascalCase variable"),
///   "Dict", "Dict".to_string()
/// );
/// ```
/// If we want to parse a snake_case variable, we can try something like:
/// ```
/// # use lip::*;
/// # use std::collections::HashSet;
/// assert_succeed(
///  variable(&(|c| c.is_lowercase()), &(|c| c.is_lowercase() || c.is_digit(10)), &(|c| *c == '_'), &HashSet::new(), "a snake_case variable"),
///  "my_variable_1", "my_variable_1".to_string()
/// );
/// ```
/// The below uses the same snake_case variable parser. However, the separator `_` appeared at the end of the name `invalid_variable_name_`:
/// ```
/// # use lip::*;
/// # use std::collections::HashSet;
/// assert_fail(
///  variable(&(|c| c.is_lowercase()), &(|c| c.is_lowercase() || c.is_digit(10)), &(|c| *c == '_'), &HashSet::new(), "a snake_case variable"),
///  "invalid_variable_name_", "I'm expecting a snake_case variable but found `invalid_variable_name_` ended with the separator `_`."
/// );
/// ```
pub fn variable<'a, S: Clone, F1, F2, F3>(
    start: &'a F1,
    inner: &'a F2,
    separator: &'a F3,
    reserved: &'a HashSet<String>,
    expecting: &'a str,
) -> impl Parser<'a, Output = String, State = S>
where
    F1: Fn(char) -> bool,
    F2: Fn(char) -> bool,
    F3: Fn(char) -> bool,
{
    take_chomped(pair(
        chomp_ifc(start, expecting),
        chomp_while0c(move |c: char| inner(c) || separator(c), expecting),
    ))
    .update(move |input, name, location, state| {
        if reserved.contains(&name) {
            ParseResult::Err {
                message: format!(
                    "I'm expecting {} but found a reserved word `{}`.",
                    expecting, name
                ),
                from: Location {
                    col: location.col - name.len(),
                    ..location
                },
                to: location,
                state,
                committed: false,
            }
        } else if name
            .chars()
            .zip(name[1..].chars())
            .any(|(c, next_c)| separator(c) && separator(next_c))
        {
            ParseResult::Err {
                message: format!(
                    "I'm expecting {} but found `{}` with duplicated separators.",
                    expecting, name
                ),
                from: Location {
                    col: location.col - name.len(),
                    ..location
                },
                to: location,
                state,
                committed: false,
            }
        } else if separator(name.chars().last().unwrap()) {
            ParseResult::Err {
                message: format!(
                    "I'm expecting {} but found `{}` ended with the separator `{}`.",
                    expecting,
                    name,
                    &name.chars().last().unwrap()
                ),
                from: Location {
                    col: location.col - name.len(),
                    ..location
                },
                to: location,
                state,
                committed: false,
            }
        } else {
            ParseResult::Ok {
                input,
                location,
                output: name,
                state,
                committed: true,
            }
        }
    })
}

/// What’s the deal with trailing commas? Are they Forbidden? Are they Optional? Are they Mandatory?
#[derive(Copy, Clone)]
pub enum Trailing {
    Forbidden,
    Optional,
    Mandatory,
}

pub enum OneOfTwo<T1, T2> {
    First(T1),
    Second(T2),
}

impl<'a, P1, P2, S: Clone> Parser<'a> for OneOfTwo<P1, P2>
where
    P1: Parser<'a, State = S>,
    P2: Parser<'a, Output = P1::Output, State = S>,
{
    type Output = P1::Output;
    type State = S;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        match *self {
            OneOfTwo::First(ref p) => p.parse(input, location, state),
            OneOfTwo::Second(ref p) => p.parse(input, location, state),
        }
    }
}

pub enum OneOfThree<T1, T2, T3> {
    First(T1),
    Second(T2),
    Third(T3),
}

impl<'a, P1, P2, P3, S: Clone> Parser<'a> for OneOfThree<P1, P2, P3>
where
    P1: Parser<'a, State = S>,
    P2: Parser<'a, Output = P1::Output, State = S>,
    P3: Parser<'a, Output = P1::Output, State = S>,
{
    type Output = P1::Output;
    type State = S;

    fn parse(
        &self,
        input: &'a str,
        location: Location,
        state: Self::State,
    ) -> ParseResult<'a, Self::Output, Self::State> {
        match *self {
            OneOfThree::First(ref p) => p.parse(input, location, state),
            OneOfThree::Second(ref p) => p.parse(input, location, state),
            OneOfThree::Third(ref p) => p.parse(input, location, state),
        }
    }
}

/// Parse a sequence like lists or code blocks.
///
/// Example:
/// Parse a list containing the string "abc" with optional trailing comma:
/// ```
/// # use lip::*;
/// assert_succeed(sequence(
///   "[",
///   token("abc"),
///   ",",
///   space0(),
///   "]",
///   Trailing::Optional),
/// "[abc, abc, abc]", vec!["abc", "abc", "abc"]);
/// ```
/// Note: `spaces` are inserted between every part.
/// So if you use `space1` instead of `space0`, you need to
/// put more spaces before and after separators, between
/// start symbol and first item and between last item or separator
/// and the end symbol:
/// ```
/// # use lip::*;
/// assert_succeed(sequence(
///   "[",
///   token("abc"),
///   ",",
///   space1(),
///   "]",
///   Trailing::Optional),
/// "[ abc , abc , abc ]", vec!["abc", "abc", "abc"]);
/// ```
pub fn sequence<'a, A, ItemParser, SpacesParser, S: Clone>(
    start: &'static str,
    item: ItemParser,
    separator: &'static str,
    spaces: SpacesParser,
    end: &'static str,
    trailing: Trailing,
) -> impl Parser<'a, Output = Vec<A>>
where
    ItemParser: Parser<'a, Output = A, State = S> + Clone,
    SpacesParser: Parser<'a, Output = (), State = S> + Clone,
{
    wrap(
        pair(token(start), spaces.clone()),
        optional(
            pair(
                item.clone(),
                right(
                    spaces.clone(),
                    left(
                        zero_or_more(wrap(
                            left(token(separator), spaces.clone()).backtrackable(),
                            item.clone(),
                            spaces.clone(),
                        )),
                        match trailing {
                            Trailing::Forbidden => token("").first_of_three(),
                            Trailing::Optional => {
                                optional_with_default("", left(token(separator), spaces.clone()))
                                    .second_of_three()
                            }
                            Trailing::Mandatory => {
                                left(token(separator), spaces.clone()).third_of_three()
                            }
                        },
                    ),
                ),
            )
            .map(move |(first_item, mut rest_items)| {
                rest_items.insert(0, first_item);
                rest_items
            }),
        )
        .map(|items| items.unwrap_or(vec![])),
        token(end),
    )
}

/// Wrap a parser with two other delimiter parsers
fn wrap<'a, A, B, C, P1, P2, P3, S: Clone>(
    left_delimiter: P1,
    wrapped: P2,
    right_delimiter: P3,
) -> impl Parser<'a, Output = B, State = S>
where
    P1: Parser<'a, Output = A, State = S>,
    P2: Parser<'a, Output = B, State = S>,
    P3: Parser<'a, Output = C, State = S>,
{
    right(left_delimiter, left(wrapped, right_delimiter))
}

/// Record the beginning and ending location of the thing being parsed.
///
/// You can surround any parser with `located` and remember the location
/// of the parsed output for later error messaging or text processing.
pub fn located<'a, P, A>(parser: P) -> impl Parser<'a, Output = Located<A>>
where
    P: Parser<'a, Output = A>,
{
    fn_parser(
        move |input, location, state| match parser.parse(input, location, state) {
            ParseResult::Ok {
                input: cur_input,
                output,
                location: cur_location,
                state: cur_state,
                committed: cur_committed,
            } => ParseResult::Ok {
                input: cur_input,
                output: Located {
                    value: output,
                    from: Location {
                        row: location.row,
                        col: location.col,
                    },
                    to: Location {
                        row: cur_location.row,
                        col: cur_location.col,
                    },
                },
                location: cur_location,
                state: cur_state,
                committed: cur_committed,
            },
            ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            } => ParseResult::Err {
                message,
                from,
                to,
                state,
                committed,
            },
        },
    )
}

/// Pretty print the error.
///
/// Example:
/// 1| A=A+2
///      ^^^
/// ⚠️ I can't find a computation instruction matching `A+2`.
/// Try something like `D+1` and `0`.
pub fn display_error(source: &str, error_message: String, from: Location, to: Location) -> String {
    let row = from.row;
    let col = from.col;
    let error_length = if to.col == from.col {
        1
    } else {
        to.col - from.col
    };
    let row_tag = row.to_string();
    let row_tag_len = row_tag.len();
    let error_line = row_tag + "| " + source.split('\n').collect::<Vec<&str>>()[row - 1];
    let error_pointer = " ".repeat(col - 1 + row_tag_len + 2) + &"^".repeat(error_length);
    error_line + "\n" + &error_pointer + "\n" + "⚠️ " + &error_message
}

fn update_state<'a, P, F>(parser: P, f: F) -> UpdateState<P, F>
where
    P: Parser<'a>,
    F: Fn(P::Output, P::State) -> P::State,
{
    UpdateState(parser, f)
}

fn update<'a, P, A, B, F>(parser: P, f: F) -> Update<P, F>
where
    P: Parser<'a>,
    F: Fn(&'a str, A, Location, P::State) -> ParseResult<'a, B, P::State>,
{
    Update(parser, f)
}

#[doc(hidden)]
pub fn assert_succeed<'a, P, A: PartialEq + Debug>(parser: P, source: &'a str, expected: A)
where
    P: Parser<'a, Output = A, State = ()>,
{
    assert_eq!(
        parser
            .parse(source, Location { row: 1, col: 1 }, ())
            .unwrap(source),
        expected
    )
}

#[doc(hidden)]
pub fn assert_fail<'a, P, A: Debug>(parser: P, source: &'a str, message: &'a str)
where
    P: Parser<'a, Output = A, State = ()>,
{
    assert_eq!(
        parser
            .parse(source, Location { row: 1, col: 1 }, ())
            .unwrap_err(),
        message
    )
}

/// Returns the number of cells visually occupied by a sequence
/// of graphemes
/// source: https://github.com/unicode-rs/unicode-width/issues/4#issuecomment-549906181
fn unicode_column_width(s: &str) -> usize {
    s.graphemes(true).map(grapheme_column_width).sum()
}

/// Returns the number of cells visually occupied by a grapheme.
/// The input string must be a single grapheme.
/// source: https://github.com/unicode-rs/unicode-width/issues/4#issuecomment-549906181
fn grapheme_column_width(s: &str) -> usize {
    // Due to this issue:
    // https://github.com/unicode-rs/unicode-width/issues/4
    // we cannot simply use the unicode-width crate to compute
    // the desired value.
    // Let's check for emoji-ness for ourselves first
    use xi_unicode::EmojiExt;
    for c in s.chars() {
        if c.is_emoji_modifier_base() || c.is_emoji_modifier() {
            // treat modifier sequences as double wide
            return 2;
        }
    }
    UnicodeWidthStr::width(s)
}

fn char_column_width(c: char) -> usize {
    UnicodeWidthChar::width(c).unwrap_or(0)
}
