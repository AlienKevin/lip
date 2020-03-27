//! # Lip Parsing Library
//! 
//! Lip provides powerful parser combinators for you to
//! create reusable and flexible parsers.

#[macro_use]
mod tests;

use std::rc::Rc;
use std::fmt::*;
use std::collections::HashSet;

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
/// at row 1 and column 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
  pub row: usize,
  pub col: usize,
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
  },
  Err {
    message: String,
    from: Location,
    to: Location,
    state: State,
  },
}

impl<'a, T, S: Clone> ParseResult<'a, T, S> {
  /// Map the parse output to a new value if parse succeeds.
  /// Otherwise, return error as usual.
  pub fn map<U, F: FnOnce(T) -> U>(self, func: F) -> ParseResult<'a, U, S> {
    match self {
      ParseResult::Ok { input, location, output, state } =>
        ParseResult::Ok {
          input,
          location,
          output: func(output),
          state,
        },
      ParseResult::Err { message, from, to, state } =>
        ParseResult::Err { message, from, to, state },
    }
  }
  /// Map the parse output to a new value if parse succeeds.
  /// The map function is supplied both the output and the
  /// state of the parser.
  /// Otherwise, return error as usual.
  pub fn map_with_state<U, F: FnOnce(T, S) -> U>(self, func: F) -> ParseResult<'a, U, S> {
    match self {
      ParseResult::Ok { input, location, output, state } =>
        ParseResult::Ok {
          input,
          location,
          output: func(output, state.clone()),
          state: state,
        },
      ParseResult::Err { message, from, to, state } =>
        ParseResult::Err { message, from, to, state },
    }
  }
  /// Map the error message to a new message if parse fails.
  /// Otherwise, return output as usual.
  pub fn map_err<F: FnOnce(String) -> String>(self, func: F) -> ParseResult<'a, T, S> {
    match self {
      ParseResult::Ok { input, location, output, state } =>
        ParseResult::Ok {
          input,
          location,
          output,
          state,
        },
      ParseResult::Err { message, from, to, state } =>
        ParseResult::Err {
          message: func(message),
          from,
          to,
          state,
        }
    }
  }
  /// Returns a new parser which is given the current output if parse succeeds.
  /// Otherwise, return error as usual.
  pub fn and_then<U, F: FnOnce(&'a str, T, Location, S) -> ParseResult<'a, U, S>>(self, func: F) -> ParseResult<'a, U, S> {
    match self {
      ParseResult::Ok { input, output, location, state } =>
        func(input, output, location, state),
      ParseResult::Err { message, from, to, state } =>
        ParseResult::Err { message, from, to, state },
    }
  }
  fn unwrap(self, source: &'a str) -> T {
    match self {
      ParseResult::Ok { output, .. } =>
        output,
      ParseResult::Err { message, from, to, .. } =>
        panic!(display_error(source, message, from, to)),
    }
  }
  fn unwrap_err(self, source: &'a str) -> ParseResult<'a, T, S>
  where
    T: Debug + 'a
  {
    match self {
      ParseResult::Ok { output, .. } =>
        panic!(format!("{:#?}", output)),
      ParseResult::Err { message, from, to, state } =>
        ParseResult::Err { message, from, to, state },
    }
  }
}

pub trait Parser<'a, Output, State: Clone> {
  /// Run the parser on a given input, starting at
  /// a given location and state.
  fn parse(&self, input: &'a str, location: Location, state: State) -> ParseResult<'a, Output, State>;
  /// Map the output to a new output if parse succeeds.
  /// Otherwise, return error as usual.
  /// 
  /// The only difference from the `map` on `ParseResult`
  /// is that this `map` turns one `Parser` into another while the `map`
  /// on `ParseResult` turns one `ParseResult` into another.
  fn map<F, NewOutput>(self, map_fn: F) -> BoxedParser<'a, NewOutput, State>
    where
        Self: Sized + 'a,
        Output: 'a,
        NewOutput: 'a,
        State: 'a,
        F: Fn(Output) -> NewOutput + 'a,
  {
      BoxedParser::new(map(self, map_fn))
  }
  /// The map function is supplied both the output and the
  /// state of the parser.
  /// Otherwise, return error as usual.
  /// 
  /// The only difference from the `map_with_state` on `ParseResult`
  /// is that this `map_with_state` turns one `Parser` into another while the `map_with_state`
  /// on `ParseResult` turns one `ParseResult` into another.
  fn map_with_state<F, NewOutput>(self, map_fn: F) -> BoxedParser<'a, NewOutput, State>
  where
      Self: Sized + 'a,
      Output: 'a,
      NewOutput: 'a,
      State: 'a,
      F: Fn(Output, State) -> NewOutput + 'a,
  {
      BoxedParser::new(map_with_state(self, map_fn))
  }
  /// Map the error message to a new message if parse fails.
  /// Otherwise, return output as usual.
  /// 
  /// The only difference from the `map_err` on `ParseResult`
  /// is that this `map_err` turns one `Parser` into another while the `map_err`
  /// on `ParseResult` turns one `ParseResult` into another.
  fn map_err<F>(self, map_fn: F) -> BoxedParser<'a, Output, State>
    where
        Self: Sized + 'a,
        Output: 'a,
        State: 'a,
        F: Fn(String) -> String + 'a,
  {
      BoxedParser::new(map_err(self, map_fn))
  }
  /// Returns a new parser which is given the current output if parse succeeds.
  /// Otherwise, return error as usual.
  /// 
  /// The only difference from the `and_then` on `ParseResult`
  /// is that this `and_then` turns one `Parser` into another while the `and_then`
  /// on `ParseResult` turns one `ParseResult` into another.
  fn and_then<F, NextParser, NewOutput>(self, f: F) -> BoxedParser<'a, NewOutput, State>
  where
    Self: Sized + 'a,
    Output: 'a,
    NewOutput: 'a,
    State: 'a,
    NextParser: Parser<'a, NewOutput, State> + 'a,
    F: Fn(Output) -> NextParser + 'a,
  {
      BoxedParser::new(and_then(self, f))
  }
  /// Judge if the output meets the requirement using a predicate function
  /// if the parse succeeds. Otherwise, return error as usual.
  fn pred<F>(self, predicate: &'a F, expecting: &'a str) -> BoxedParser<'a, Output, State>
  where
    Self: Sized + 'a,
    Output: std::fmt::Display + 'a,
    State: 'a,
    F: Fn(&Output) -> bool + 'a,
  {
    BoxedParser::new(pred(self, predicate, expecting))
  }
  /// Ignore the parse output and return `()` (emtpy tuple)
  fn ignore(self) -> BoxedParser<'a, (), State>
    where
      Self: Sized + 'a,
      Output: 'a,
      State: 'a,
  {
      BoxedParser::new(map(self, |_| ()))
  }
  /// Update the state given the new output and state of the parse if parse succeeds.
  /// Otherwise, return error as usual.
  fn update_state<F>(self, f: F) -> BoxedParser<'a, Output, State>
  where
    Self: Sized + 'a,
    State: 'a,
    Output: Clone + 'a,
    F: Fn(Output, State) -> State + 'a,
  {
    BoxedParser::new(update_state(self, f))
  }
  /// Update the result of the parser if parse succeeds.
  /// Otherwise, return error as usual.
  /// 
  /// This is the most general and powerful method of the parser.
  /// Think about using simpler methods like `map` and `map_err` before
  /// choosing `update`.
  fn update<F, NewOutput>(self, f: F) -> BoxedParser<'a, NewOutput, State>
  where
    Self: Sized + 'a,
    State: 'a,
    Output: Clone + 'a,
    NewOutput: Clone + 'a,
    F: Fn(&'a str, Output, Location, State) -> ParseResult<'a, NewOutput, State> + 'a,
  {
    BoxedParser::new(update(self, f))
  }
  /// Check if you have reached the end of the input you are parsing.
  /// 
  /// If you want to parse an input containing only "abc":
  /// ```
  /// # use lip::*;
  /// assert_eq!(
  ///  token("abc").end().parse("abc", Location { row: 1, col: 1}, ()),
  ///  ParseResult::Ok {
  ///    input: "",
  ///    output: "abc",
  ///    location: Location { row: 1, col: 4 },
  ///    state: (),
  ///  }
  ///);
  ///assert_eq!(
  ///  token("abc").end().parse("abcd", Location { row: 1, col: 1}, ()),
  ///  ParseResult::Err {
  ///    message: "I'm expecting the end of input.".to_string(),
  ///    from: Location { row: 1, col: 4 },
  ///    to: Location { row: 1, col: 4 },
  ///    state: (),
  ///  }
  ///);
  /// ```
  fn end(self) -> BoxedParser<'a, Output, State>
  where
    Self: Sized + 'a,
    Output: Clone + 'a,
    State: 'a,
  {
    BoxedParser::new(end(self))
  }
}

impl<'a, F, Output, State: 'a> Parser<'a, Output, State> for F
where
  F: Fn(&'a str, Location, State) -> ParseResult<'a, Output,State>,
  State: Clone,
{
  fn parse(&self, input: &'a str, location: Location, state: State) -> ParseResult<'a, Output, State> {
    self(input, location, state)
  }
}

impl<'a, Output: 'a, State: 'a> Clone for BoxedParser<'a, Output, State> {
  fn clone(&self) -> Self {
    BoxedParser {
      parser: self.parser.clone()
    }
  }
}

/// Box `Parser` trait so its size is decidable in compile time.
/// 
/// Essentially allocate the `Parser` on the heap in runtime.
/// Makes passing `Parser` around much easier because types that `impl trait`
/// may be different under the hood while `BoxedParser` is always a pointer
/// to a place in the heap.
pub struct BoxedParser<'a, Output, State> {
  parser: Rc<dyn Parser<'a, Output, State> + 'a>,
}

impl<'a, Output,State> BoxedParser<'a, Output, State> {
  /// Box any type that implements the `Parser` trait
  pub fn new<P>(parser: P) -> Self
  where
      P: Parser<'a, Output, State> + 'a,
      State: Clone,
  {
      BoxedParser {
          parser: Rc::new(parser),
      }
  }
}

impl<'a, Output, State> Parser<'a, Output, State> for BoxedParser<'a, Output, State>
  where
    State: Clone,
  {
  fn parse(&self, input: &'a str, location: Location, state: State) -> ParseResult<'a, Output, State> {
      self.parser.parse(input, location, state)
  }
}

fn and_then<'a, P, F, A, B, S: Clone + 'a, NextP>(parser: P, f: F) -> impl Parser<'a, B, S>
  where
    P: Parser<'a, A, S>,
    NextP: Parser<'a, B, S>,
    F: Fn(A) -> NextP,
    S: Clone,
{
  move |input, location, state| parser.parse(input, location, state)
    .and_then(| next_input, next_output, next_location, next_state: S |
      f(next_output).parse(next_input, next_location, next_state)
    )
}

/// Parse a given token string.
pub fn token<'a, S: Clone + 'a>(expected: &'static str) -> BoxedParser<'a, &str, S> {
  BoxedParser::new(
    move |input: &'a str, location: Location, state: S| {
    let found = input.get(0..expected.len());
    match found {
      Some(next) if next == expected => ParseResult::Ok {
        input: &input[expected.len()..],
        output: expected,
        location: increment_col(expected.len(), location),
        state,
      },
      _ => ParseResult::Err {
        message: format!(
          "I'm expecting a `{}` but found {}.",
          expected,
          display_token(found)
        ),
        from: location,
        to: match found {
          Some(found_str) => Location {
            col: location.col + found_str.len(),
            ..location
          },
          None => location,
        },
        state,
      },
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

fn display_token<T: Display>(token: Option<T>) -> String {
  match token {
    Some(token_content) => format!("`{}`", token_content).replace("\n", "\\n"),
    None => "nothing".to_string(),
  }
}

/// Pair up two parsers. Run the left parser, then the right,
/// and last combine both outputs into a tuple.
pub fn pair<'a, P1, P2, R1, R2, S: Clone + 'a>(parser1: P1, parser2: P2) -> impl Parser<'a, (R1, R2), S>
where
  P1: Parser<'a, R1, S>,
  P2: Parser<'a, R2, S>,
{
  move |input, location, state|
    parser1.parse(input, location, state)
      .and_then(| next_input, first_output, next_location, next_state: S |
        parser2.parse(next_input, next_location, next_state).map(| second_output |
          (first_output, second_output)
        )
      )
}

fn map<'a, P: 'a, F: 'a, A, B, S: Clone + 'a>(parser: P, map_fn: F) -> BoxedParser<'a, B, S>
where
  P: Parser<'a, A, S>,
  F: Fn(A) -> B,
{
  BoxedParser::new(
    move |input, location, state| parser.parse(input, location, state).map(
    |output| map_fn(output)
  ))
}

fn map_with_state<'a, P: 'a, F: 'a, A, B, S: Clone + 'a>(parser: P, map_fn: F) -> BoxedParser<'a, B, S>
where
  P: Parser<'a, A, S>,
  F: Fn(A, S) -> B,
{
  BoxedParser::new(
    move |input, location, state: S| match parser.parse(input, location, state.clone()) {
      ParseResult::Ok {
        input: next_input,
        output,
        location: next_location,
        state: next_state,
      } => ParseResult::Ok {
        input: next_input,
        location: next_location,
        output: map_fn(output, next_state.clone()),
        state: next_state,
      },
      ParseResult::Err {
        message,
        from,
        to,
        state: error_state,
      } => ParseResult::Err {
        message,
        from,
        to,
        state: error_state,
      }
    }
  )
}

fn map_err<'a, P, F, A, S: Clone + 'a>(parser: P, map_fn: F) -> impl Parser<'a, A, S>
where
  P: Parser<'a, A, S>,
  F: Fn(String) -> String,
{
  move |input, location, state| parser.parse(input, location, state).map_err(
    |error_message| map_fn(error_message)
  )
}

/// Run the left parser, then the right, last keep the left result and discard the right.
pub fn left<'a, P1: 'a, P2: 'a, R1: 'a, R2: 'a, S: Clone + 'a>(parser1: P1, parser2: P2) -> BoxedParser<'a, R1, S>
where
  P1: Parser<'a, R1, S>,
  P2: Parser<'a, R2, S>,
{
  map(pair(parser1, parser2), |(left, _right)| left)
}

/// Run the left parser, then the right, last keep the right result and discard the left.
pub fn right<'a, P1: 'a, P2: 'a, R1: 'a, R2: 'a, S: Clone + 'a>(parser1: P1, parser2: P2) -> BoxedParser<'a, R2, S>
where
  P1: Parser<'a, R1, S>,
  P2: Parser<'a, R2, S>,
{
  map(pair(parser1, parser2), |(_left, right)| right)
}

/// Run the parser one or more times and combine each output into a vector of outputs.
pub fn one_or_more<'a, P, A, S: Clone + 'a>(parser: P) -> impl Parser<'a, Vec<A>, S>
where
  P: Parser<'a, A, S>
{
  move |mut input, mut location, mut state: S| {
    let mut result = Vec::new();

    match parser.parse(input, location, state.clone()) {
      ParseResult::Ok {
        input: next_input,
        output: first_item,
        location: next_location,
        state: next_state,
      } => {
        input = next_input;
        location = next_location;
        state = next_state;
        result.push(first_item);
      }
      ParseResult::Err {
        message,
        from,
        to,
        state
      } => {
        return ParseResult::Err { message, from, to, state };
      }
    }

    loop {
      match parser.parse(input, location, state.clone()) {
        ParseResult::Ok {
          input: next_input,
          output: next_item,
          location: next_location,
          state: next_state,
        } => {
          input = next_input;
          location = next_location;
          state = next_state;
          result.push(next_item);
        },
        ParseResult::Err {..} => break
      }
    }

    ParseResult::Ok {
      input: input,
      output: result,
      location: location,
      state: state,
    }
  }
}

fn end<'a, P: 'a, A: Clone + 'a, S: Clone + 'a>(parser: P) -> impl Parser<'a, A, S>
where
  P: Parser<'a, A, S>,
{
  parser.update(|input, output, location, state|
    if input != "" {
      ParseResult::Err {
        message: "I'm expecting the end of input.".to_string(),
        from: location,
        to: location,
        state,
      }
    } else {
      ParseResult::Ok { input, output, location, state }
    }
  )
}

/// Run the parser zero or more times and combine each output into a vector of outputs.
pub fn zero_or_more<'a, P: 'a, A, S: Clone + 'a>(parser: P) -> BoxedParser<'a, Vec<A>, S>
where
  P: Parser<'a, A, S>,
{
  BoxedParser::new(
    move |mut input, mut location, mut state: S| {
    let mut result = Vec::new();

    while let ParseResult::Ok {
      input: next_input,
      output: next_item,
      location: next_location,
      state: next_state,
    } = parser.parse(input, location, state.clone())
    {
      input = next_input;
      location = next_location;
      state = next_state;
      result.push(next_item);
    }

    ParseResult::Ok {
      input: input,
      output: result,
      location: location,
      state: state,
    }
  })
}

/// Match any single character, usually used together with `pred`.
/// 
/// Exmaple:
/// ```
/// # use lip::*;
/// # use crate::lip::Parser;
/// pub fn whole_decimal<'a, S: Clone + 'a>() -> impl Parser<'a, usize, S> {
///   one_or_more(
///     any_char().pred(
///     &(| c: &char | c.is_digit(10)),
///     "a whole decimal number"
///     )
///   ).map(| digits | digits.iter().collect::<String>().parse().unwrap())
/// }
/// ```
/// The above uses `any_char` coupled with `pred` to parse a whole decimal number.
/// See [whole_decimal](fn.whole_decimal.html) for more details.
pub fn any_char<'a, S: Clone + 'a>() -> impl Parser<'a, char, S> {
  |input: &'a str, location: Location, state| match input.chars().next() {
    Some(character) => ParseResult::Ok {
      input: &input[character.len_utf8()..],
      output: character,
      location: increment_col(character.len_utf8(), location),
      state,
    },
    _ => ParseResult::Err {
      message: "I'm expecting any character but reached the end of input.".to_string(),
      from: location,
      to: location,
      state,
    },
  }
}

fn pred<'a, P, F, A: std::fmt::Display, S: Clone + 'a>(parser: P, predicate: &'a F, expecting: &'a str) -> impl Parser<'a, A, S>
where
  P: Parser<'a, A, S>,
  F: Fn(&A) -> bool,
{
  move |input, location, state: S| match parser.parse(input, location, state.clone()) {
    ParseResult::Ok {
      input: next_input,
      output: content,
      location: next_location,
      state: next_state,
    } => if predicate(&content) {
      ParseResult::Ok {
        input: next_input,
        output: content,
        location: next_location,
        state: next_state,
      }
    } else {
      ParseResult::Err {
        message: format!(
          "I'm expecting {} but found {}.",
          expecting,
          display_token(Some(content)),
        )
        .to_string(),
        from: location,
        to: next_location,
        state: next_state,
        }
    },
    _ => ParseResult::Err {
      message: format!(
        "I'm expecting {} but found {}.",
        expecting,
        display_token(input.chars().next())
      )
      .to_string(),
      from: location,
      to: location,
      state,
    },
  }
}

/// Parse a single space character.
pub fn space_char<'a, S: Clone + 'a>() -> BoxedParser<'a, (), S> {
  any_char().pred(
    &(|c: &char| *c == ' '),
    "a whitespace",
  ).ignore()
}

/// Parse a single newline character.
/// 
/// Handles `\r\n` in Windows and `\n` on other platforms.
pub fn newline_char<'a, S: Clone + 'a>() -> BoxedParser<'a, (), S> {
  BoxedParser::new(
    (move |input, location, state: S| {
      let mut next_input: &str = input;
      let mut next_location: Location = location;
      let mut next_state: S = state.clone();
      let result1 = any_char().pred(
        &(|c: &char| *c == '\r'),
        "a carriage return",
      ).parse(input, location, state);
      match result1 {
        ParseResult::Ok {
          input,
          location,
          state,
          ..
        } => {
          next_input = input;
          next_location = location;
          next_state = state;
        }
        _ => {}
      }
      let result = any_char().pred(
        &(|c: &char| *c == '\n'),
        "a newline",
      ).parse(next_input, next_location, next_state);
      match result {
        ParseResult::Ok {
          input: next_input,
          output,
          location: next_location,
          state: next_state,
        } => ParseResult::Ok {
          input: next_input,
          output: output,
          location: increment_row(1, next_location),
          state: next_state,
        },
        ParseResult::Err {
          message: error_message,
          from,
          to,
          state,
        } => ParseResult::Err {
          message: error_message,
          from,
          to,
          state,
        }
      }
    }).ignore()
  )
}

/// Parsers zero or more newline characters, each with indentations in front.
/// 
/// Indentation can also be `""` (no indentation)
pub fn newline0<'a, S: Clone + 'a>(indent_parser: BoxedParser<'a, (), S>) -> BoxedParser<'a, (), S> {
  zero_or_more(pair(
    indent_parser,
    newline_char(),
  )).ignore()
}

/// Parsers one or more newline characters, each with indentations in front.
/// 
/// Indentation can also be `""` (no indentation)
pub fn newline1<'a, S: Clone + 'a>(indent_parser: BoxedParser<'a, (), S>) -> BoxedParser<'a, (), S> {
  pair(
    newline_char(),
    newline0(indent_parser),
  ).ignore()
}

/// Parse zero or more space characters.
pub fn space0<'a, S: Clone + 'a>() -> BoxedParser<'a, (), S> {
  zero_or_more(space_char()).ignore()
}

/// Parse one or more space characters.
pub fn space1<'a, S: Clone + 'a>() -> BoxedParser<'a, (), S> {
  one_or_more(space_char()).ignore()
}

/// Parse an indentation specified the number of spaces.
pub fn indent<'a, S: Clone + 'a>(number_of_spaces: usize) -> BoxedParser<'a, (), S> {
  repeat(
    number_of_spaces,
    space_char(),
  ).ignore()
  .map_err(move |_| format!("I'm expecting an indentation.\nAll indentations should be {} spaces.", number_of_spaces))
}

/// Parse a given number of indentations specified the number of spaces.
pub fn indents<'a, S: Clone + 'a>(number_of_spaces: usize, number_of_indents: usize) -> BoxedParser<'a, (), S> {
  repeat(
    number_of_indents,
    indent(number_of_spaces),
  ).map_err(move |_| format!("I'm expecting {} indentation{}.\nAll indentations should be {} spaces.",
    number_of_indents,
    plural_suffix(number_of_indents),
    number_of_spaces,
  ))
  .ignore()
}

fn plural_suffix(count: usize) -> &'static str {
  if count > 1 { "s" } else { "" }
}

fn repeat<'a, A, P, S: Clone + 'a>(times: usize, parser: P)
  -> impl Parser<'a, Vec<A>, S>
  where
    P: Parser<'a, A, S>
{
  move |mut input, mut location, mut state: S| {
    let mut result = Vec::new();

    if times == 0 {
      return ParseResult::Ok {
        input,
        location,
        output: result,
        state,
      }
    }

    let mut counter = 0;

    while let ParseResult::Ok {
      input: next_input,
      output: next_item,
      location: next_location,
      state: next_state,
      ..
    } = parser.parse(input, location, state.clone())
    {
      if counter >= times {
        break;
      }
      input = next_input;
      location = next_location;
      state = next_state;
      result.push(next_item);
      counter = counter + 1;
    }

    ParseResult::Ok {
      input: input,
      output: result,
      location: location,
      state: state,
    }
  }
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
pub fn either<'a, A, P: 'a, S: Clone + 'a>(parser1: P, parser2: P)
  -> BoxedParser<'a, A, S>
  where
    P: Parser<'a, A, S>
{
  BoxedParser::new(
    move |input, location, state: S| {
      let result = match parser1.parse(input, location, state.clone()) {
        ok @ ParseResult::Ok {..} => ok,
        ParseResult::Err {..} =>
          parser2.parse(input, location, state)
      };
      result
    }
  )
}

/// Optionally parse something. Returns supplied default value if parse failed.
pub fn optional<'a, A: Clone + 'a, P: 'a, S: Clone + 'a>(default: A, parser: P)
  -> BoxedParser<'a, A, S>
  where
    P: Parser<'a, A, S>
{
  either(
    BoxedParser::new(
      parser
    ),
    BoxedParser::new(
      move |input, location, state|
      ParseResult::Ok {
          input,
          location,
          output: default.clone(),
          state,
        }
      )
  )
}

/// Parse a newline that maybe preceeded by a comment started with `comment_symbol`.
pub fn newline_with_comment<'a, S: Clone + 'a>(comment_symbol: &'static str) -> impl Parser<'a, (), S> {
  either(
    chain!(
      space0(),
      line_comment(comment_symbol)
    ),
    chain!(
      space0(),
      newline_char()
    ),
  ).ignore()
}

/// Parse a line comment started with `comment_symbol`.
pub fn line_comment<'a, S: Clone + 'a>(comment_symbol: &'static str) -> BoxedParser<'a, (), S> {
  chain!(
    token(comment_symbol),
    zero_or_more(any_char().pred(
      &(|c: &char| *c != '\n' && *c != '\r'),
      "any character",
    )),
    newline_char()
  ).ignore()
}

/// Chain several parsers together and parse them in sequence.
/// 
/// Example:
/// ```
/// # #[macro_use] extern crate lip;
/// # use lip::*;
/// # use crate::lip::Parser;
/// assert_eq!(
///   chain!(token("a"), token("b"), token("c")).parse("abc", Location { row: 1, col: 1 }, ()),
///   ParseResult::Ok {
///     input: "",
///     location: Location { row: 1, col: 4 },
///     output: ("a", ("b", "c")),
///     state: (),
///   }
/// );
/// ```
/// The above example parses the letters "a", "b", and "c" in sequence and returns
/// a nested tuple `("a", ("b", "c"))` containing each of the parser outputs.
#[macro_export]
macro_rules! chain {
  ($single_parser:expr) => { $single_parser };
  ($first_parser:expr, $($parsers:expr),+) => {
    $first_parser.and_then(move | output |
      chain!($($parsers),*).map(move | next_output | (output.clone(), next_output) )
    )
  };
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
pub fn int<'a, S: Clone + 'a>() -> impl Parser<'a, usize, S> {
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
pub fn float<'a, S: Clone + 'a>() -> impl Parser<'a, f64, S> {
  let expecting = "a floating point number";
  chain!(
    digits(expecting, false),
    optional(
      "".to_string(),
      right(token("."), digits(expecting, true)).map(|digits| ".".to_owned() + &digits)
    ),
    optional(
      "".to_string(),
      chain!(
        either(token("e"), token("E")),
        optional("", either(token("+"), token("-"))),
        digits(expecting, false)
      ).map(|(_, (sign, exponent))|
        "e".to_string() + sign + &exponent
      )
    )
  ).map(|(whole, (fraction, exponent))|
    (whole + &fraction + &exponent).parse().unwrap()
  )
}

fn digits<'a, S: Clone + 'a>(name: &'a str, allow_leading_zeroes: bool) -> impl Parser<'a, String, S> {
  one_or_more(
    any_char().pred(
    &(| character: &char | character.is_digit(10))
    , name
    )
  ).update(move |input, digits, location, state|
    if !allow_leading_zeroes && digits[0] == '0' && digits.len() > 1 {
      ParseResult::Err {
        message: format!("You can't have leading zeroes in {}.", name),
        from: Location {
          col: location.col - digits.len(),
          ..location
        },
        to: location,
        state,
      }
    } else {
      ParseResult::Ok {
        input,
        output: digits.iter().collect::<String>(),
        location,
        state
      }
    }
  )
}

/// Parse a variable.
/// 
/// If we want to parse a PascalCase variable excluding three reserved words, we can try something like:
/// ```
/// # use lip::*;
/// let reserved = &([ "Func", "Import", "Export" ].iter().cloned().map(| element | element.to_string()).collect());
/// assert_eq!(
///   variable(&(|c| c.is_uppercase()), &(|c| c.is_lowercase()), &(|_| false), reserved, "a PascalCase variable")
///     .parse("Dict", Location { row: 1, col: 1}, ()),
///   ParseResult::Ok {
///     input: "",
///     output: "Dict".to_string(),
///     location: Location { row: 1, col: 5 },
///     state: (),
///   }
/// );
/// ```
/// If we want to parse a snake_case variable, we can try something like:
/// ```
/// # use lip::*;
/// # use std::collections::HashSet;
/// assert_eq!(
///  variable(&(|c| c.is_lowercase()), &(|c| c.is_lowercase() || c.is_digit(10)), &(|c| *c == '_'), &HashSet::new(), "a snake_case variable")
///    .parse("my_variable_1", Location { row: 1, col: 1}, ()),
///  ParseResult::Ok {
///    input: "",
///    output: "my_variable_1".to_string(),
///    location: Location { row: 1, col: 14 },
///    state: (),
///  }
///);
/// ```
/// The below uses the same snake_case variable parser. However, the separator `_` appeared at the end of the name `invalid_variable_name_`:
/// ```
/// # use lip::*;
/// # use std::collections::HashSet;
/// assert_eq!(
///  variable(&(|c| c.is_lowercase()), &(|c| c.is_lowercase() || c.is_digit(10)), &(|c| *c == '_'), &HashSet::new(), "a snake_case variable")
///    .parse("invalid_variable_name_", Location { row: 1, col: 1}, ()),
///  ParseResult::Err {
///    message: "I'm expecting a snake_case variable but found `invalid_variable_name_` ended with the separator `_`.".to_string(),
///    from: Location { row: 1, col: 1 },
///    to: Location { row: 1, col: 23 },
///    state: (),
///  }
///);
/// ```
pub fn variable<'a, S: Clone + 'a, F1: 'a, F2: 'a, F3: 'a>(start: &'a F1, inner: &'a F2, separator: &'a F3, reserved: &'a HashSet<String>, expecting: &'a str) -> impl Parser<'a, String, S>
  where
    F1: Fn(&char) -> bool,
    F2: Fn(&char) -> bool,
    F3: Fn(&char) -> bool,
{
  chain!(
    any_char().pred(start, expecting),
    zero_or_more(one_of!(
      any_char().pred(separator, expecting),
      any_char().pred(inner, expecting)
    ))
  ).update(move |input, (start_char, mut inner_chars), location, state| {
    inner_chars.insert(0, start_char);
    let name = inner_chars.iter().collect::<String>();
    if reserved.contains(&name) {
      ParseResult::Err {
        message: format!("I'm expecting {} but found a reserved word `{}`.", expecting, name),
        from: Location {
          col: location.col - name.len(),
          ..location
        },
        to: location,
        state,
      }
    } else {
      if name.chars().zip(name[1..].chars()).any(|(c, next_c)| separator(&c) && separator(&next_c)) {
        ParseResult::Err {
          message: format!("I'm expecting {} but found `{}` with duplicated separators.", expecting, name),
          from: Location {
            col: location.col - name.len(),
            ..location
          },
          to: location,
          state,
        }
      } else if separator(&name.chars().last().unwrap()) {
        ParseResult::Err {
          message: format!("I'm expecting {} but found `{}` ended with the separator `{}`.", expecting, name, &name.chars().last().unwrap()),
          from: Location {
            col: location.col - name.len(),
            ..location
          },
          to: location,
          state,
        }
      } else {
        ParseResult::Ok {
          input, location, output: name.clone(), state,
        }  
      }
    }
  })
}

#[derive(Clone)]
enum Trailing {
  Forbidden,
  Optional,
  Mandatory,
}

#[derive(Clone)]
struct SequenceArgs<'a, A: 'a, S: 'a> {
  start: &'static str,
  separator: &'static str,
  end: &'static str,
  spaces: BoxedParser<'a, (), S>,
  item: BoxedParser<'a, A, S>,
  trailing: Trailing,
}

fn sequence<'a, A: Clone + 'a, S: Clone + 'a>(args: &'a SequenceArgs<'a, A, S>) -> BoxedParser<'a, Vec<A>, S> {
  chain!(
    token(args.start),
    args.spaces.clone(),
    optional(
      vec![],
      chain!(
        args.item.clone(),
        zero_or_more(right(wrap(args.spaces.clone(), token(args.separator), args.spaces.clone()), args.item.clone()))
      ).map(move |(first_item, mut rest_items)| {
        rest_items.insert(0, first_item);
        rest_items
      })
    ),
    match args.trailing {
      Trailing::Forbidden =>
        token(""),
      Trailing::Optional =>
        optional("", token(args.end)),
      Trailing::Mandatory =>
        token(args.end)
    }
  ).map(|(_, (_, (items, _)))|
    items
  )
}

/// Wrap a parser with two other delimiter parsers
/// 
/// Example:
/// Parsing a double-quoted string.
/// ```
/// # use lip::*;
/// assert_eq!(
///  succeed(wrap(token("\""), one_or_more(any_char().pred(&(|c: &char| *c != '"'), "string")).map(|chars| chars.iter().collect::<String>()), token("\"")), "\"I, have 1 string here\""),
///  "I, have 1 string here",
/// );
/// ```
pub fn wrap<'a, A: 'a, B: 'a, C: 'a, S: Clone + 'a, P1: 'a, P2: 'a, P3: 'a>(left_delimiter: P1, wrapped: P2, right_delimiter: P3) -> BoxedParser<'a, B, S>
where
  P1: Parser<'a, A, S>,
  P2: Parser<'a, B, S>,
  P3: Parser<'a, C, S>,
{
  right(
    left_delimiter,
    left(
      wrapped,
      right_delimiter,
    ),
  )
}

/// Record the beginning and ending location of the thing being parsed.
/// 
/// You can surround any parser with `located` and remember the location
/// of the parsed output for later error messaging or text processing.
pub fn located<'a, P: 'a, A, S: Clone + 'a>(parser: P) -> impl Parser<'a, Located<A>, S>
  where
    P: Parser<'a, A, S>
{
  move |input, location, state|
  match parser.parse(input, location, state) {
    ParseResult::Ok {
      input: next_input,
      output,
      location: next_location,
      state: next_state,
    } => ParseResult::Ok {
        input: next_input,
        output: Located {
          value: output,
          from: Location {
            row: location.row,
            col: location.col,
          },
          to: Location {
            row: next_location.row,
            col: next_location.col,
          },
        },
        location: next_location,
        state: next_state,
      },
    ParseResult::Err {
      message: error_message,
      from,
      to,
      state,
    } =>
      ParseResult::Err {
        message: error_message,
        from,
        to,
        state,
      }
  }
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
  let error_line = row.to_string() + "| " + source.split("\n").collect::<Vec<&str>>()[row - 1];
  let error_pointer = " ".repeat(col - 1 + row.to_string().len() + 2) + &"^".repeat(error_length);
  let error_report =
    error_line + "\n" + &error_pointer + "\n" + "⚠️ " + &error_message;
  error_report
}

fn update_state<'a, P, A: Clone, S: Clone + 'a, F>(parser: P, f: F) -> impl Parser<'a, A, S>
  where
    P: Parser<'a, A, S>,
    F: Fn(A, S) -> S
{
  move |input, location, state| {
    match parser.parse(input, location, state) {
      ParseResult::Ok {
        input: next_input,
        location: next_location,
        state: next_state,
        output,
      } =>
        ParseResult::Ok {
          input: next_input,
          output: output.clone(),
          location: next_location,
          state: f(output, next_state),
        },
      ParseResult::Err {
        message,
        from,
        to,
        state,
      } =>
        ParseResult::Err {
          message,
          from,
          to,
          state,
        }
    }
  }
}

fn update<'a, P, A: Clone, B: Clone, S: Clone + 'a, F>(parser: P, f: F) -> impl Parser<'a, B, S>
  where
    P: Parser<'a, A, S>,
    F: Fn(&'a str, A, Location, S) -> ParseResult<'a, B, S>
{
  move |input, location, state| {
    match parser.parse(input, location, state) {
      ParseResult::Ok {
        input: next_input,
        location: next_location,
        state: next_state,
        output,
      } =>
        f(next_input, output, next_location, next_state),
      ParseResult::Err {
        message,
        from,
        to,
        state,
      } =>
        ParseResult::Err {
          message,
          from,
          to,
          state,
        }
    }
  }
}

#[doc(hidden)]
pub fn succeed<'a, P: 'a, A: 'a>(parser: P, source: &'a str) -> A
where
  P: Parser<'a, A, ()>
{
  parser.parse(source, Location { row: 1, col: 1 }, ()).unwrap(source)
}

#[doc(hidden)]
pub fn fail<'a, P: 'a, A: Debug + 'a>(parser: P, source: &'a str) -> ParseResult<'a, A, ()>
where
  P: Parser<'a, A, ()>
{
  parser.parse(source, Location { row: 1, col: 1 }, ()).unwrap_err(source)
}