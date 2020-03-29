#[cfg(test)]
use super::*;
use super::Parser;
use super::Location;
use super::ParseResult;
use super::Trailing;
use std::fmt::Debug;

#[test]
fn test_one_of() {
  succeed(one_of!(token("a"), token("b"), token("c")), "c", "c");
  fail(one_of!(token("a"), token("b"), token("c")), "", "I'm expecting a `c` but found nothing.");
  fail(one_of!(token("a"), token("b"), token("c")), "w", "I'm expecting a `c` but found `w`.");
}

#[test]
fn test_chain() {
  succeed(chain!(token("a"), token("b"), token("c")), "abc", ("a", ("b", "c")));
  fail(chain!(token("a"), token("b"), token("d")), "abc", "I'm expecting a `d` but found `c`.");
}

#[test]
fn test_update() {
  #[derive(Debug, Clone, PartialEq)]
  struct Counter {
    count: usize,
  }
  assert_eq!(
    token("a").update(| input, output, location, state: Counter |
      ParseResult::Ok {
        input,
        output: format!("{}b", output),
        location,
        state: Counter { count: state.count + 1 },
        bound: true,
      }
    ).parse("a", Location { row: 1, col: 1 }, Counter { count: 0 }),
    ParseResult::Ok {
      input: "",
      location: Location { row: 1, col: 2 },
      output: "ab".to_string(),
      state: Counter { count : 1 },
      bound: true,
    }
  );
  let counted_parser = token("a").update(| input, output, location, state: Counter |
    if state.count > 10 {
      ParseResult::Err {
        message: "Too many things (more than 10)!".to_string(),
        from: Location {
          col: location.col - 1,
          ..location
        },
        to: location,
        state,
        bound: false,
      }
    } else {
      ParseResult::Ok {
        input,
        output: format!("{}a", output),
        location,
        state: Counter { count: state.count + 1 },
        bound: true,
      }
    }
  );
  assert_eq!(
    counted_parser.parse("a", Location { row: 1, col: 1 }, Counter { count: 0 }),
    ParseResult::Ok {
      input: "",
      location: Location { row: 1, col: 2 },
      output: "aa".to_string(),
      state: Counter { count : 1 },
      bound: true,
    }
  );
  assert_eq!(
    counted_parser.parse("a", Location { row: 1, col: 1 }, Counter { count: 11 }),
    ParseResult::Err {
      message: "Too many things (more than 10)!".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 2 },
      state: Counter { count : 11 },
      bound: false,
    }
  );
}

#[test]
fn test_token() {
  succeed(token(""), "aweiow", "");
}

#[test]
fn test_variable() {
  let reserved = &([ "Func", "Import", "Export" ].iter().cloned().map(| element | element.to_string()).collect());
  succeed(variable(&(|c| c.is_uppercase()), &(|c| c.is_lowercase()), &(|_| false), reserved, "a capitalized name"),
    "Dict", "Dict".to_string());
  fail(variable(&(|c| c.is_uppercase()), &(|c| c.is_lowercase()), &(|_| false), reserved, "a capitalized name"),
    "dict", "I'm expecting a capitalized name but found `d`.");
  fail(variable(&(|c| c.is_uppercase()), &(|c| c.is_lowercase()), &(|_| false), reserved, "a capitalized name"),
    "Export", "I'm expecting a capitalized name but found a reserved word `Export`.");
  succeed(variable(&(|c| c.is_uppercase()), &(|c| c.is_alphanumeric()), &(|c| *c == '.' || *c == '$'), reserved, "a variable name"),
    "Main.Local$frame3", "Main.Local$frame3".to_string());
  fail(variable(&(|c| c.is_uppercase()), &(|c| c.is_alphanumeric()), &(|c| *c == '.' || *c == '$'), reserved, "a variable name"),
    "Main.Local$$frame3", "I'm expecting a variable name but found `Main.Local$$frame3` with duplicated separators.");
  fail(variable(&(|c| c.is_uppercase()), &(|c| c.is_alphanumeric()), &(|c| *c == '.' || *c == '$'), reserved, "a variable name"),
    "Main.Local$frame3$", "I'm expecting a variable name but found `Main.Local$frame3$` ended with the separator `$`.");
}

#[test]
fn test_end() {
  succeed(token("abc").end(), "abc", "abc");
  fail(token("abc").end(), "abcd", "I'm expecting the end of input.");
} 

#[test]
fn test_one_or_more() {
  succeed(one_or_more(token("a")), "a", vec!["a"]);
  succeed(one_or_more(token("a")), "aaaa", vec!["a", "a", "a", "a"]);
  fail(one_or_more(token("a")), "bbc", "I'm expecting a `a` but found `b`.");
}

#[test]
fn test_int() {
  succeed(int(), "2000892303900", 2000892303900);
  succeed(int(), "0", 0);
  fail(int(), "01", "You can't have leading zeroes in an integer.");
  fail(int(), "0010", "You can't have leading zeroes in an integer.");
}

#[test]
fn test_float() {
  succeed(float(), "123", 123_f64);
  succeed(float(), "3.1415", 3.1415_f64);
  succeed(float(), "0.1234", 0.1234_f64);
  succeed(float(), "1e-42", 1e-42_f64);
  succeed(float(), "6.022e23", 6.022e23_f64);
  succeed(float(), "6.022E+23", 6.022E+23_f64);
  succeed(float(), "6.022e-23", 6.022E-23_f64);
  fail(float(), ".023", "I'm expecting a floating point number but found `.`.");
  fail(float(), "023.99", "You can't have leading zeroes in a floating point number.");
  fail(float(), "r33", "I'm expecting a floating point number but found `r`.");
  fail(float(), "-33", "I'm expecting a floating point number but found `-`.");
}

#[test]
fn test_wrap() {
  succeed(wrap(token("\""), take_chomped(chomp_while0(|c: &char| *c != '"', "string")), token("\"")), "\"I, have 1 string here\"",
    "I, have 1 string here".to_string());
  fail(wrap(token("\""), take_chomped(chomp_while0(|c: &char| *c != '"', "string")), token("\"")), "\"I, have 1 string here",
    "I'm expecting a `\"` but found nothing.");
}

#[test]
fn test_sequence() {
  succeed(sequence(
    "[",
    token("abc"),
    ",",
    space0(),
    "]",
    Trailing::Optional), "[ abc , abc , abc ]", vec!["abc", "abc", "abc"]);
  succeed(sequence(
    "[",
    token("abc"),
    ",",
    space0(),
    "]",
    Trailing::Optional), "[ abc , abc  , abc , ]", vec!["abc", "abc", "abc"]);
  fail(sequence(
    "[",
    token("abc"),
    ",",
    space0(),
    "]",
    Trailing::Forbidden), "[ abc , abc  , abc  , ]", "I\'m expecting a `]` but found `,`.");
  succeed(sequence(
    "[",
    token("abc"),
    ",",
    space0(),
    "]",
    Trailing::Mandatory), "[ abc, abc , abc  ,  ]", vec!["abc", "abc", "abc"]);
  fail(sequence(
    "[",
    token("abc"),
    ",",
    space0(),
    "]",
    Trailing::Mandatory), "[abc, abc  , abc ]", "I\'m expecting a `,` but found `]`.");
  succeed(sequence(
    "[",
    token("abc"),
    ",",
    space1(),
    "]",
    Trailing::Mandatory), "[ abc , abc  , abc , ]", vec!["abc", "abc", "abc"]);
  succeed(sequence(
    "[",
    token("abc"),
    ",",
    zero_or_more(chomp_if(|c: &char| *c == ' ' || *c == '\n' || *c == '\r', "space")).ignore(),
    "]",
    Trailing::Optional),
"[
  abc,
  abc,
  abc,
]", vec!["abc", "abc", "abc"]);
  succeed(sequence(
    "[",
    token("abc"),
    ",",
    zero_or_more(chomp_if(|c: &char| *c == ' ' || *c == '\n' || *c == '\r', "space")).ignore(),
    "]",
    Trailing::Forbidden),
"[
abc,
abc,
abc
]", vec!["abc", "abc", "abc"]);
}