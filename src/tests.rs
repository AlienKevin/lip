#[cfg(test)]
use super::*;
use super::Parser;
use super::Location;
use super::ParseResult;
use std::fmt::Debug;

#[test]
fn test_one_of() {
  assert_eq!(
    one_of!(token("a"), token("b"), token("c")).parse("c", Location { row: 1, col: 1 }, ()),
    ParseResult::Ok {
      input: "",
      location: Location { row: 1, col: 2 },
      output: "c",
      state: (),
    }
  );
  assert_eq!(
    one_of!(token("a"), token("b"), token("c")).parse("", Location { row: 1, col: 1 }, ()),
    ParseResult::Err {
      message: "I'm expecting a `c` but found nothing.".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 1 },
      state: (),
    }
  );
  assert_eq!(
    one_of!(token("a"), token("b"), token("c")).parse("w", Location { row: 1, col: 1 }, ()),
    ParseResult::Err {
      message: "I'm expecting a `c` but found `w`.".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 2 },
      state: (),
    }
  );
}

#[test]
fn test_chain() {
  assert_eq!(
    chain!(token("a"), token("b"), token("c")).parse("abc", Location { row: 1, col: 1 }, ()),
    ParseResult::Ok {
      input: "",
      location: Location { row: 1, col: 4 },
      output: ("a", ("b", "c")),
      state: (),
    }
  );
  assert_eq!(
    chain!(token("a"), token("b"), token("d")).parse("abc", Location { row: 1, col: 1 }, ()),
    ParseResult::Err {
      message: "I'm expecting a `d` but found `c`.".to_string(),
      from: Location { row: 1, col: 3 },
      to: Location { row: 1, col: 4 },
      state: (),
    }
  );
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
      }
    ).parse("a", Location { row: 1, col: 1 }, Counter { count: 0 }),
    ParseResult::Ok {
      input: "",
      location: Location { row: 1, col: 2 },
      output: "ab".to_string(),
      state: Counter { count : 1 },
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
      }
    } else {
      ParseResult::Ok {
        input,
        output: format!("{}a", output),
        location,
        state: Counter { count: state.count + 1 },
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
    }
  );
  assert_eq!(
    counted_parser.parse("a", Location { row: 1, col: 1 }, Counter { count: 11 }),
    ParseResult::Err {
      message: "Too many things (more than 10)!".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 2 },
      state: Counter { count : 11 },
    }
  );
}

#[test]
fn test_token() {
  assert_eq!(
    token("").parse("aweiow", Location { row: 1, col: 1 }, ()),
    ParseResult::Ok {
      input: "aweiow",
      output: "",
      location: Location { row: 1, col: 1 },
      state: (),
    }
  );
}

#[test]
fn test_variable() {
  let reserved = &([ "Func", "Import", "Export" ].iter().cloned().map(| element | element.to_string()).collect());
  assert_eq!(
    variable(&(|c| c.is_uppercase()), &(|c| c.is_lowercase()), &(|_| false), reserved, "a capitalized name")
      .parse("Dict", Location { row: 1, col: 1}, ()),
    ParseResult::Ok {
      input: "",
      output: "Dict".to_string(),
      location: Location { row: 1, col: 5 },
      state: (),
    }
  );
  assert_eq!(
    variable(&(|c| c.is_uppercase()), &(|c| c.is_lowercase()), &(|_| false), reserved, "a capitalized name")
      .parse("dict", Location { row: 1, col: 1}, ()),
    ParseResult::Err {
      message: "I'm expecting a capitalized name but found `d`.".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 2 },
      state: (),
    }
  );
  assert_eq!(
    variable(&(|c| c.is_uppercase()), &(|c| c.is_lowercase()), &(|_| false), reserved, "a capitalized name")
      .parse("Export", Location { row: 1, col: 1}, ()),
    ParseResult::Err {
      message: "I'm expecting a capitalized name but found a reserved word `Export`.".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 7 },
      state: (),
    }
  );
  assert_eq!(
    variable(&(|c| c.is_uppercase()), &(|c| c.is_alphanumeric()), &(|c| *c == '.' || *c == '$'), reserved, "a variable name")
      .parse("Main.Local$frame3", Location { row: 1, col: 1}, ()),
    ParseResult::Ok {
      input: "",
      output: "Main.Local$frame3".to_string(),
      location: Location { row: 1, col: 18 },
      state: (),
    }
  );
  assert_eq!(
    variable(&(|c| c.is_uppercase()), &(|c| c.is_alphanumeric()), &(|c| *c == '.' || *c == '$'), reserved, "a variable name")
      .parse("Main.Local$$frame3", Location { row: 1, col: 1}, ()),
    ParseResult::Err {
      message: "I'm expecting a variable name but found `Main.Local$$frame3` with duplicated separators.".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 19 },
      state: (),
    }
  );
  assert_eq!(
    variable(&(|c| c.is_uppercase()), &(|c| c.is_alphanumeric()), &(|c| *c == '.' || *c == '$'), reserved, "a variable name")
      .parse("Main.Local$frame3$", Location { row: 1, col: 1}, ()),
    ParseResult::Err {
      message: "I'm expecting a variable name but found `Main.Local$frame3$` ended with the separator `$`.".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 19 },
      state: (),
    }
  );
}

#[test]
fn test_end() {
  assert_eq!(
    token("abc").end().parse("abc", Location { row: 1, col: 1}, ()),
    ParseResult::Ok {
      input: "",
      output: "abc",
      location: Location { row: 1, col: 4 },
      state: (),
    }
  );
  assert_eq!(
    token("abc").end().parse("abcd", Location { row: 1, col: 1}, ()),
    ParseResult::Err {
      message: "I'm expecting the end of input.".to_string(),
      from: Location { row: 1, col: 4 },
      to: Location { row: 1, col: 4 },
      state: (),
    }
  );
}

#[test]
fn test_one_or_more() {
  assert_eq!(
    one_or_more(token("a")).parse("a", Location { row: 1, col: 1 }, ()),
    ParseResult::Ok {
      input: "",
      output: vec!["a"],
      location: Location { row: 1, col: 2 },
      state: (),
    }
  );
  assert_eq!(
    one_or_more(token("a")).parse("aaaa", Location { row: 1, col: 1 }, ()),
    ParseResult::Ok {
      input: "",
      output: vec!["a", "a", "a", "a"],
      location: Location { row: 1, col: 5 },
      state: (),
    }
  );
  assert_eq!(
    one_or_more(token("a")).parse("bbc", Location { row: 1, col: 1 }, ()),
    ParseResult::Err {
      message: "I'm expecting a `a` but found `b`.".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 2 },
      state: (),
    }
  );
}

#[test]
fn test_int() {
  assert_eq!(
    int().parse("2000892303900", Location { row: 1, col: 1 }, ()),
    ParseResult::Ok {
      input: "",
      output: 2000892303900,
      location: Location { row: 1, col: 14 },
      state: (),
    }
  );
  assert_eq!(
    int().parse("0", Location { row: 1, col: 1 }, ()),
    ParseResult::Ok {
      input: "",
      output: 0,
      location: Location { row: 1, col: 2 },
      state: (),
    }
  );
  assert_eq!(
    int().parse("01", Location { row: 1, col: 1 }, ()),
    ParseResult::Err {
      message: "You can't have leading zeroes in an integer.".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 3 },
      state: (),
    }
  );
  assert_eq!(
    int().parse("0010", Location { row: 1, col: 1 }, ()),
    ParseResult::Err {
      message: "You can't have leading zeroes in an integer.".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 5 },
      state: (),
    }
  );
}

#[test]
fn test_float() {
  assert_eq!(success(float(), "123"), 123_f64);
  assert_eq!(success(float(), "3.1415"), 3.1415_f64);
  assert_eq!(success(float(), "0.1234"), 0.1234_f64);
  assert_eq!(success(float(), "1e-42"), 1e-42_f64);
  assert_eq!(success(float(), "6.022e23"), 6.022e23_f64);
  assert_eq!(success(float(), "6.022E+23"), 6.022E+23_f64);
  assert_eq!(success(float(), "6.022e-23"), 6.022E-23_f64);
  assert_eq!(fail(float(), ".023"), ParseResult::Err {
    message: "I'm expecting a floating point number but found `.`.".to_string(),
    from: Location { row: 1, col: 1 },
    to: Location { row: 1, col: 2 },
    state: (),
  });
  assert_eq!(fail(float(), "023.99"), ParseResult::Err {
    message: "You can't have leading zeroes in a floating point number.".to_string(),
    from: Location { row: 1, col: 1 },
    to: Location { row: 1, col: 4 },
    state: (),
  });
  assert_eq!(fail(float(), "r33"), ParseResult::Err {
    message: "I'm expecting a floating point number but found `r`.".to_string(),
    from: Location { row: 1, col: 1 },
    to: Location { row: 1, col: 2 },
    state: (),
  });
  assert_eq!(fail(float(), "-33"), ParseResult::Err {
    message: "I'm expecting a floating point number but found `-`.".to_string(),
    from: Location { row: 1, col: 1 },
    to: Location { row: 1, col: 2 },
    state: (),
  });
}

fn success<'a, P: 'a, A: 'a>(parser: P, source: &'a str) -> A
where
  P: Parser<'a, A, ()>
{
  parser.parse(source, Location { row: 1, col: 1 }, ()).unwrap(source)
}

fn fail<'a, P: 'a, A: Debug + 'a>(parser: P, source: &'a str) -> ParseResult<'a, A, ()>
where
  P: Parser<'a, A, ()>
{
  parser.parse(source, Location { row: 1, col: 1 }, ()).unwrap_err(source)
}