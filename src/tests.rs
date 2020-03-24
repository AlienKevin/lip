#[cfg(test)]
use super::*;

#[test]
fn test_one_of() {
  assert_eq!(
    one_of!(token("a"), token("b"), token("c")).parse("c", Location { row: 1, col: 1 }, ()),
    ParseResult::ParseOk {
      input: "",
      location: Location { row: 1, col: 2 },
      output: "c",
      state: (),
    }
  );
  assert_eq!(
    one_of!(token("a"), token("b"), token("c")).parse("", Location { row: 1, col: 1 }, ()),
    ParseResult::ParseError {
      message: "I'm expecting a `c` but found nothing.".to_string(),
      from: Location { row: 1, col: 1 },
      to: Location { row: 1, col: 1 },
      state: (),
    }
  );
  assert_eq!(
    one_of!(token("a"), token("b"), token("c")).parse("w", Location { row: 1, col: 1 }, ()),
    ParseResult::ParseError {
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
    ParseResult::ParseOk {
      input: "",
      location: Location { row: 1, col: 4 },
      output: ("a", ("b", "c")),
      state: (),
    }
  );
  assert_eq!(
    chain!(token("a"), token("b"), token("d")).parse("abc", Location { row: 1, col: 1 }, ()),
    ParseResult::ParseError {
      message: "I'm expecting a `d` but found `c`.".to_string(),
      from: Location { row: 1, col: 3 },
      to: Location { row: 1, col: 4 },
      state: (),
    }
  );
}
