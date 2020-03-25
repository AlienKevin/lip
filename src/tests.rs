#[cfg(test)]
use super::*;

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
