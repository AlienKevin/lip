use super::*;
use std::convert::identity;

#[test]
fn test_one_of() {
    assert_succeed(one_of!(token("a"), token("b"), token("c")), "c", "c");
    assert_succeed(
        one_of!(
            succeed!(|_a, _b| "a")
                .keep(optional(token("a")))
                .keep(token("x")),
            token("b")
        ),
        "b",
        "b",
    );
    assert_fail(
        one_of!(token("a"), token("b"), token("c")),
        "",
        "I'm expecting a `c` but found nothing.",
    );
    assert_fail(
        one_of!(token("a"), token("b"), token("c")),
        "w",
        "I'm expecting a `c` but found `w`.",
    );
}

#[test]
fn test_update() {
    #[derive(Debug, Clone, PartialEq)]
    struct Counter {
        count: usize,
    }
    assert_eq!(
        token("a")
            .update(|input, output, location, state: Counter| ParseResult::Ok {
                input,
                output: format!("{}b", output),
                location,
                state: Counter {
                    count: state.count + 1
                },
                committed: true,
            })
            .parse("a", Location { row: 1, col: 1 }, Counter { count: 0 }),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 2 },
            output: "ab".to_string(),
            state: Counter { count: 1 },
            committed: true,
        }
    );
    let mut counted_parser = token("a").update(|input, output, location, state: Counter| {
        if state.count > 10 {
            ParseResult::Err {
                message: "Too many things (more than 10)!".to_string(),
                from: Location {
                    col: location.col - 1,
                    ..location
                },
                to: location,
                state,
                committed: false,
            }
        } else {
            ParseResult::Ok {
                input,
                output: format!("{}a", output),
                location,
                state: Counter {
                    count: state.count + 1,
                },
                committed: true,
            }
        }
    });
    assert_eq!(
        counted_parser.parse("a", Location { row: 1, col: 1 }, Counter { count: 0 }),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 2 },
            output: "aa".to_string(),
            state: Counter { count: 1 },
            committed: true,
        }
    );
    assert_eq!(
        counted_parser.parse("a", Location { row: 1, col: 1 }, Counter { count: 11 }),
        ParseResult::Err {
            message: "Too many things (more than 10)!".to_string(),
            from: Location { row: 1, col: 1 },
            to: Location { row: 1, col: 2 },
            state: Counter { count: 11 },
            committed: false,
        }
    );
}

#[test]
fn test_token() {
    assert_succeed(token(""), "abc", "");
    assert_succeed(token("a"), "abc", "a");
    assert_succeed(token("ab"), "abc", "ab");
    assert_succeed(token("abc"), "abc", "abc");

    // Normalization Form C (NFC) Characters are decomposed and then re-composed by canonical equivalence
    assert_succeed(token("ãáç"), "ãáç", "ãáç");
    // Normalization Form D (NFD) Characters are decomposed by canonical equivalence
    assert_succeed(token("ãáç"), "ãáç", "ãáç");

    // Normalization Form C (NFC) Characters are decomposed and then re-composed by canonical equivalence
    assert_fail(token("ãáç"), "ãá", "I'm expecting a `ãáç` but found `ãá`.");
    // Normalization Form D (NFD) Characters are decomposed by canonical equivalence
    assert_fail(token("ãáç"), "ãá", "I'm expecting a `ãáç` but found `ãá`.");

    // Normalization Form C (NFC) Characters are decomposed and then re-composed by canonical equivalence
    assert_fail(
        token("ãáç"),
        "ãá\nabc",
        "I'm expecting a `ãáç` but found `ãá\\n`.",
    );
    // Normalization Form D (NFD) Characters are decomposed by canonical equivalence
    assert_fail(
        token("ãáç"),
        "ãá\nabc",
        "I'm expecting a `ãáç` but found `ãá\\n`.",
    );

    assert_succeed(
        token("👩‍🔬👩🏿‍💻我哋👨‍👨‍👧‍👧呢一餐"),
        "👩‍🔬👩🏿‍💻我哋👨‍👨‍👧‍👧呢一餐",
        "👩‍🔬👩🏿‍💻我哋👨‍👨‍👧‍👧呢一餐",
    );
    assert_succeed(
        token("👩‍🔬👩🏿‍💻"),
        "👩‍🔬👩🏿‍💻我哋👨‍👨‍👧‍👧呢一餐",
        "👩‍🔬👩🏿‍💻",
    );

    assert_fail(
        token("👩‍🔬👩🏿‍💻我哋👨‍👨‍👧‍👧呢一餐"),
        "👩‍🔬👩🏿‍💻我哋👨‍👨‍👧‍👧呢",
        "I'm expecting a `👩‍🔬👩🏿‍💻我哋👨‍👨‍👧‍👧呢一餐` but found `👩‍🔬👩🏿‍💻我哋👨‍👨‍👧‍👧呢`.",
    );
}

#[test]
fn test_variable() {
    let reserved = &(["Func", "Import", "Export"]
        .iter()
        .cloned()
        .map(|element| element.to_string())
        .collect());
    assert_succeed(
        variable(
            &(|c| c.is_uppercase()),
            &(|c| c.is_lowercase()),
            &(|_| false),
            reserved,
            "a capitalized name",
        ),
        "Dict",
        "Dict".to_string(),
    );
    assert_fail(
        variable(
            &(|c| c.is_uppercase()),
            &(|c| c.is_lowercase()),
            &(|_| false),
            reserved,
            "a capitalized name",
        ),
        "dict",
        "I'm expecting a capitalized name but found `d`.",
    );
    assert_fail(
        variable(
            &(|c| c.is_uppercase()),
            &(|c| c.is_lowercase()),
            &(|_| false),
            reserved,
            "a capitalized name",
        ),
        "Export",
        "I'm expecting a capitalized name but found a reserved word `Export`.",
    );
    assert_succeed(
        variable(
            &(|c| c.is_uppercase()),
            &(|c| c.is_alphanumeric()),
            &(|c| c == '.' || c == '$'),
            reserved,
            "a variable name",
        ),
        "Main.Local$frame3",
        "Main.Local$frame3".to_string(),
    );
    assert_fail(
        variable(
            &(|c| c.is_uppercase()),
            &(|c| c.is_alphanumeric()),
            &(|c| c == '.' || c == '$'),
            reserved,
            "a variable name",
        ),
        "Main.Local$$frame3",
        "I'm expecting a variable name but found `Main.Local$$frame3` with duplicated separators.",
    );
    assert_fail(variable(&(|c| c.is_uppercase()), &(|c| c.is_alphanumeric()), &(|c| c == '.' || c == '$'), reserved, "a variable name"),
    "Main.Local$frame3$", "I'm expecting a variable name but found `Main.Local$frame3$` ended with the separator `$`.");
}

#[test]
fn test_end() {
    assert_succeed(token("abc").end(), "abc", "abc");
    assert_fail(
        token("abc").end(),
        "abcd",
        "I'm expecting the end of input.",
    );
}

#[test]
fn test_one_or_more() {
    assert_succeed(one_or_more(token("a")), "a", vec!["a"]);
    assert_succeed(one_or_more(token("a")), "aaaa", vec!["a", "a", "a", "a"]);
    assert_fail(
        one_or_more(token("a")),
        "bbc",
        "I'm expecting a `a` but found `b`.",
    );

    assert_succeed(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more(token("a")))
                .skip(token("b")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        vec!["a", "a"],
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more(token("a")))
                .skip(token("b")),
            token("aab").map(|s| vec![s])
        )),
        "b",
        "I'm expecting a `aab` but found `b`.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more(token("aa")))
                .skip(token("!")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting a `!` but found `b`.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more(
                    succeed!(identity).keep(token("aa")).skip(token("!"))
                ))
                .skip(token("?")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting a `!` but found `b`.",
    );
    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more(
                    succeed!(identity).keep(token("aa")).skip(token("!"))
                ))
                .skip(token("?")),
            token("aab").map(|s| vec![s])
        )),
        "aa!aab",
        "I'm expecting a `!` but found `b`.",
    );
}

#[test]
fn test_int() {
    assert_succeed(int(), "2000892303900", 2000892303900);
    assert_succeed(int(), "0", 0);
    assert_fail(int(), "01", "You can't have leading zeroes in an integer.");
    assert_fail(
        int(),
        "0010",
        "You can't have leading zeroes in an integer.",
    );
}

#[test]
fn test_float() {
    assert_succeed(float(), "123", 123_f64);
    assert_succeed(float(), "3.1415", 3.1415_f64);
    assert_succeed(float(), "0.1234", 0.1234_f64);
    assert_succeed(float(), "1e-42", 1e-42_f64);
    assert_succeed(float(), "6.022e23", 6.022e23_f64);
    assert_succeed(float(), "6.022E+23", 6.022E+23_f64);
    assert_succeed(float(), "6.022e-23", 6.022E-23_f64);
    assert_fail(
        float(),
        ".023",
        "I'm expecting a floating point number but found `.`.",
    );
    assert_fail(
        float(),
        "023.99",
        "You can't have leading zeroes in a floating point number.",
    );
    assert_fail(
        float(),
        "r33",
        "I'm expecting a floating point number but found `r`.",
    );
    assert_fail(
        float(),
        "-33",
        "I'm expecting a floating point number but found `-`.",
    );
}

#[test]
fn test_wrap() {
    assert_succeed(
        wrap(
            token("\""),
            take_chomped(chomp_while0c(|c: char| c != '"', "string")),
            token("\""),
        ),
        "\"I, have 1 string here\"",
        "I, have 1 string here".to_string(),
    );
    assert_fail(
        wrap(
            token("\""),
            take_chomped(chomp_while0c(|c: char| c != '"', "string")),
            token("\""),
        ),
        "\"I, have 1 string here",
        "I'm expecting a `\"` but found nothing.",
    );
}

/*
#[test]
fn test_sequence() {
    assert_succeed(
        sequence("[", token("abc"), ",", space0(), "]", Trailing::Optional),
        "[ abc , abc , abc ]",
        vec!["abc", "abc", "abc"],
    );
    assert_succeed(
        sequence("[", token("abc"), ",", space0(), "]", Trailing::Optional),
        "[ abc , abc  , abc , ]",
        vec!["abc", "abc", "abc"],
    );
    assert_fail(
        sequence("[", token("abc"), ",", space0(), "]", Trailing::Forbidden),
        "[ abc , abc  , abc  , ]",
        "I\'m expecting a `]` but found `,`.",
    );
    assert_succeed(
        sequence("[", token("abc"), ",", space0(), "]", Trailing::Mandatory),
        "[ abc, abc , abc  ,  ]",
        vec!["abc", "abc", "abc"],
    );
    assert_fail(
        sequence("[", token("abc"), ",", space0(), "]", Trailing::Mandatory),
        "[abc, abc  , abc ]",
        "I\'m expecting a `,` but found `]`.",
    );
    assert_succeed(
        sequence("[", token("abc"), ",", space1(), "]", Trailing::Mandatory),
        "[ abc , abc  , abc , ]",
        vec!["abc", "abc", "abc"],
    );
    assert_succeed(
        sequence(
            "[",
            token("abc"),
            ",",
            &zero_or_more(chomp_ifc(
                |c: char| c == ' ' || c == '\n' || c == '\r',
                "space",
            ))
            .ignore(),
            "]",
            Trailing::Optional,
        ),
        "[
  abc,
  abc,
  abc,
]",
        vec!["abc", "abc", "abc"],
    );
    assert_succeed(
        sequence(
            "[",
            token("abc"),
            ",",
            &zero_or_more(chomp_ifc(
                |c: char| c == ' ' || c == '\n' || c == '\r',
                "space",
            ))
            .ignore(),
            "]",
            Trailing::Forbidden,
        ),
        "[
abc,
abc,
abc
]",
        vec!["abc", "abc", "abc"],
    );
}
*/

#[test]
fn test_keep() {
    assert_succeed(
        succeed!(|x, y| (x, y))
            .keep(int())
            .skip(token(","))
            .keep(int()),
        "2,3",
        (2, 3),
    );
    assert_succeed(
        succeed!(|x, y| (x, y))
            .keep(int())
            .skip(token(","))
            .keep(int()),
        "2,3",
        (2, 3),
    );
    assert_fail(
        succeed!(|x, y| (x, y))
            .keep(int())
            .skip(token(","))
            .keep(int()),
        "2,",
        "I'm expecting an integer but reached the end of input.",
    );
}

#[test]
fn test_newline_with_comment() {
    assert_succeed(
        succeed!(|_| ())
            .keep(token("abc"))
            .skip(newline_with_comment("//")),
        "abc // some comments here!\n",
        (),
    );
    assert_fail(
        succeed!(|_| ())
            .keep(token("abc"))
            .skip(newline_with_comment("//")),
        "abc // some comments here!",
        "I'm expecting a newline but reached the end of input.",
    );
    assert_fail(
        succeed!(|_| ())
            .keep(token("abc"))
            .skip(newline_with_comment("//")),
        "abc -- some comments here!",
        "I'm expecting a `//` but found `--`.",
    );
}

#[test]
fn test_optional() {
    assert_succeed(succeed!(identity).keep(optional(token("abc"))), "", None);
    assert_succeed(
        succeed!(identity)
            .skip(token("abc"))
            .keep(optional(token("hello"))),
        "abc",
        None,
    );
    assert_fail(
        succeed!(|sign: Option<_>, n: f64| if let Some(_) = sign { -n } else { n })
            .keep(optional(token("-")))
            .keep(float()),
        "null",
        "I'm expecting a floating point number but found `n`.",
    );
    assert_succeed(
        succeed!(|sign: Option<_>, n: f64| if let Some(_) = sign { -n } else { n })
            .keep(optional(token("-")))
            .keep(float()),
        "-3.2e2",
        -3.2e2,
    );
}

#[test]
fn test_optional_with_default() {
    assert_succeed(
        succeed!(identity).keep(optional_with_default("default", token("abc"))),
        "",
        "default",
    );
    assert_succeed(
        succeed!(identity)
            .skip(token("abc"))
            .keep(optional_with_default("default", token("hello"))),
        "abc",
        "default",
    );
    assert_fail(
        succeed!(|sign: bool, n: f64| if sign { -n } else { n })
            .keep(optional_with_default(false, token("-").map(|_| true)))
            .keep(float()),
        "null",
        "I'm expecting a floating point number but found `n`.",
    );
    assert_succeed(
        succeed!(|sign: bool, n: f64| if sign { -n } else { n })
            .keep(optional_with_default(false, token("-").map(|_| true)))
            .keep(float()),
        "-3.2e2",
        -3.2e2,
    );
}

#[test]
fn test_one_or_more_until() {
    assert_succeed(
        succeed!(identity).keep(one_or_more_until(
            "the letter `a`",
            token("a"),
            "the ending `b`",
            token("b"),
        )),
        "ab",
        vec!["a"],
    );
    assert_succeed(
        succeed!(identity).keep(one_or_more_until(
            "the letter `a`",
            token("a"),
            "the ending `b`",
            token("b"),
        )),
        "aaab",
        vec!["a", "a", "a"],
    );
    assert_fail(
        succeed!(identity).keep(one_or_more_until(
            "the letter `a`",
            token("a"),
            "the ending `b`",
            token("b"),
        )),
        "b",
        "I'm expecting at least one occurrence of the letter `a` but reached the ending `b`.",
    );
    assert_fail(
        succeed!(identity).keep(one_or_more_until(
            "the letter `a`",
            token("a"),
            "the ending `b`",
            token("b"),
        )),
        "aaac",
        "I'm expecting either the letter `a` or the ending `b`. However, neither was found.",
    );
    assert_succeed(
        succeed!(identity).keep(one_or_more_until(
            "the letter `a`",
            token("a"),
            "the ending `b`",
            token("b"),
        )),
        "aaa",
        vec!["a", "a", "a"],
    );

    assert_succeed(
        succeed!(identity).keep(one_or_more_until(
            "the line",
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| c != '\n', "line")))
                .skip(token("\n")),
            "the end symbol",
            token("<end>"),
        )),
        "this is the 1st line
this is the 2nd line

this is the 4th line

<end>",
        vec![
            "this is the 1st line".to_string(),
            "this is the 2nd line".to_string(),
            "".to_string(),
            "this is the 4th line".to_string(),
            "".to_string(),
        ],
    );

    assert_succeed(
        succeed!(identity).keep(one_or_more_until(
            "the line",
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| c != '\n', "line")))
                .skip(token("\n")),
            "the end symbol",
            token("<end>"),
        )),
        "this is the 1st line
this is the 2nd line

this is the 4th line
",
        vec![
            "this is the 1st line".to_string(),
            "this is the 2nd line".to_string(),
            "".to_string(),
            "this is the 4th line".to_string(),
        ],
    );

    assert_fail(
        succeed!(identity).keep(one_or_more_until(
            "the line",
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| c != '\n', "line")))
                .skip(token("\n")),
            "the end symbol",
            token("<end>"),
        )),
        "<end>",
        "I'm expecting at least one occurrence of the line but reached the end symbol.",
    );

    // adapted from test_zero_or_more_until()

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more_until(
                    "a letter `a`",
                    token("a"),
                    "an end symbol",
                    token("^")
                ))
                .skip(token("b")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting either a letter `a` or an end symbol. However, neither was found.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more_until(
                    "a letter `a`",
                    token("a"),
                    "an end symbol",
                    token("^")
                ))
                .skip(token("b")),
            token("aab").map(|s| vec![s])
        )),
        "b",
        "I'm expecting a `aab` but found `b`.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more_until(
                    "an `aa`",
                    token("aa"),
                    "an end symbol",
                    token("^")
                ))
                .skip(token("!")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting either an `aa` or an end symbol. However, neither was found.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more_until(
                    "an `aa!`",
                    succeed!(identity).keep(token("aa")).skip(token("!")),
                    "an end symbol",
                    token("^")
                ))
                .skip(token("?")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting a `!` but found `b`.",
    );

    // committed err when running end_parser
    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more_until(
                    "an `aa`",
                    token("aa"),
                    "an end symbol",
                    succeed!(identity).keep(token("b")).skip(token("!"))
                ))
                .skip(token("?")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting a `!` but found nothing.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(one_or_more_until(
                    "an `aa`",
                    token("aa"),
                    "an end symbol",
                    succeed!(identity).keep(token("b")).skip(token("!"))
                ))
                .skip(token("?")),
            token("aab").map(|s| vec![s])
        )),
        "b",
        "I'm expecting a `!` but found nothing.",
    );
}

#[test]
fn test_zero_or_more() {
    assert_succeed(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(zero_or_more(token("a")))
                .skip(token("b")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        vec!["a", "a"],
    );

    assert_succeed(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(zero_or_more(token("a")))
                .skip(token("b")),
            token("aab").map(|s| vec![s])
        )),
        "b",
        vec![],
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(zero_or_more(token("aa")))
                .skip(token("!")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting a `!` but found `b`.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(zero_or_more(
                    succeed!(identity).keep(token("aa")).skip(token("!"))
                ))
                .skip(token("?")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting a `!` but found `b`.",
    );
}

#[test]
fn test_zero_or_more_until() {
    assert_succeed(
        succeed!(identity).keep(zero_or_more_until(
            "a letter `a`",
            token("a"),
            "an ending `b`",
            token("b"),
        )),
        "ab",
        vec!["a"],
    );
    assert_succeed(
        succeed!(identity).keep(zero_or_more_until(
            "a letter `a`",
            token("a"),
            "an ending `b`",
            token("b"),
        )),
        "aaab",
        vec!["a", "a", "a"],
    );
    assert_succeed(
        succeed!(identity).keep(zero_or_more_until(
            "a letter `a`",
            token("a"),
            "an ending `b`",
            token("b"),
        )),
        "b",
        vec![],
    );
    assert_fail(
        succeed!(identity).keep(zero_or_more_until(
            "a letter `a`",
            token("a"),
            "an ending `b`",
            token("b"),
        )),
        "aaac",
        "I'm expecting either a letter `a` or an ending `b`. However, neither was found.",
    );
    assert_succeed(
        succeed!(identity).keep(zero_or_more_until(
            "a letter `a`",
            token("a"),
            "an ending `b`",
            token("b"),
        )),
        "aaa",
        vec!["a", "a", "a"],
    );
    assert_succeed(
        succeed!(identity).keep(zero_or_more_until(
            "a letter `a`",
            token("a"),
            "an ending `b`",
            token("b"),
        )),
        "",
        vec![],
    );

    assert_succeed(
        succeed!(identity).keep(zero_or_more_until(
            "a line",
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| c != '\n', "line")))
                .skip(token("\n")),
            "an end tag",
            token("<end>"),
        )),
        "this is the 1st line
this is the 2nd line

this is the 4th line

<end>",
        vec![
            "this is the 1st line".to_string(),
            "this is the 2nd line".to_string(),
            "".to_string(),
            "this is the 4th line".to_string(),
            "".to_string(),
        ],
    );

    assert_succeed(
        succeed!(identity).keep(zero_or_more_until(
            "a line",
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| c != '\n', "line")))
                .skip(token("\n")),
            "an end tag",
            token("<end>"),
        )),
        "this is the 1st line
this is the 2nd line

this is the 4th line
",
        vec![
            "this is the 1st line".to_string(),
            "this is the 2nd line".to_string(),
            "".to_string(),
            "this is the 4th line".to_string(),
        ],
    );

    assert_succeed(
        succeed!(identity).keep(zero_or_more_until(
            "a line",
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| c != '\n', "line")))
                .skip(token("\n")),
            "an end tag",
            token("<end>"),
        )),
        "<end>",
        vec![],
    );

    // edge case: the language of parser may be a superset of end_parser
    assert_succeed(
        succeed!(identity).keep(zero_or_more_until(
            "a line",
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| c != '\n', "line")))
                .skip(token("\n")),
            "an end tag",
            token("<end>"),
        )),
        "<end>\n",
        vec![],
    );

    // adapted from test_zero_or_more()

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(zero_or_more_until(
                    "a letter `a`",
                    token("a"),
                    "an end symbol",
                    token("^")
                ))
                .skip(token("b")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting either a letter `a` or an end symbol. However, neither was found.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(zero_or_more_until(
                    "a letter `a`",
                    token("a"),
                    "an end symbol",
                    token("^")
                ))
                .skip(token("b")),
            token("aab").map(|s| vec![s])
        )),
        "b",
        "I'm expecting a `aab` but found `b`.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(zero_or_more_until(
                    "an `aa`",
                    token("aa"),
                    "an end symbol",
                    token("^")
                ))
                .skip(token("!")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting either an `aa` or an end symbol. However, neither was found.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(zero_or_more_until(
                    "an `aa!`",
                    succeed!(identity).keep(token("aa")).skip(token("!")),
                    "an end symbol",
                    token("^")
                ))
                .skip(token("?")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting a `!` but found `b`.",
    );

    // committed err when running end_parser
    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(zero_or_more_until(
                    "an `aa`",
                    token("aa"),
                    "an end symbol",
                    succeed!(identity).keep(token("b")).skip(token("!"))
                ))
                .skip(token("?")),
            token("aab").map(|s| vec![s])
        )),
        "aab",
        "I'm expecting a `!` but found nothing.",
    );

    assert_fail(
        succeed!(identity).keep(one_of!(
            succeed!(identity)
                .keep(zero_or_more_until(
                    "an `aa`",
                    token("aa"),
                    "an end symbol",
                    succeed!(identity).keep(token("b")).skip(token("!"))
                ))
                .skip(token("?")),
            token("aab").map(|s| vec![s])
        )),
        "b",
        "I'm expecting a `!` but found nothing.",
    );
}

#[test]
fn test_any_char() {
    assert_eq!(
        any_char("a character").parse("a", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 2 },
            output: 'a',
            state: (),
            committed: false,
        }
    );
    assert_eq!(
        any_char("a character").parse("\n", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 2, col: 1 },
            output: '\n',
            state: (),
            committed: false,
        }
    );
    assert_eq!(
        any_char("a character").parse("혇", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 3 },
            output: '혇',
            state: (),
            committed: false,
        }
    );
    assert_eq!(
        any_char("a character").parse("我", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 3 },
            output: '我',
            state: (),
            committed: false,
        }
    );
    assert_eq!(
        any_char("a character").parse("🤣", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 3 },
            output: '🤣',
            state: (),
            committed: false,
        }
    );
}

#[test]
fn test_any_grapheme() {
    assert_eq!(
        any_grapheme("a grapheme").parse("a", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 2 },
            output: "a",
            state: (),
            committed: false,
        }
    );
    assert_eq!(
        any_grapheme("a grapheme").parse("\n", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 2, col: 1 },
            output: "\n",
            state: (),
            committed: false,
        }
    );
    assert_eq!(
        any_grapheme("a grapheme").parse("\r\n", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 2, col: 1 },
            output: "\r\n",
            state: (),
            committed: false,
        }
    );
    assert_eq!(
        any_grapheme("a grapheme").parse("혇", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 3 },
            output: "혇",
            state: (),
            committed: false,
        }
    );
    assert_eq!(
        any_grapheme("a grapheme").parse("我", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 3 },
            output: "我",
            state: (),
            committed: false,
        }
    );
    assert_eq!(
        any_grapheme("a grapheme").parse("🤣", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 3 },
            output: "🤣",
            state: (),
            committed: false,
        }
    );
    assert_eq!(
        any_grapheme("a grapheme").parse("👩‍🔬", Location { row: 1, col: 1 }, ()),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 3 },
            output: "👩‍🔬",
            state: (),
            committed: false,
        }
    );
}

#[test]
fn test_chomp_if() {
    assert_succeed(
        succeed!(identity).keep(take_chomped(chomp_if(|c| c == "👨‍👩‍👧‍👦", "family emoji"))),
        "👨‍👩‍👧‍👦",
        "👨‍👩‍👧‍👦".to_string(),
    );
    assert_succeed(
        succeed!(identity).keep(take_chomped(chomp_if(|c| c == "혇", "Korean"))),
        "혇",
        "혇".to_string(),
    );
    assert_succeed(
        succeed!(identity).keep(take_chomped(chomp_if(|c| c == "齉", "Chinese"))),
        "齉",
        "齉".to_string(),
    );
    assert_succeed(
        succeed!(identity).keep(take_chomped(chomp_if(|c| c == "ë", "IPA Symbol"))),
        "ë",
        "ë".to_string(),
    );
    assert_fail(
        succeed!(identity).keep(chomp_if(|c| c == "a", "a letter `a`")),
        "",
        "I'm expecting a letter `a` but reached the end of input.",
    );
    assert_fail(
        succeed!(identity).keep(chomp_if(|_| true, "any character")),
        "",
        "I'm expecting any character but reached the end of input.",
    );
}

#[test]
fn test_chomp_ifc() {
    assert_fail(
        succeed!(identity).keep(chomp_ifc(|c| c == 'a', "a letter `a`")),
        "",
        "I'm expecting a letter `a` but reached the end of input.",
    );
    assert_fail(
        succeed!(identity).keep(chomp_ifc(|_| true, "any character")),
        "",
        "I'm expecting any character but reached the end of input.",
    );
}

#[test]
fn test_chomp_while1() {
    assert_succeed(
        succeed!(identity).keep(take_chomped(chomp_while1(|c| c == "我", "character '我'"))),
        "我我我你",
        "我我我".to_string(),
    );
    assert_fail(
        succeed!(identity).keep(take_chomped(chomp_while1(|c| c == "我", "character `我`"))),
        "你",
        "I'm expecting character `我` but found `你`.",
    );
    assert_succeed(
        succeed!(identity).keep(take_chomped(chomp_while1(
            |c| c != "👩‍👩‍👦‍👦",
            "any emoji except the family emoji",
        ))),
        "🥲🥰🏉👩‍👩‍👦‍👦👩",
        "🥲🥰🏉".to_string(),
    );
    assert_fail(
        succeed!(identity).keep(take_chomped(chomp_while1(
            |c| c != "👩‍👩‍👦‍👦",
            "any emoji except the family emoji",
        ))),
        "👩‍👩‍👦‍👦👩",
        "I'm expecting any emoji except the family emoji but found `👩‍👩‍👦‍👦`.",
    );
}

#[test]
fn test_chomp_while0() {
    assert_succeed(
        succeed!(identity).keep(take_chomped(chomp_while0(|c| c == "我", "character '我'"))),
        "我我我你",
        "我我我".to_string(),
    );
    assert_succeed(
        succeed!(identity).keep(take_chomped(chomp_while0(|c| c == "我", "character '我'"))),
        "你",
        "".to_string(),
    );
    assert_succeed(
        succeed!(identity).keep(take_chomped(chomp_while0(
            |c| c != "👩‍👩‍👦‍👦",
            "any emoji except the family emoji",
        ))),
        "🥲🥰🏉👩‍👩‍👦‍👦👩",
        "🥲🥰🏉".to_string(),
    );
    assert_succeed(
        succeed!(identity).keep(take_chomped(chomp_while0(
            |c| c != "👩‍👩‍👦‍👦",
            "any emoji except the family emoji",
        ))),
        "👩‍👩‍👦‍👦👩",
        "".to_string(),
    );
}

#[test]
fn test_digits() {
    assert_succeed(
        digits("a nonnegative int without leading zeroes", false),
        "1028923",
        "1028923".to_string(),
    );
    assert_fail(
        digits("a nonnegative int without leading zeroes", false),
        "a",
        "I'm expecting a nonnegative int without leading zeroes but found `a`.",
    );
}
