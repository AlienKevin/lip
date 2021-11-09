use super::Location;
use super::ParseResult;
use super::Parser;
use super::Trailing;
#[cfg(test)]
use super::*;
use std::fmt::Debug;

#[test]
fn test_one_of() {
    assert_succeed(one_of!(token("a"), token("b"), token("c")), "c", "c");
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
                bound: true,
            })
            .parse("a", Location { row: 1, col: 1 }, Counter { count: 0 }),
        ParseResult::Ok {
            input: "",
            location: Location { row: 1, col: 2 },
            output: "ab".to_string(),
            state: Counter { count: 1 },
            bound: true,
        }
    );
    let counted_parser = token("a").update(|input, output, location, state: Counter| {
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
                state: Counter {
                    count: state.count + 1,
                },
                bound: true,
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
            bound: true,
        }
    );
    assert_eq!(
        counted_parser.parse("a", Location { row: 1, col: 1 }, Counter { count: 11 }),
        ParseResult::Err {
            message: "Too many things (more than 10)!".to_string(),
            from: Location { row: 1, col: 1 },
            to: Location { row: 1, col: 2 },
            state: Counter { count: 11 },
            bound: false,
        }
    );
}

#[test]
fn test_token() {
    assert_succeed(token(""), "aweiow", "");
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
            &(|c| *c == '.' || *c == '$'),
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
            &(|c| *c == '.' || *c == '$'),
            reserved,
            "a variable name",
        ),
        "Main.Local$$frame3",
        "I'm expecting a variable name but found `Main.Local$$frame3` with duplicated separators.",
    );
    assert_fail(variable(&(|c| c.is_uppercase()), &(|c| c.is_alphanumeric()), &(|c| *c == '.' || *c == '$'), reserved, "a variable name"),
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
            take_chomped(chomp_while0c(|c: &char| *c != '"', "string")),
            token("\""),
        ),
        "\"I, have 1 string here\"",
        "I, have 1 string here".to_string(),
    );
    assert_fail(
        wrap(
            token("\""),
            take_chomped(chomp_while0c(|c: &char| *c != '"', "string")),
            token("\""),
        ),
        "\"I, have 1 string here",
        "I'm expecting a `\"` but found nothing.",
    );
}

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
            zero_or_more(chomp_ifc(
                |c: &char| *c == ' ' || *c == '\n' || *c == '\r',
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
            zero_or_more(chomp_ifc(
                |c: &char| *c == ' ' || *c == '\n' || *c == '\r',
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
    assert_succeed(
        succeed!(|a| a).keep(optional("yes", token("abc"))),
        "",
        "yes",
    );
    assert_succeed(
        succeed!(|a| a)
            .skip(token("abc"))
            .keep(optional("yes", token("hello"))),
        "abc",
        "yes",
    );
}

#[test]
fn test_one_or_more_until() {
    assert_succeed(
        succeed!(|list| list).keep(one_or_more_until(token("a"), token("b"))),
        "ab",
        vec!["a"],
    );
    assert_succeed(
        succeed!(|list| list).keep(one_or_more_until(token("a"), token("b"))),
        "aaab",
        vec!["a", "a", "a"],
    );
    assert_fail(
        succeed!(|list| list).keep(one_or_more_until(token("a"), token("b"))),
        "b",
        "I'm expecting at least one occurrence of the intended string but reached the end delimiter."
    );
    assert_fail(
        succeed!(|list| list).keep(one_or_more_until(token("a"), token("b"))),
        "aaac",
        "I'm expecting either the intended string or the end delimiter. However, neither was found.",
    );
    assert_succeed(
        succeed!(|list| list).keep(one_or_more_until(token("a"), token("b"))),
        "aaa",
        vec!["a", "a", "a"],
    );

    assert_succeed(
        succeed!(|list| list).keep(one_or_more_until(
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| *c != '\n', "line")))
                .skip(token("\n")),
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
        succeed!(|list| list).keep(one_or_more_until(
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| *c != '\n', "line")))
                .skip(token("\n")),
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
        succeed!(|list| list).keep(one_or_more_until(
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| *c != '\n', "line")))
                .skip(token("\n")),
            token("<end>"),
        )),
        "<end>",
        "I'm expecting at least one occurrence of the intended string but reached the end delimiter.",
    );
}

#[test]
fn test_zero_or_more_until() {
    assert_succeed(
        succeed!(|list| list).keep(zero_or_more_until(token("a"), token("b"))),
        "ab",
        vec!["a"],
    );
    assert_succeed(
        succeed!(|list| list).keep(zero_or_more_until(token("a"), token("b"))),
        "aaab",
        vec!["a", "a", "a"],
    );
    assert_succeed(
        succeed!(|list| list).keep(zero_or_more_until(token("a"), token("b"))),
        "b",
        vec![],
    );
    assert_fail(
        succeed!(|list| list).keep(zero_or_more_until(token("a"), token("b"))),
        "aaac",
        "I'm expecting either the intended string or the end delimiter. However, neither was found.",
    );
    assert_succeed(
        succeed!(|list| list).keep(zero_or_more_until(token("a"), token("b"))),
        "aaa",
        vec!["a", "a", "a"],
    );
    assert_succeed(
        succeed!(|list| list).keep(zero_or_more_until(token("a"), token("b"))),
        "",
        vec![],
    );

    assert_succeed(
        succeed!(|list| list).keep(zero_or_more_until(
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| *c != '\n', "line")))
                .skip(token("\n")),
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
        succeed!(|list| list).keep(zero_or_more_until(
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| *c != '\n', "line")))
                .skip(token("\n")),
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
        succeed!(|list| list).keep(zero_or_more_until(
            succeed!(|line| line)
                .keep(take_chomped(chomp_while0c(|c| *c != '\n', "line")))
                .skip(token("\n")),
            token("<end>"),
        )),
        "<end>",
        vec![],
    );
}

#[test]
fn test_chomp_if() {
    assert_succeed(
        succeed!(|s| s).keep(take_chomped(chomp_if(|c| c == "👨‍👩‍👧‍👦", "family emoji"))),
        "👨‍👩‍👧‍👦",
        "👨‍👩‍👧‍👦".to_string(),
    );
    assert_succeed(
        succeed!(|s| s).keep(take_chomped(chomp_if(|c| c == "혇", "Korean"))),
        "혇",
        "혇".to_string(),
    );
    assert_succeed(
        succeed!(|s| s).keep(take_chomped(chomp_if(|c| c == "齉", "Chinese"))),
        "齉",
        "齉".to_string(),
    );
    assert_succeed(
        succeed!(|s| s).keep(take_chomped(chomp_if(|c| c == "ë", "IPA Symbol"))),
        "ë",
        "ë".to_string(),
    );
    assert_fail(
        succeed!(|s| s).keep(chomp_if(|c| c == "a", "a letter `a`")),
        "",
        "I'm expecting a letter `a` but reached the end of input.",
    );
    assert_fail(
        succeed!(|s| s).keep(chomp_if(|_| true, "any character")),
        "",
        "I'm expecting any character but reached the end of input.",
    );
}

#[test]
fn test_chomp_ifc() {
    assert_fail(
        succeed!(|s| s).keep(chomp_ifc(|c| *c == 'a', "a letter `a`")),
        "",
        "I'm expecting a letter `a` but reached the end of input.",
    );
    assert_fail(
        succeed!(|s| s).keep(chomp_ifc(|_| true, "any character")),
        "",
        "I'm expecting any character but reached the end of input.",
    );
}

#[test]
fn test_chomp_while1() {
    assert_succeed(
        succeed!(|s| s).keep(take_chomped(chomp_while1(|c| c == "我", "character '我'"))),
        "我我我你",
        "我我我".to_string(),
    );
    assert_fail(
        succeed!(|s| s).keep(take_chomped(chomp_while1(|c| c == "我", "character `我`"))),
        "你",
        "I'm expecting character `我` but found `你`.",
    );
    assert_succeed(
        succeed!(|s| s).keep(take_chomped(chomp_while1(
            |c| c != "👩‍👩‍👦‍👦",
            "any emoji except the family emoji",
        ))),
        "🥲🥰🏉👩‍👩‍👦‍👦👩",
        "🥲🥰🏉".to_string(),
    );
    assert_fail(
        succeed!(|s| s).keep(take_chomped(chomp_while1(
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
        succeed!(|s| s).keep(take_chomped(chomp_while0(|c| c == "我", "character '我'"))),
        "我我我你",
        "我我我".to_string(),
    );
    assert_succeed(
        succeed!(|s| s).keep(take_chomped(chomp_while0(|c| c == "我", "character '我'"))),
        "你",
        "".to_string(),
    );
    assert_succeed(
        succeed!(|s| s).keep(take_chomped(chomp_while0(
            |c| c != "👩‍👩‍👦‍👦",
            "any emoji except the family emoji",
        ))),
        "🥲🥰🏉👩‍👩‍👦‍👦👩",
        "🥲🥰🏉".to_string(),
    );
    assert_succeed(
        succeed!(|s| s).keep(take_chomped(chomp_while0(
            |c| c != "👩‍👩‍👦‍👦",
            "any emoji except the family emoji",
        ))),
        "👩‍👩‍👦‍👦👩",
        "".to_string(),
    );
}
