use criterion::{black_box, criterion_group, criterion_main, Bencher, Criterion};

#[macro_use]
extern crate partial_application;

use lip::Trailing;
use lip::*;
use std::collections::HashMap;
use std::convert::identity;

/// Mostly conformant to JSON spec defined at https://www.json.org/json-en.html

type Object = HashMap<String, Value>;

type Array = Vec<Value>;

#[derive(Debug, Clone, PartialEq)]
enum Value {
    VString(String),
    VNumber(f64),
    VObject(Object),
    VArray(Array),
    VBool(bool),
    VNull,
}

fn object<'a>() -> BoxedParser<'a, Object, ()> {
    // println!("object");
    sequence(
        "{",
        succeed!(|key, value| (key, value))
            .skip(whitespace())
            .keep(string())
            .skip(whitespace())
            .skip(token(":"))
            .keep(value()),
        ",",
        whitespace(),
        "}",
        Trailing::Forbidden,
    )
    .map(|pairs| pairs.iter().cloned().collect())
}

fn array<'a>() -> BoxedParser<'a, Array, ()> {
    // println!("array");
    sequence("[", value(), ",", whitespace(), "]", Trailing::Forbidden)
}

fn value<'a>() -> BoxedParser<'a, Value, ()> {
    // println!("value");
    BoxedParser::new(move |input, location, state| value_helper().parse(input, location, state))
}

fn value_helper<'a>() -> BoxedParser<'a, Value, ()> {
    // println!("value_helper");
    use Value::*;
    succeed!(identity)
        .skip(whitespace())
        .keep(one_of!(
            string().map(VString),
            object().map(VObject),
            array().map(VArray),
            token("true").map(|_| VBool(true)),
            token("false").map(|_| VBool(false)),
            token("null").map(|_| VNull),
            number().map(VNumber)
        ))
        .skip(whitespace())
}

fn string<'a>() -> BoxedParser<'a, String, ()> {
    // println!("string");
    succeed!(|cs: Vec<char>| cs.into_iter().collect())
        .skip(token("\""))
        .keep(zero_or_more_until(
            "a character",
            one_of!(
                succeed!(|cs: String| cs.chars().next().unwrap()).keep(take_chomped(chomp_ifc(
                    is_non_escape,
                    "Any Unicode characters except \" or \\ or control characters",
                ))),
                succeed!(identity).skip(token("\\")).keep(one_of!(
                    token("\"").map(|_| '\"'),
                    token("\\").map(|_| '\\'),
                    token("/").map(|_| '/'),
                    token("b").map(|_| '\u{0008}'),
                    token("f").map(|_| '\u{000C}'),
                    token("n").map(|_| '\n'),
                    token("r").map(|_| '\r'),
                    token("t").map(|_| '\t'),
                    succeed!(|digits: Vec<char>| {
                        let c: String = digits.iter().collect();
                        char::from_u32(u32::from_str_radix(&c, 16).unwrap()).unwrap()
                    })
                    .skip(token("u"))
                    .keep(repeat(4, hex_digit()))
                ))
            ),
            "a closing `\"`",
            token("\""),
        ))
        .skip(token("\""))
}

fn hex_digit<'a>() -> BoxedParser<'a, char, ()> {
    succeed!(|cs: String| cs.chars().next().unwrap()).keep(take_chomped(chomp_ifc(
        |c| match *c {
            '0'..='9' | 'a'..='z' | 'A'..='Z' => true,
            _ => false,
        },
        "a hex digit from 0 to F",
    )))
}

fn number<'a>() -> BoxedParser<'a, f64, ()> {
    // println!("number");
    succeed!(|sign: Option<_>, n: f64| if sign.is_some() { -n } else { n })
        .keep(optional(token("-")))
        .keep(float())
}

fn whitespace<'a>() -> BoxedParser<'a, (), ()> {
    // println!("whitespace");
    succeed!(|_| ()).keep(zero_or_more(one_of!(
        chomp_ifc(|c| *c == '\x20', "a space"),
        chomp_ifc(|c| *c == '\t', "a horizontal tab"),
        chomp_ifc(|c| *c == '\n', "a newline"),
        chomp_ifc(|c| *c == '\r', "a carriage return")
    )))
}

fn is_non_escape(c: &char) -> bool {
    match *c {
        '\x00'..='\x1F' | '\\' | '\"' => false,
        _ => true,
    }
}

fn bench_json(data: &str, bencher: &mut Bencher<'_>) {
    let parser = value();
    match parser.run(data, ()) {
        ParseResult::Ok { .. } => (),
        ParseResult::Err {
            message, from, to, ..
        } => {
            println!("{}", display_error(data, message, from, to));
            panic!();
        }
    }
    bencher.iter(|| {
        let result = parser.run(data, ());
        black_box(result)
    });
}

fn bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("json");
    group.sample_size(10);
    group.bench_function("data", partial!(bench_json => include_str!("data.json"), _));
    group.bench_function(
        "twitter",
        partial!(bench_json => include_str!("twitter.json"), _),
    );
}

criterion_group!(json, bench);
criterion_main!(json);
