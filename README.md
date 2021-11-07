![lip logo](media/lip_logo.png)

# Lip
Lip provides powerful parser combinators for creating reusable and flexible parsers.

# Why Lip?
* Easy to understand - uses intuitive combinators like keep and skip
* Compact - takes less than an hour to learn this library fully
* Flexible and composable parser combinators
* Efficient - minimal backtracking
* Built-in support for precise, located error messages
* Keep track of extra states like line number and instruction index
* Extensible - create your own combinators if needed

```rust
// Parse an (x, y) position pair
use lip::*;
let position = succeed!(|x, y| (x, y))
  .keep(int())
  .skip(token(","))
  .keep(int())
  .run("2,3", ()); // run this parser on string "2,3" without extra states
// when parsing finished, position == (2, 3)
```

# Tutorial
Reading the [parser combinator](https://bodil.lol/parser-combinators/) by Bodil is an excellent way to know how parser combinators work.

# License
MIT

# Credits
Based on Bodil's [Parser Combinator Tutorial](https://bodil.lol/parser-combinators/) and Evan's [elm/paser](https://github.com/elm/parser).