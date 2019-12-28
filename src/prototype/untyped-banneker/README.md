# untyped-banneker

A small Scheme-like language written in Scheme, based on an implementation of the ideas from Chapter 1 of Lectures on the Curry Howard Isomorphism.

## Syntax rules

### let

```mllike
let x = symbol("hello")
let square = fun int_arg -> int_arg * int_arg
let sumsquare x =
    let y = (square x)
    y + y
```

### let ... in

```mllike
let x = symbol("hello")
let square = fun int_arg -> int_arg * int_arg

let sumsquare x =
    let y = (square x) in
        let result = y + y
        result

let sumsquare_wrong x =
    let y = (square x) in
        let result = y + y
    // this will throw an error!
    // result is out of scope at this point
    result

```

### let-effect


