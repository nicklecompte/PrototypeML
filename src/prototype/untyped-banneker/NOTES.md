# Notes

## Alternative interpretation of untyped lambda calculus in Lisp-like languages

In Scheme the fundamental unit of computation beyond constants and symbols is the cons - while often presented in the special case of a list, it is in fact a general operator:

(cons a b) = (a.b) where a, b are any Scheme object

What if instead we had a more literal "everything is a function" approach?

Definition: Let A be an alphabet  and W be all words created from this alphabet. The set of alpha pre-terms \Lambda^{-} is the union of the following:
1) functions W -> W
2) functions W -> (\Lambda^{-})

\Lambda^{-} has a subset identified with W