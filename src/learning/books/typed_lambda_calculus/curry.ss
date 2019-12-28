; The Curry type system
; Originally this was developed for the theory of combinators, and due to their
; implementation are often called systems of type assignment. If the type
; \sigma \in \mathbb{T} is assigned to the term M \in \Lambda, one writes
; |- M : \sigma. Usually a set of assumptions \Gamma is needed to derive a type
; assignment and one writes \Gamma |- M : \sigma ("Gamma yields M in sigma")
; A particular Curry type assignment depends on two parameters: the set
; \mathbb{T} and the rules of type assignment.
;
; Definition : the set of types of \lambda\rightarrow, notation
; Type(\lambda \rightarrow), is inductively defined as follows.
; Write \mathbb{T} = Type(\lambda \rightarrow).
; 1) Start with some \alpha, \alpha', \alpha''... \in \mathbb{T}
; 2) For each \sigma, \tau \in \mathbb{T}, the type (\sigma \rightarrow \tau)
; of functions is also in \mathbb{T}.
;
; We can represent this definition of \mathbb{T} using the following syntax:
;
; \mathbb{T} = \mathbb{V} | \mathbb{T} -> \mathbb{T}
; where
; \mathbb{V} = \alpha | \mathbb{V}''