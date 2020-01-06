; Notes from A Semantics For Typed Logic Programs, by P.M. Hill and R.W. Topor
;
;
;   From the authors' perspective (and in these notes), the semantics of typed
; logic programs should be based on type first-order logic, in the same sense
; that untpyed logic programs are typically based on untyped first-order logic.
; First they will provide a semantics for arbitrary theories in a typed first-
; order logic,  and then to use these semantics for typed logic programs. They
; are particularly interested in languages that support parametric and inclusion
; polymorphism; that is, a parametric order-sorted language. This allows us to
; define procedures that can be used differently in different contexts: the
; procedures in a polymorphic language can have different arguments while using
; the same underlying code by implementing parametric polymorphism, while inclu-
; -sion polymorphism allows us to define subsets easily.
;
;   Previous work included extending many-sorted logic to include parametric
; polymorphism. [Many-sorted logic is a logic-specific idea of types, defined by
; partitioning the universe set into "sorts" and allowing certain relations to
; be defined as syntactically ill-formed if they combine disjoint sorts.] It has
; also been extended to include inclusion polymorphism by implementing a partial
; ordering on types, and then these concepts were combined in separate ways.
; However, all of this work was done with *definite programs* [a definite prog-
; -gram is a program written with Horn Clauses, i.e. Prolog-style x:=(A,B,C)].
; Further, in all this work subtypes were implemented as subsets of some uni-
; -verse, typically the Herbrand universe
;
;;;;;;; Mathematical logic refresher ;;;;;;
; Given an alphabet A, a first-order language L is defined by the set of
; sequences of the following:
; A itself [the non-logical symbols of the language]
; A countably infinite collection of vriables x_1, x_2,...
; The boolean connectives: negation, implication, disjunfction, conjunction
; The universal (for all) and existential (there exists) quantifiers
; Round brackets ( and ) - used to group symbols
; A ground term in L can be defined recursively as follows:
; - any element of A
; - if F is an n-ary function symbol and a_1 ... a_n are groud terms then
; f(a_1...a_n) is a ground term
; A free variable for a given element in L can be defined recursively as follows:
; - the free variables of an atom are the variables occurring in it
; - the free variables of not-p are the same as p
; - the free variables of p and q, p or q, and p -> q are union(free p, free q)
; - the free variables of (for all x)p(x) and (there exists x)p(x) are given by
; {free variables of p} / {x}
;A ground term is a term without free variables.
; The Herbrand universe is the set of ground terms.
;
;;;;;;;;;;;;;;;;;;
;
; In this chapter the authors remove the restriction to definite programs, pro-
; -vide declarative and procedural semantics, and consider interpretations with
; several independent domains. They require explicit type annotations, which
; somewhat restricts the view of subtypes but enforces structure greater than
; subsetting.
;
;   They start by defining a type language, which consists of a set of elements
; (the types) together with an ordering relation.