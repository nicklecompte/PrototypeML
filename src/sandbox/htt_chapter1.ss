#|
Via Homotopy Type Theory: Univalent Foundations of Mathematics
Encoding some of the ideas in Chez Scheme for...reasons.

- a set theory can be understood as having two "layers":
    1) some a priori provided inductive system of logic
    2) a theory constructed from axioms built in this system (eg ZFC)

By contrast, type theory is only concerned with types. Propositions are identified
with particular types, and the mathematical activity "prove a theorem" is really the
programming job of "construct an object with type {proposition}"

We'll need to make a small digression into deductive reasoning:
Informally, a deductive system is a collection of rules for making judgements.
Algebraically, judgments are like elements of a group and the rules are like group operations.

In a deductive system of first order logic, there is only one judgment: a proposition has a proof.
A rule of first-order logic such as "if A, if B, then (A and B)" is really a rule of proof
construction: given the judgments "A has a proof" and "B has a proof" we may make the judgment
"A and B has a proof."

The basic judgment of type theory, analogous to "a has a proof," is "a : A", expressed:
    - "a is a term with type A",
    - "a is an element of A",
    - "a is a point of A"

The judgment (a : A) is derivable in type theory <=> "A has a proof, a" is derivable in deductive logic.


|#

