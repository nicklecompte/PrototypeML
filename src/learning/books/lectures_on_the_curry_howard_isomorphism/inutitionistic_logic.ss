; Ch.2 of Lectures on Curry Howard
;
; Classical understanding of logic is based on the notion
; of truth. The truth of a statement is absolute and
; independent of any reasoning, understanding, or
; action. Statements are either true or false with
; no regard to an external observer.
;
; Classical logic is robust, but not necessarily informative.
; The statement (P or (not P)) is not very meaningful even
; if it may expose imoportant truths. For instance:
;
;   There are seven 7's in a row somewhere in the
; decimal representation of pi.
;
; This is either true or not true, and it may well be the
; case that we will never know. Another example:
;
;   There are two irrational numbers x and y such that
; x^y is rational.
;
; The proof is very simple: if sqrt(2)^sqrt(2) is rational,
; then we are done. Otherwise, (sqrt(2)^(sqrt(2))^(sqrt(2))
; is obviously rational and by hypothesis its base and exponent are not.
;
; The problem is that this doesn't tell us what the irrational
; number actually is.
;
;   This is why there is interest in intuitionistic (or
; constructive) logic.
;
;;; Intuitive sematics ;;;
;
; The following rules explain the infiormal connstructive
; semantics of propositional correctness. These rules
; are sometimes called the BHK-interpretation (for
; Brouwer/Heyting/Kolmogorov).
;
;   - A construction of \phi_1 \and \phi_2 consists of
; a construction of \phi_1 and a construction of \phi_2
;   - A construction of \phi_1 \or \phi_2 consists of
; a number i \in {1,2} and a construction \phi_i.
;   - A construction of \phi_1 -> \phi_2 consists of
; a function transforming every construction of \phi_1
; into a construction of \phi_2.
;   - There is no possible construction of ⊥ (falsity)
;
; Negation \not \phi is best understood as an abbreviation
; of \phi -> ⊥. A construction of \not \phi is a function that
; turns every construction of \phi into a
; non-existent object. Note that this also holds
; in classical logic, but that \not \phi is a much
; stronger statement than "there is no construction
; for \phi."
;
; Example: The following tautologies from classical
; logic may or may not have intutivie explanations
; in the BHK interpretation.
;
; ⊥ -> p [the domain of ⊥ is the empty set. So any
; function works for this]

; ((p -> q) -> p) -> p  [does not seem to hold in
; intuitionistic logic since it begs the question
; of constructing p -> q in the first place]
;
; p -> \not (\not p) [
;   This expands to
;       p -> ((p -> ⊥) -> ⊥)
;   So, given a proof of p, we must construct a function
; that takes proofs (p -> ⊥) (that is, a function
; mapping proofs of p to proofs of falsity),
; and obtains proofs of ⊥. Such a function is
;   f(function_taking_proofs_of_p_to_falsity) =
;   function_taking_proofs_of_p_to_falsity(given_proof_o)
;]
;
; \not (\not p) -> p [does not seem to have intuitionistic
; interpretation]
; [explore the rest of these]
;
; Natural deduction
;
; We assume an infinite set PV of propositional
; variables and we define the set Φ of formulas by induction, represented by
; the following grammar:
; Φ ::= ⊥ | PV | (Φ → Φ) | (Φ ∨ Φ) | (Φ ∧ Φ).

(define-syntax create-formula
  (lambda (x) (syntax-case x (propositional-variable constant app func pi : ->)
    [(_ name (sort sort-value))
      #'(pseudoterm-interface (pseudoterm-kind sort) sort-value name)]
    [(_ name (variable variable-value))
      #'(pseudoterm-interface (pseudoterm-kind variable) variable-value name)]
    [(_ name (constant constant-value))
      #'(pseudoterm-interface (pseudoterm-kind constant) constant-value name)]
    [(_ name (app left right))
      #'(pseudoterm-interface (pseudoterm-kind app) (cons left right) name)]
    [(_ name (func variable-term : variable-type-term -> body))
      #'(pseudoterm-interface (pseudoterm-kind func)
        (cons (cons 'λ (cons variable-term variable-type-term)) body) name)]
    [(_ name (pi variable-term : variable-type-term -> body))
      #'(pseudoterm-interface (pseudoterm-kind pi)
        (cons (cons 'π (cons variable-term variable-type-term)) body) name)]
    )
  )
)
