;;; Helpers ;;;

; Slow stupid union of two lists
(define union
  (lambda (ls1 ls2) (
      cond
        [(null? ls1) ls2]
        [(member (car ls1) ls2) (union (cdr ls1) ls2)]
        [else (union (cdr ls1) (cons (car ls1) ls2))])
  ))

; The object of study in lambda calculus are lambda terms.
; Before defining those, it is useful to introduce the notion
; of a pre-term

; Definition:
; Let V = {v_0, v_1, ...} denote an infinite alphabet.
; The set \Lambda^{-}(V) of *pre-terms* is the set of strings
; satisfying the following grammar:
; \Lambda^{-} := V \Union (\Lambda^{-} \Lambda^{-}) \Union (\lambda V \Lambda^{-})

; Examples:
; v_1 \in \Lambda^{-}
; (v_0 (v_1 v_2)) \in \Lambda^{-}
; (\lambda v_1 . (v1 v2)) \in \Lambda^{-}
; (v_1 v_2 v_2) \notin \Lambda^{-}

; first we need a way to distinguish the lambda term
; We make the defining token a (list 'lambda) since we want 'lambda itself
; to be in our alphabet (Scheme symbols)
; Note: this is not type-safe. We should probably add "if not symbol? throw"
(define raise-symbol-to-lambda
  (lambda (symbol) (
    cons 'mllambda symbol)))

(define test-raise-symbol-to-lambda
  (raise-symbol-to-lambda 'y))

(define is-raised-lambda-symbol?
  (lambda (term)
    (cond
      [(symbol? term) #f]
      [(pair? term) (and (equal? (car term) 'mllambda) (symbol? (cdr term)))]
      [else #f]
    )))

(define test-is-raised-lambda-symbol
  (and
    (not (is-raised-lambda-symbol? 'a))
    (not (is-raised-lambda-symbol? (cons 'a 'b)))
    (not (is-raised-lambda-symbol? (cons 'a  'mllambda)))
    (is-raised-lambda-symbol? (cons 'mllambda 'a))
    (not (is-raised-lambda-symbol? (cons 'mllambda (cons 'a 'b))))
  ))

(define is-preterm-of-scheme-symbol?
  ; In this implementation, symbols are symbols
  (lambda (maybeterm)
    (cond
      ; Null is not a preterm
      [(null? maybeterm) #f]
      ; Symbols are preterms except the distinguished lambda symbol
      [(symbol? maybeterm) (not (equal? 'mllambda maybeterm))]
      ; Lambda symbols AND the first part of lambda expressions are not preterms
      [(equal? (car maybeterm) 'mllambda) #f]
      ; Complete lambda expressions are preterms
      [(is-raised-lambda-symbol? (car maybeterm)) (is-preterm-of-scheme-symbol? (cdr maybeterm))]
      ; The (properly-defined) sum of two preterms is a preterm
      [else (and (is-preterm-of-scheme-symbol? (car maybeterm)) (is-preterm-of-scheme-symbol? (cdr maybeterm)))]
)))

; Definition:
; For a term M in a set of preterms Lambda^{-} define the set FV(M) \subset V of
; *free variables of M* as follows:
; FV(x) = {x}
; FV(\lambda x, P) = FV(P)\{x}
; FV(P,Q) = FV(P) \Union FV(Q)
; If FV(M) = {} then M is *closed.*

(define get-free-variables
  ; Get all the free variables of a preterm
  (lambda (preterm)
    (cond
      ; Symbols by themselves are preterms
      [(symbol? preterm) (list preterm)]
      [(is-raised-lambda-symbol? (car preterm))
        (let ([ft_cdr (get-free-variables (cdr preterm))])
          (filter (lambda (y) (not (equal? y (cdr (car preterm))))) ft_cdr)) ]
      [else (union (get-free-variables (car preterm)) (get-free-variables (cdr preterm)))])))


; 1.1.12. Example. Let x, y, z denote distinct variables. Then
; (i) FV(xyz) = {x, y, z};

(define test-get-free-variables-1
  (get-free-variables (cons (cons 'x 'y) 'z)))
(define test-get-free-variables-2
  (get-free-variables (cons (raise-symbol-to-lambda 'x) (cons 'x 'y))))
(define test-get-free-variables-3
  (get-free-variables (cons
                        (cons (raise-symbol-to-lambda 'x) (cons 'x 'x))
                        (cons (raise-symbol-to-lambda 'y) (cons 'y 'y)))))

; Definition:
; For M, N \in \Lambda^{-}(V) and x \in V, the *substitution of N for x in M*,
; written M[x := N] \in Lambda^{-}(V), is defined as follows, where x != y:
; x[x := N] = N
; y[x := N] = y
; (P Q)(x := N) = ( P(x := N) Q(x := N) )
; (\lambda x . P)[x := N] = (\lambda x . P)
; (\lambda y . P)[x := N] = (\lambda y .P[x := N]) if y \notin FV(N) or x \notin FV(P)
; (\lambda y . P)[x := N] = (\lambda z . P[y := z][x := N]) if y \in FV(N) and x \in FV(P),
; where z \in V is chosen such that z \notin FV(P) \Union FV(N)
; To choose such a z, assign an ordering to the (countable) alphabet and choose a minimal
; index satisfying the above.

; small helper to get a symbol not in the list
; not effecient, just a bunch of a's.
(define get-symbol-not-in-list
  (lambda (ls)
    (letrec ([helper (lambda (lis sy)
                        (cond
                          [(member sy lis) (helper lis (string->symbol (string-append (symbol->string sy) "a")))]
                          [else sy]))])
     (helper ls 'a))))

(define apply-preterm-substitution
  (lambda (preterm-to-substitute substitution-symbol substitution-preterm)
    ( cond
      [(symbol? preterm-to-substitute)
        (cond
          [(equal? preterm-to-substitute substitution-symbol) substitution-preterm]
          [else preterm-to-substitute])]
      [(and (is-preterm-of-scheme-symbol? (car preterm-to-substitute)) (is-preterm-of-scheme-symbol? (cdr preterm-to-substitute)))
        (cons
          (apply-preterm-substitution (car preterm-to-substitute) substitution-symbol substitution-preterm)
          (apply-preterm-substitution (cdr preterm-to-substitute) substitution-symbol substitution-preterm))]
      [else ; must be a  lambda . preterm
        (let ([x (cdr (car preterm-to-substitute))] [p (cdr preterm-to-substitute)]) ; the symbol in the lambda
          (cond
            [(equal? x substitution-symbol) preterm-to-substitute]
            [(or
              (not (member x (get-free-variables substitution-preterm)))
              (not (member substitution-symbol (get-free-variables p))))
                (cons (car preterm-to-substitute) (apply-preterm-substitution p substitution-symbol substitution-preterm))]
            [else (let ([z (get-symbol-not-in-list
                             (union (get-free-variables p)
                                    (get-free-variables substitution-preterm)))])
                              (apply-preterm-substitution
                                (cons (raise-symbol-to-lambda z)
                                (apply-preterm-substitution p x z))
                                substitution-symbol substitution-preterm))]
            ))])))

; x[x := N] = N
(define test-preterm-substitution-1
  (apply-preterm-substitution 'x 'x (cons (cons (raise-symbol-to-lambda 'y) '(y plusplus)) 'z)))


; y[x := N] = y
(define test-preterm-substitution-2
  (apply-preterm-substitution 'y 'x (cons 'a 'b)))


; (P Q)(x := N) = ( P(x := N) Q(x := N) )
(define test-preterm-substitution-3
 (apply-preterm-substitution (cons 'y 'x) 'x (cons 'a 'b)))

(define test-preterm-substitution-4
  (apply-preterm-substitution (cons 'y 'x) 'y (cons 'a 'x)))


; ; (\lambda x . P)[x := N] = (\lambda x . P)
(define test-preterm-substitution-5
  (apply-preterm-substitution
    (cons (raise-symbol-to-lambda 'x) (cons 'y 'x))
    'x (cons 'a 'x)))


; ; (\lambda y . P)[x := N] = (\lambda y .P[x := N]) if y \notin FV(N) or x \notin FV(P)
(define test-preterm-substitution-6
  (apply-preterm-substitution
    (cons (raise-symbol-to-lambda 'y) (cons 'y 'x))
    'x (cons 'a 'x)))

(define test-preterm-substitution-7 ; working
  (apply-preterm-substitution
    (cons (raise-symbol-to-lambda 'y) (cons 'y 'b))
    'x (cons 'x 'y)))


; ; (\lambda y . P)[x := N] = (\lambda z . P[y := z][x := N]) if y \in FV(N) and x \in FV(P),
; ; where z \in V is chosen such that z \notin FV(P) \Union FV(N)
(define test-preterm-substitution-8
  (apply-preterm-substitution
    (cons (raise-symbol-to-lambda 'y) (cons 'a (cons 'y 'x)))
    'x  (cons 'y 'c)))

(define test-preterm-substitution
  (apply-preterm-substitution
    (cons
      (cons (raise-symbol-to-lambda 'x) 'x)
      (cons 'y 'z)) 'x 'y))


; ; 1.1.14. Example. If x, y, z are distinct variables, then for a certain variable u:
; ; ((����x.x yz) (����y.x y z) (����z.x y z))[x := y]=(����x.x yz) (����u.y u z) (����z.y y z)

(define test-preterm-substitution-14
  (apply-preterm-substitution
  (cons
    (cons (raise-symbol-to-lambda 'x) (cons 'x (cons 'y 'z)))
    (cons
      (cons (raise-symbol-to-lambda 'y) (cons 'x (cons 'y 'z)))
      (cons (raise-symbol-to-lambda 'z) (cons 'x (cons 'y 'z)))
    )
  )
  'x
  'y
))

;  Let alpha-equivalence (written ~alpha) be the smallest relation on the lambda  terms such that
; 1) P ~alpha P
; 2) lambda x : P ~alpha  lambda y : P[x:=y]
; and closed under the following rules:
; a) P ~alpha P' => for all x in V, lambda x . P ~alpha lambda x . P'
; b) P ~alpha P' => for all Z in Lambda^{-}, P . Z ~alpha  P' . Z
; c) P ~alpha P' => for all Z in Lambda^{-}, Z . P ~alpha  Z . P'
; d) P ~alpha P' => P' ~alpha P
; ; e P ~alpha P' and P' ~alpha P'' => P ~alpha P''

(define are-alpha-equivalent-preterms?
    (lambda (interm1 interm2)
      (letrec ([inner (lambda (term1 term2)
        (cond
            ; equal preterms are alpha-equivalent
            [(equal? term1 term2) #t]
            ; short-circuiting the above so we can
            ; assume the preterms are not symbols, and hence pairs
            [(and (symbol? term1) (symbol? term2)) (equal? term1 term2)]
            [(symbol? term1) #f]
            [(symbol? term2) #f]
            [(is-raised-lambda-symbol? (car term1))
                (let ([x (cdr (car term1))] [p (cdr term1)])
                    (cond
                        [(is-raised-lambda-symbol? (car term2))
                        (if (equal? (cdr (car term2)) x)
                            ; if term2 is a lambda with the same variable,
                            ; then they are alpha-equivalent iff their expressions are.
                            (inner p (cdr term2))
                            ; If term2 is a lambda expression with a different symbol for the variable,
                            ; then the cdr of the term must be the substituin of x for y for alpha-equivalence
                            (inner (cdr term2) (apply-preterm-substitution p x (cdr (car term2)))))]
                        [else #f]
                ))]
            [else (let ([term1-a (car term1)]
                        [term1-b (cdr term1)]
                        [term2-a (car term2)]
                        [term2-b (cdr term2)])
                        (and
                          (are-alpha-equivalent-preterms? term1-a term2-a)
                          (are-alpha-equivalent-preterms? term1-b term2-b)
        ))]
  ))])
      (or (inner interm1 interm2) (inner interm2 interm1))
  )))

(define test-alpha-equivalent-bundled
  (and
; Correct
  (are-alpha-equivalent-preterms?
    (cons (cons 'mllambda 'x) (cons (cons 'mllambda 'b) 'x))
    (cons (cons 'mllambda 'x) (cons (cons 'mllambda 't) 'x)))

  ; Correct
  (are-alpha-equivalent-preterms?
    (cons (cons 'mllambda 'a) (cons (cons 'mllambda 'b) 'a))
    (cons (cons 'mllambda 'x) (cons (cons 'mllambda 'b) 'x)))

  ; now it's correct :)
  (are-alpha-equivalent-preterms?
    (cons (cons 'mllambda 'a) (cons (cons 'mllambda 'b) 'a))
    (cons (cons 'mllambda 'x) (cons (cons 'mllambda 't) 'x)))

  ; works
  (not (are-alpha-equivalent-preterms?
    (cons
      (cons (cons 'mllambda 'a) (cons (cons 'mllambda 'b) 'a))
      (cons (cons 'mllambda 'x) (cons (cons 'mllambda 't) 'x))
    )
    (cons (cons 'mllambda 'x) (cons (cons 'mllambda 't) 'x))
  ))

  ; works
  (are-alpha-equivalent-preterms?
    (cons
      (cons (cons 'mllambda 'a) (cons (cons 'mllambda 'b) 'a))
      (cons (cons 'mllambda 'x) (cons (cons 'mllambda 't) 'x))
    )
    (cons
      (cons (cons 'mllambda 'x) (cons (cons 'mllambda 't) 'x))
      (cons (cons 'mllambda 'a) (cons (cons 'mllambda 'b) 'a))
    )
  )
  ; Works
  (are-alpha-equivalent-preterms?
    (cons (cons 'mllambda 'x) 'x)
    (cons (cons 'mllambda 'y) 'y))

  ; Works
  (not (are-alpha-equivalent-preterms?
    (cons (cons 'mllambda 'x) (cons 'x 'x))
    (cons (cons 'mllambda 'y) (cons 'a 'y))))
  ))

(are-alpha-equivalent-preterms? (cons (cons (cons 'mllambda 'a) (cons (cons 'mllambda 'b) 'a)) (cons (cons 'mllambda 'x) (cons (cons 'mllambda 't) 'x))) (cons (cons 'mllambda 'x) (cons (cons 'mllambda 't) 'x)))

; ; $ = ?????????????????????????? (26 characters)
; ; ? = \lambda abcdefghijklmnopqstuvwxyzr . r (thisisafixedpointcombinator)
; ; $ F = ?????????????????????????? F
; ;     = (\lambda abcdefghijklmnopqstuvwxyzr . r (thisisafixedpointcombinator))????????????????????????? F
; ;     ; Now F is in the 26th position:
; ;     =_beta  (\lambda abcdefghijklmnopqstuvwxyz . F (thisisafixedpointcombinatoF))?????????????????????????
; ;     =_beta F ?????????????????????????? F
; ;     = F ($ F)
; ; Examples:
; ; lambda x . x ~alpha lambda y . y
; ; lambda x . x z ~alpha lambda y . y z
; ; lambda x . (lambda y . x y) ~alpha lambda y . (lambda x . y x)
; ; lambda x . x y NOT ~alpha lambda x . x z

; ; Definition For any M \in \Lambda^{-} define the equivalence class [M]_{alpha} by

; ; [M]_{alpha} = {N \in \Lambda^{-} : M ~alpha N}

; ; Then the set of lambda terms., \Lambda, is the set of distinct equivalence classes.
; ; NOTE: Often people use lambda term to mean preterm, and equivalent preterms
; ; are termed "identfied" lambda terms.

; ; From here on we almost always refer to this equivalence class,
; ; not the preterm itself, and we drop the [_]_{alpha} notation.

; ; Definition: For M \in \Lambda define the set FV(M) \subset V of
; ;free variables of M as follows:

; ; 1) FV(x) = {x}
; ; 2) FV(\lambda x, P) = FV(P) \ {x}
; ; 3) FV(P,Q) = FV(P) \union FV(Q)
; ; If FV(M) = {} then M is closed.

; ; Note: strictly speaking, FV is a function from \Lambda to V.
; ; We must show that function exists and is unique.
; ; Uniqueness is easy: any two implementations FV_1 and FV_2 must
; ; 1) evaluate to the same thing for any symbol by rule 1
; ; 2) evaluate to the same thing for any \lambda x . y by rule 1 and 2
; ; 3) evalute to the same pair by rule 3
; ; The result follows from induction.
; ; Existence: just take a function that chooses a member of the equivalnece
; ; class at random. Since the choice is irrelevant (by uniqueness),
; ; this is well-defined.

; ; We can define substitution similarly.
; ; For M, N  \in \Lambda, and x \in V, the
; ; substititon of N for x in M is defined:
; ; x[x: = N] = N
; ;  y[x:=N] = y
; ; {P Q}[x:=N] = P[x:=N]Q[x:=N]
; ;  (lambda y . P)[x:=N] = \lambda y . (P[x:=N]) if x != y and y\notin FV(N)

; ;; WARNING: the notes did not have this one and I am not sure why.
; ;; (lambda y . P)[x := N] = \lambda z . (P [y:=z][x:=N]) o.w.

; ;; Reductin

; ; Defintion: let \arrow_\beta be the smallest relation on \Lambda such that
; ; (\lambda x . P) Q \arrow_\beta P[x:=Q]
; ; which is closed under the rules
; ; a) P \arrow_\beta P' => for all x in V, lambda x . P \arrow_\beta lambda x . P'
; ; b) P \arrow_\beta P' => for all Z in Lambda, P . Z \arrow_\beta  P' . Z
; ; c) P \arrow_\beta P' => for all Z in Lambda, Z . P \arrow_\beta  Z . P'

; ; Definition:
; ; The relation \Aarrow_\beta (multi-step beta-reduction) is the transitive-reflexive
; ; closure of \arrow_\beta - that is, \Aarrow_\beta is the smallest relation closed
; ; under the rules
; ; P \arrow_\beta P' => P \Aarrow_\beta P'
; ; P \Aarrow_\beta P' and P' \Aarrow_\beta P'' => P \Aarrow_\beta P''
; ; P \Aarrow_\beta P

; ; Definition
; ; The relation =_beta (beta-equality) is the transitive-reflexive-symmettic
; ; closure of \arrow_\beta. We will often just write =.

; ; Examples:
; ; (\lambda x . x x ) (\lambda z . z) \arrow_\beta
; ;    (x x)[x := \lambda z . z]
; ;    (\lambda z .z )(\lambda y . y)
; ; (\lambda z .z) (\lambda y.y) \arrow_\beta
; ;     z[z:=\lambda y. y]
; ;     = \lambda y .y
; ; (\lambda x.x x)(\lambda z.z) \Aarrow_\beta \lambda y .y
; ; (\lambda x . x) y z = y ((\lambda x . x) z)


; ; a record type to represent a beta reduction

;(define-record-type MLRecordTypeElement
;  (fields property-name type value) (nongenerative))

(define get-one-deeply-recursed-beta-reduction
  (lambda (term) (
      cond
        [(symbol? term)
          term]
        [(symbol? (car term)) ; base case of P \beta P' => Z P \beta Z P'
          (cons
            (car term)
            (get-one-deeply-recursed-beta-reduction (cdr term)))]
        [(is-raised-lambda-symbol? (car term)) ; P \beta P' => lambda x . P \beta lambda x . P'
          (cons
            (car term)
            (get-one-deeply-recursed-beta-reduction (cdr term)))]
        [(is-raised-lambda-symbol? (car (car term))) ; base case of definition for beta reduction
          (apply-preterm-substitution
            (cdr (car term))
            (cdr (car (car term)))
            (cdr term))]
        [else (cons
                 (get-one-deeply-recursed-beta-reduction (car term))
                 (get-one-deeply-recursed-beta-reduction (cdr term))
              )]
  )))

; should be (x x)
(define test-beta-reduction-1
  (let ([reduced
    (get-one-deeply-recursed-beta-reduction
      (cons
        (cons (cons 'mllambda 'x) (cons 'x 'x))
        (cons (cons 'mllambda 'z) 'z)
      ))])
    (are-alpha-equivalent-preterms?
      reduced
      (cons (cons (cons 'mllambda 'z) 'z) (cons (cons 'mllambda 'y) 'y)))
  )
)

(define test-beta-reduction-2
  (let ([reduced
          (get-one-deeply-recursed-beta-reduction
            (cons
              (cons (cons 'mllambda 'z) 'z)
              (cons (cons 'mllambda 'y) 'y)
            ))])
        (are-alpha-equivalent-preterms?
          reduced
          (cons (cons 'mllambda 'y) 'y))))

(define test-beta-reduction-3
  (let ([reduced
          (get-one-deeply-recursed-beta-reduction
             (cons
               (cons (cons 'mllambda 'x) (cons 'x 'x))
               (cons (cons 'mllambda 'x) 'x)
            ))])
        (are-alpha-equivalent-preterms?
          (get-one-deeply-recursed-beta-reduction reduced)
          (cons (cons 'mllambda 'x) 'x))))

(define get-full-beta-reduction
  (lambda (term) (
      letrec ([inner
        (lambda (thisterm lastterm) (
            if (equal? lastterm thisterm) thisterm
               (inner (get-one-deeply-recursed-beta-reduction thisterm) thisterm)
        ) )])
      (inner (get-one-deeply-recursed-beta-reduction term) term))
   ))

(define test-beta-reduction-4
  (let ([baseterm
          (cons
            (cons (cons 'mllambda 'x) (cons 'x 'x))
            (cons (cons 'mllambda 'x) 'x)
          )
        ])
  (are-alpha-equivalent-preterms? (get-full-beta-reduction baseterm) (cons (cons 'mllambda 'x) 'x))))

(define are-beta-equal?
  (lambda (term1 term2)
    (are-alpha-equivalent-preterms?
      (get-full-beta-reduction term1)
      (get-full-beta-reduction term2))
  )
)

; ;;; Informal interpretation ;;;

; ; Informally, \lambda-terms express functions and applications of
; ; functions in a pure form. For instance, the \lambda-term
; ; I = \lambda x. x
; ; intutively denotes the function that maps any argument to itself.
; ; This is similar to the n |-> n notation in mathemmatics.
; ; Howecver, \lammbda x.x is a *stribng* over an alphabet with symbols
; ; \lambda, x, etc.
; ; As in the notaiton n |-> n, the name of the abstracted variable
; ; is not significant; this is why we identify \lambda x . x with \lambda y . y, etc.

; ; beta-reduction formalizes the calculation of values in functions
; ; by collapsing and collecting like terms.

; ; One good preterm is
(define identity (cons (cons 'mllambda 'x) 'x))

(define test-beta-reduction-5
  (are-beta-equal? (cons identity 'kitten) 'kitten))

; Another term is
(define k-star
  (cons (cons 'mllambda 'y) (cons (cons 'mllambda 'x ) 'x)))
; which maps any preterm to the identity function.

; There's also
(define k
  (cons (cons 'mllambda 'y) (cons (cons 'mllambda 'x) 'y)))

; which denotes the function that maps any argument k to a function g
; that, for all symbols x,  satisfies g(x) = k

(define test-beta-reduction-7
  (are-beta-equal? (cons k-star 'kitten) identity))

(define test-beta-reduction-6
  (are-beta-equal? 'kitten (get-full-beta-reduction (cons (cons k 'kitten) 'doggie))))


(define omega-function
    (cons
      (cons 'mllambda 'x)
      (cons 'x 'x)
    )
)
(define omega-combinator (cons omega-function omega-function))

; The omega-combinator is a nontrivial preterm
; which beta-reduces to itself.

(define test-beta-reduction-9
  (equal? (get-one-deeply-recursed-beta-reduction omega-combinator) omega-combinator))

;;; The Church-Rosser Theorem

; Since a lambda term M can contain several beta-redexes,
; there may be several N such that M \beta N.
; The Church-Rosser theorem states that, if
; M \Aarrow_beta M1 and
; M \Aarow_beta M2,
; then a single lambda term M3 can be found with
; M1 \Aarrow_beta M3 and M2 \Aarrow_beta M3

; In particular, if M1 and M2 are beta-normal,
; meaning that they're lambda terms that admit no further
; beta reductions, then they must be the same lambda term.

; A relation > on Lambda satisifes the diamond property if
; fo all M1, M2, M3 \in \Lambda,  if M1 > M2 and M1 > M3, then there exists
; an M4 \in \lambda such that M2 > M4 and M3 > M4

; The transitive closure of a binary relation R, R*, is the least relation satisfying
; R(A,B) => R*(A,B)
; R*(A,B) and R*(B,C) => R*(A,C)

; The reflexive closure of R, R=, is the least relation satisfying
; R(A,B) => R=(A,B)
; R=(A,A)

; Lemma: Let > be a relation on \Lambda and suppose its transitive closure is \Aarrow_beta.
; If > satisfies the diamond property, then so does \Aarrow_beta

; Proof: Suppose > satisifes the diamond property. We must show that if >(M1, M2) and >(M2, M3),
; there exists an M4 in \Lambda such that M2 \Aarrow_beta M4 and M3 \Aarrow_beta M4.
; Because \Aarrow_beta is the transitive closure, M1 \Aarrow_beta M3.
; There are two cases:
; >(M1, M3):
;  In this case, we have >(M1, M2) and >(M1,M3). Because > satisfies the diamond properity,
;  there exists M4 such that >(M2,M4) and >(M3, M4). Since > \subset \Aarrow_beta the proposition holds.
; not >(M1, M3)
;  M1 \Aarrow_beta M3. Therefore there exists an N such that one of the following hold:
;  - (>(M1, N) and \Aarrow_beta(N, M3)
; - (\Aarrow_beta(M1,N) and >(N, M3))
; - (>(M1, N) and >(N, M3))
; In the last case the propositon holds by > having the diamond property.
; In the other cases an inductive reduction can be made to the last case,
; and the proposition holds.

; Definition: Let \Aarrow_iota be the relation on  \Lambda defined by
; 1) P \Aarrow_iota P
; 2) P \Aarrow_iota P' => \lambda x . P \Aarrow_iota \lambda x . P'
; 3) P \AArrow_iota P' and Q \Aaarow_iota Q'
;     => P Q \Aarrow_iota P' Q'
; 4) P \Aarrow_iota P' and Q \Aarrow_iota Q'
;     => (lambda x. P) Q \Aarrow_iota P'[x := Q']

; Lemma: M \Aarrow_iota M' and N \Aarrow_iota N'
;        => M[x := N] \Aarrow_iota M'[x:= N']
; proof:
; Case M = M':
; we must show N \Aarrow_iota N' => M[x := N] \Aarrow_iota M[x := N']
; case M of
;   x : x[x := N] = N \Aaarrow_iota N' = x[x:=N']
;   y : y[x:=N] = y \Aarrow_iota y = y[x:=N']
; (P Q): P[x: = N] Q[x :=N] and it follows by inductiion and 3)
; (lambda y . P) : (lambda y . P)[x = N] = (lambda y . P[x := N])
;        \Aaarrow_iota (lambda y . P[x:=N']) if induction hypothesis on P holds
; This proves for M = M'.
; Case M != M':
; Since M \Aaarrow_iota M', we can also induct on the cases using the above lemma.

; Lemma. \Aarrow_iota satisfies the diamond property.
; Proof:
; Suppose we have M1 \Aarrow_iota M2 and M1 \Aaarrow_iota M3.
; Case 1) M1 = M2.
; TakE M4 = M3. This base case for induction is satisfied.
; Case 2) M1 = lambda x . P and M2 = lambda x . P' with P \Aaarrow_iota P'.
; Then M3 must be lambda x . Q for some Q with P \Aarrow_iota Q.
; If induction hypothesis holds, then this case satisfies diamond property.
; Case 3) M1 =  P Q and M2 = P' Q' wiith P \Aarrow_iota P' and Q \Aarrow_iota Q'.
; Assume P is not a lambda expression (this is case 4).
; Then M3 must also be of the form P'' Q''.
; Hypothesis follows by induction seperately
; on P \Aaarow_iota P' and P \Aarrow P''
; then Q \Aarrow_iota Q' and Q \Aarrow_iota Q''
; Case 4) Follows from previous lemma:
; M1 = (lambda x . P) Q, M2 = P'[x:= Q'] and M3 = P''[x :=Q'']
; Take P''' and Q''' inductively and apply last lemma.

; Lemma: \Aaarrow_beta is the transitive closure of \Aarrow_iota
; Proof:
; On one hand, (\Arrow_beta)= \subset \Aarrow_iota \subset \Aarrow_beta
; OTOH, \Aarrow_beta = (\Arrow_beta=)* \subset (\Aarrow_iota)*
; So \Aarrow_iota* = \Aarrow_beta.

; Church-Rosser theorem: \Aarrow_beta satisfies the diamond property.

; Corollary: If M =_beta N, then there exists an L \in \Lambda such that
; M \Aarrow_beta L and N \Aarrow_beta L.

; Corollary: If M \Aarrow_beta N1 and M \Aarrow_beta N2 and both N1 and n2
; are in beta-normal form, then N1 = N2.

(define test-beta-equality-1
  (not (are-beta-equal?
    (cons (cons 'mllambda 'x) 'x)
    (cons (cons 'mllambda 'x) (cons (cons 'mllambda 'y) 'x))
    )
  )
)

(define mytr
  (cons
    (cons 'mllambda 'x)
    (cons (cons 'mllambda 'y) 'x)))

(define myfl
  (cons
    (cons 'mllambda 'x)
    (cons (cons 'mllambda 'y) 'y)))

(define myifthenelse
   (lambda (b p q) (cons (cons b p) q)))

(define test-beta-equality-2
  (are-beta-equal? (myifthenelse mytr 'p 'q) 'p))

(define test-beta-equality-3
  (are-beta-equal? (myifthenelse myfl 'p 'q) 'q))

(define mypair
  (lambda (p q) (
        cons (cons 'mllambda 'x) (cons (cons 'x p) q)
  )))

(define mypi1
  (cons
    (cons 'mllambda 'x)
    (cons
      (cons 'mllambda 'y)
      'x)
  ))

(define test-beta-equality-4
  (are-beta-equal?
    (cons (mypair 'p 'q) mypi1)
    'p))

(define mypi2
  (cons
    (cons 'mllambda 'x)
    (cons
      (cons 'mllambda 'y)
      'y)
  ))

(define test-beta-equality-5
  (are-beta-equal?
    (cons (mypair 'p 'q) mypi2)
    'q))

(define my-gamma-combinator
  (cons
    (cons 'mllambda 'f)
    (cons
      (cons
        (cons 'mllambda 'x)
        (cons 'f (cons 'x 'x))
      )
      (cons
        (cons 'mllambda 'x)
        (cons 'f (cons 'x 'x))
      )
    )
  )
)

; Demonstratng recursion is well-defined in our lambda calculus:
(let ([F
       (cons
           my-gamma-combinator
           (cons (cons 'mllambda 'f) 'M)
        )
      ])
  (are-beta-equal? (apply-preterm-substitution 'M 'f F) F))

; This allows us to write recursive definitions of ����-terms; that
; is, we may define F as a ����-term satisfying a fixed point equation F =���� ����x.M
; ugh character issues :(
; where the term F occurs somewhere inside M. However, there may be
; several terms F satisfying this equation (will these be ����-equal?).

; Note to self: in the future, just use lambda for everything :/

