;;; Helpers ;;;

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

; Scheme implementation, with the alphabet taken to be the set of
; (Chez) Scheme atoms

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
  (lambda (maybeterm)
    (cond
      [(null? maybeterm) #f]
      [(symbol? maybeterm) #t]
      [(equal? (car maybeterm) 'mllambda) #f]
      [(is-raised-lambda-symbol? (car maybeterm)) (is-preterm-of-scheme-symbol? (cdr maybeterm))]
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
  (lambda (preterm)
   (cond
      [(symbol? preterm) (list preterm)]
      [(is-raised-lambda-symbol? (car preterm))
        (let ([ft_cdr (get-free-variables (cdr preterm))])
          (filter (lambda (y) (not (equal? y (cdr (car preterm))))) ft_cdr)) ]
      [else (union (get-free-variables (car preterm)) (get-free-variables (cdr preterm)))])))


; 1.1.12. Example. Let x, y, z denote distinct variables. Then
; (i) FV(xyz) = {x, y, z};

(define test-get-free-variables-1
  (get-free-variables (cons (cons 'x 'y) 'z)))
; (ii) FV(λx.x y) = {y};
(define test-get-free-variables-2
  (get-free-variables (cons (raise-symbol-to-lambda 'x) (cons 'x 'y))))
; (iii) FV((λx.x x) λy.y y) = {}.
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
; (\lambda x . P)[x := N] = (\lambda x . P)
(define test-preterm-substitution-5
  (apply-preterm-substitution
    (cons (raise-symbol-to-lambda 'x) (cons 'y 'x))
    'x (cons 'a 'x)))
; (\lambda y . P)[x := N] = (\lambda y .P[x := N]) if y \notin FV(N) or x \notin FV(P)
(define test-preterm-substitution-6
  (apply-preterm-substitution
    (cons (raise-symbol-to-lambda 'y) (cons 'y 'x))
    'x (cons 'a 'x)))

(define test-preterm-substitution-7 ; WRONG!
  (apply-preterm-substitution
    (cons (raise-symbol-to-lambda 'y) (cons 'y 'b))
    'x (cons 'x 'y)))

; (\lambda y . P)[x := N] = (\lambda z . P[y := z][x := N]) if y \in FV(N) and x \in FV(P),
; where z \in V is chosen such that z \notin FV(P) \Union FV(N)
(define test-preterm-substitution-8
  (apply-preterm-substitution
    (cons (raise-symbol-to-lambda 'y) (cons 'a (cons 'y 'x)))
    'x  (cons 'y 'c)))

(define test-preterm-substitution
  (apply-preterm-substitution
    (cons
      (cons (raise-symbol-to-lambda 'x) 'x)
      (cons 'y 'z)) 'x 'y))

; 1.1.14. Example. If x, y, z are distinct variables, then for a certain variable u:
; ((λx.x yz) (λy.x y z) (λz.x y z))[x := y]=(λx.x yz) (λu.y u z) (λz.y y z)

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