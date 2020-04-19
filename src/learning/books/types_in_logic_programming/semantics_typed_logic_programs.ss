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

(define-enumeration ordering (LT GT EQ) orderings)

; LIST[T] -> (T -> T -> bool) -> bool
(define (reflexive? input-set relation-fn)
  (or
    (null? input-set)
    (and
      (relation-fn (car input-set) (car input-set))
      (reflexive? (cdr input-set) relation-fn))))

; LIST[T] -> (T -> T -> bool) -> bool
(define (anti-symmetric? input-set order-fn)
  (or
    (null? input-set)
    (letrec [(crawlfun (lambda (cur-item all-items)
      (cond
        [(null? all-items) #t]
        [(and (order-fn cur-item (car all-items)) (order-fn (car all-items) cur-item))
          (and
            (equal? (car all-items) cur-item)
            (crawlfun cur-item (cdr all-items)))]
        [else (crawlfun cur-item (cdr all-items))])))]
      (and
        (crawlfun (car input-set) input-set)
        (anti-symmetric? (cdr input-set) order-fn)))))

(define (transitive? input-set order-fn)
  (or
    (null? input-set)
    (letrec [(crawlfun (lambda (cur-item all-items)
      (cond
        [(null? all-items) #t]
        [(order-fn cur-item (car all-items))
          (letrec [(cur2 (car all-items)) (crawlfun2 (lambda (all2)
            (cond
              [(null? all2) #t]
              [(order-fn cur2 (car all2))
                (and (order-fn cur-item (car all2)) (crawlfun2 (cdr all2)))]
              [else (crawlfun2 (cdr all2))])))]
            (crawlfun2 all-items))]
        [else (crawlfun cur-item (cdr all-items))])))]
      (and
        (crawlfun (car input-set) input-set)
        (transitive? (cdr input-set) order-fn)))))

; LIST[T] -> (T -> T -> partial-ordering) -> bool
(define (partial-order? input-set order-fn)
  (or
    (null? input-set)
    (let ([cur-item (car input-set)])
    (and
      (order-fn cur-item cur-item)
      (letrec [(crawler-first (lambda (all-items)
        (cond
          [(null? all-items) #t]
          [(order-fn cur-item (car all-items))
            (and
              (if (order-fn (car all-items) cur-item)
                ; check for anti-symmetry
                (equal? cur-item (car all-items))
                ; otherwise just pass #t
                #t)
               ; otherwise check for transitivity
                (letrec ([crawler-second (lambda (rest-items)
                  (cond
                    [(null? rest-items) #t]
                    [(order-fn (car all-items) (car rest-items))
                      (if (not (order-fn cur-item (car rest-items)))
                        #f
                        (crawler-second (cdr rest-items)))]
                    [else (crawler-second (cdr rest-items))]))])
              (and (crawler-second input-set) (crawler-first (cdr all-items)))))]
          [else (crawler-first (cdr all-items))])))]
        (crawler-first (cdr input-set)))
        (partial-order? (cdr input-set) order-fn)))))

(define-syntax type-alphabet-term
  (lambda (x) (syntax-case x (sort variable constant app func pi : ->)
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