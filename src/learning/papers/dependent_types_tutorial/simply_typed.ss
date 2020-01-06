; Loh, McBride, Swierstra, A tutorial implementation of a dependently-typed
; lambda calculus
; Ported from Haskell to Scheme
;
;;; Simply typed lambda calculus
;
; We consder the simply-typed lambda calculus, \lambda_{\rarrow} for short.
; One can view \lambda_{\rarrow} as the smallest possible statically-typed fun-
; -ctional programming language. Every term is explicitly typed and no type in-
; -ference is performed. It has a much simpler structure than the lambda cal-
; -culus implemented for SML or Haskell, which support polymorphic types and
; type constructors.
;
;;;;;;;;;; Abstract syntax of \lambda_{\rarrow} ;;;;;;;;;;
;
; The base syntax consists of just two constructs:
;
; \tau ::= \alpha         --base-type
;      | \tau -> \tau'    --function-type
;
; There are four types of terms in our calculus:
;     e ::= e : \tau        --annotated-term
;         | x               --variable
;         | e e'            --application
;         | \lambda x -> e  --lambda-abstraction
;
; Terms can be evaluated to values:
;     n ::= x     --variable
;     |   n c     --application
;
;;;;;;;;;; Evaluation ;;;;;;;;;;
;
; The notation e \Downarrow v means that the result of completely evalu-
; -ateing e is v. Since we are in a strongly normalizing language, the evalu-
; -ation strategy is irrelevant. To keep presentation simple we evaluate every-
; -thing as far as possible, and even evaluate under lambda. Type annotations
; are ignored during evaluation. Variables evaluate to themselves.
;
; Evaluation rules:
; if a term evaluates to a value, then the term with annotation evaluates to
; the same value.
; Latex:
; \frac{e \Downarrow v}{e : \tau \Downarrow v}
;
; A variable evaluates to itself.
; Latex:
; \frac{}{x \Downarrow x}
;
; Evaluation of applicative terms is a bit more interesting. It depends on
; whether the left subterm actually evaluates to a lambda or a neutral term. If
; the latter, the evaluation does not proceed further and we construct a new
; neutral term from evaluating the subterms.
;
;   However, if it is a lambda, we \beta-reduce and evaluate the result of this
; substitution.
;
; Evaluation of terms with lambda abstractions proceeds by substituting and
; \beta-reducing.
; Latex:
; \frac
;  {e \Downarrow \lambda x \rightarrow v | v[x \righttarrow e'] \Downarrow v'}
;  {e e' \Downarrow v'}
;
; Evaluation proceeds across application.
; Latex:
; \frac{(e \Downarrow n)  (e' \Downarrow v')}{e e' \Downarrow n v'}
;
;
;;;;;;;;;; Type system ;;;;;;;;;;
;
;   Type rules are generally of the form \Gamma \vdash e : t, indicating that e
; is of type t in the context \Gamma. The context lists valid base types, and
; associates identifiers with type information. We write \alpha : * to indicate
; that \alpha is a base type, and x : \tau to indicate that x is a term of type
; \tau. Every free variable in both terms and types must occur in the context.
; For instance, if we want to declare const to be of type
;
;   (\beta -> \beta) -> \alpha -> \beta -> \beta
;
; we need our context to contain the following:
;   \alpha : *
;   \beta : *
;   const :: (\beta -> \beta) -> \alpha -> \beta -> \beta
;
; And that in particular \alpha and \beta must be introduced first. These con-
; -siderations motivate the definitions of context and their validity given
; below.
;
; Multiple bindings for the same variable can occur in a context, with the
; rightmost binding taking precedence. We write \Gamma(z) to denote the infor-
; -mation associated with identifier z by context \Gamma.
;
; Rules
; \Gamma := \epsilon is the empty context
; The empty context is valid.
; Latex: \frac{}{valid(\epsilon)}
;
; \Gamma = \Gamma, \alpha : * -- adding a type identifier
; Given valid context \Gamma, the context \Gamma, \alpha : * is also valid
; Latex: \frac {valid(Gamma)}{valid(\Gamma,\alpha : *)}
;
; \Gamma = \Gamma, x:: \tau --adding a term identifier
; Given a valid context \Gamma and a type \tau described in \Gamma,
; the context \Gamma, x : \tau is also valid.
; Latex: \frac{valid(Gamma), \Gamma \vdash \tau : *}{valid(\Gamma, x :: \tau)}
;
; A type is well-formed when all its free variables appear in the context.
; Latex: \frac{\Gamma(\alpha) = *}{\Gamma \vdash \alpha : *}
;
; Given two well-formed types in the context, the type of functions between them
; is also well-formed.
; Latex: \frac{\Gamma \vdash \tau : *, \Gamma \vdash \tau' : *}
;                {\Gamma \vdash \tau -> \tau' : *}
;
; In the rules for the well-formedness of types as well as the type rules them-
; -selves which folklow, we implicitly assume all contexts are valid.
;
; Note that this lambda calculus is not polymorphic: a type identifier repre-
; -sents one specific type and cannot be instantiated.
;
;
;;;;;;;;;; Type rules ;;;;;;;;;;
; We do not try to infer the types of lambda-vound variables, so all terms must
; be annotated and we only perform type checking. However, given a term is anno-
; -tated, we can easily determine the type. We mark with :d (=_{\downarrow}) when the
; type is supposed to be annotated (i.e. explicitly provided to the type-
; -checking algorithm) and :u (:_{\uparrow}) when the type is produced by the
; type-checking algorithm. This distinction will become significant in the
; implementation.
;
; We first look at inferable terms. The rule ANN specifies that, given a type
; \tau is defined in a context \Gamma and the term e is defined in \Gamma and
; specified by a :d \tau annotation, the type of e can be checked against its
; annotation and returned.
; Latex:
; \frac{\Gamma \vdash \tau : *, \Gamma \vdash e :d \tau}
;  {\Gamma \vdash (e : \tau) :u \Tau}
;
; The rule VAR specifies that the type of a variable can be looked up in its
; environment.
; Latex:
; \frac{\Gamma(x)=\tau}{\Gamma \vdash x :u \tau}
;
; The rule APP deals with functions. Given an expression e which the type-
; checker can determine is a function (\tau -> \tau') and an expression e' which
; has been annotated as type \tau, the application of e to e' can be determined
; to be of type \tau'.
;
; The rule CHK is specifically for type-checking. If the type-checker can infer
; that an expression e has type \tau, the it can check a term annotated as type
; \tau. Latex:
; \frac{\Gamma \vdash e :u \tau}{\Gamma \vdash e :d \tau}
;
; The final rule deals with type-checking and lambda closures. Suppose we've
; added a term identifier x to our context \Gamma with type \tau and \Gamma
; defines a term e of type t'. Then the lambda expression \lambda x -> e defines
; a term of type (\tau -> \tau'). Not in particular that this implies lambdas in
; a given context can only be checked against function types. Actually type-
; checking the body requires an extended context.

;;;;;;;;;; Implementation ;;;;;;;;;;

; We distinguish terms where the type can be read off ("inferable terms")
; and terms which need a type to be checked ("checkable")
; this allows a hindley-milner inference
;

; First, we represent union types as pairs (constructor-symbol, value)
; the following macro helps with some of the boilerplate for checking these
(define-syntax check-is-tagged-term
  (syntax-rules ()
    ; object : any scheme type
    ; conds : (prefix : symbol) -> (term: any) -> bool
    [(_ object conds)
      (and
        (pair? object) ; must be (prefix, term)
        (let ([prefix (car object)] [term (cdr object)])
          (and
            (symbol? prefix)
            (conds prefix term)))
      )
    ]
  )
)

; Simple helper for checking that a scheme-object is a pair
; with a symbolic prefix
; tagged-term? : Any -> Bool
(define (tagged-term? scheme-object)
  (check-is-tagged-term scheme-object (lambda (a b) #t))
)

;  (define (make-customer name telephone)
;         (lambda (msg)
;           (case msg
;                 ((name) name)
;                 ((telephone) telephone))))

;  (define customer (make-customer "Kent Beck" "1-800-SmallTalk"))

;  (customer 'name) => Kent Beck

; Introducing tagged-term type for name
(define (name-object? scheme-object)
  (check-is-tagged-term scheme-object (lambda (prefix term)
    (cond
        ; The Global form of a Name is just a string
        [(equal? prefix 'Global) (string? term)]
        ; The Local form of a Name is its DeBrujin index
        [(equal? prefix 'Local) (integer? term)]
        ; When we need to extract a term from a value from our language
        ; we will use a quote function. quote will take a value and an integer
        ; (the index of the list of binders we have received)
        ; Therefore the Quote form of a name is the integer in this list.
        [(equal? prefix 'Quote) (integer? term)]
        [else #f]
    ))
  )
)

; Introducting type for type
; type-object? : Any -> Bool
(define (type-object? scheme-object)
  (check-is-tagged-term scheme-object (lambda (prefix term)
    (cond
        ; A type-object can be Free and bound to a simple Name
        [(equal? 'TFree prefix) (name-object? term)]
        ; A type-object can be Fun and represtend as a function
        ; [type-object] -> [type-object]
        [(equal? 'Fun prefix)
          (and
            (pair? term)
            (type-object? (car term))
            (type-object? (cdr term))
          )
        ]
    )
  ))
)

; Test
(type-object? '(TFree . (Global . "String"))) ; #t

; We introduce recursive datatypes for values and neutral terms
(define (value-object? scheme-object)
  (check-is-tagged-term scheme-object (lambda (prefix term)
    (cond
      ; A Lambda value is actually just a regular scheme function
      ; term : value-object -> value-object
      ; and will presumably be built from language-defined functions via compos-
      ; -ition of primitives.
      [(equal? prefix 'VLam) (procedure? term)]
      ; A Neutral value is a neutral-object
      [(equal? prefix 'VNeutral) (neutral-object? term)]
    )
  ))
)

(define (neutral-object? scheme-object)
  (check-is-tagged-term scheme-object (lambda (prefix term)
    (cond
      [(equal? prefix 'NFree) (name-object? term)]
      [(equal? prefix 'NApp) (and
        (pair? term)
        (neutral-object? (car term))
        (value-object? (cdr term))
      )]
    )
  ))
)

; An infeerable term is either
;   an *annotated term*, a pair (checkable-term, type)
;   a bound variable (here represented as an integer)
;   a free variable (here represented as a Name)
;
; A checkable term is either
;   itself an inferable term
;   a lambda of a checkable term

(define (inferable-term? scheme-object)
  (check-is-tagged-term scheme-object (lambda (prefix term)
    (cond
        [(equal? prefix 'Ann) (and (checkable-term? (car term)) (type-object? cdr term))]
        [(equal? prefix 'Bound) (integer? term)] ; DeBrujin index
        [(equal? prefix 'Free) (name-object? term)]
        [(equal? prefix? 'Apply) (and (inferable-term? (car term)) (inferable-term? (cdr term)))]
        [else #f]
    )
  ))
)

(define (checkable-term? scheme-object)
  (check-is-tagged-term scheme-object (lambda (prefix term)
    (cond
        [(equal? prefix 'Inf) (inferable-term? term)]
        [(equal? prefix 'Lam) (checkable-term? term)]
        [else #f]
    )
  ))
)

; We introduce a function vfree that creates the value corresponding to any free
; variable.
;
; vfree : Name -> Value
(define (vfree name)
  (cons 'VNeutral (cons 'NFree name))
)

(define test-vfree
  (let ([name (cons 'Global "test")])
    (value-object? (vfree name))
  )
)

;;;;;;;;;; Evaluation ;;;;;;;;;;

; In this implementation, substitution is handled by passing around a list of
; values. Since we have the DeBrujin indices for bound variables, these indices
; are used to locate the value in the list. [this is not efficient but w/e]. A
; new element is added to the environment when evaluating underneath a binder,
; and we look up the correct element (using Scheme's list-ref function) when we
; encounter a bound variable.

; Env? -> bool
(define (environment? scheme-list)
  (andmap value-object? scheme-list)
)

; let's make our lives easier and practice macros
(define-syntax annotated-match-one
  (syntax-rules (->)
    [(_ pairterm (term-label term-value -> e1))
      (if (equal? term-label (car pairterm))
        (begin
          (set! term-value (cdr pairterm))
          e1
        )
        #f)]
    [(_ pairterm (term-label term-fst term-snd -> e1))
      (if (equal? term-label (car pairterm))
        (begin
          (set! term-fst (car (cdr pairterm)))
          (set! term-snd (cdr (cdr pairterm)))
          e1
        )
        #f)]
  )
)

(define (test-annotated-match-one term)
    (annotated-match-one term
      ('Cat name -> (display (string-append "The cat's name is " name))))
)

(define (test-pair-annotated-match-one term)
    (annotated-match-one term
      ('Cat name age ->
        (display (string-append "The cat's name is " name " and she is " (number->string age) " years old."))))
)

(define-syntax annotated-match
  (syntax-rules (->)
    [(_ pairterm (l1 v1 -> e1)) (annotated-match-one pairterm (l1 v1 -> e1))]
    [(_ pairterm (l1 v1 -> e1) (l2 v2 -> e2) ...)
      (let ([v (annotated-match-one pairterm (l1 v1 -> e1))])
        (if v v (annotated-match pairterm (l2 v2 -> e2) ...)))
      ]
  )
)

(define (test-annotated-match term)
  (annotated-match term
    ('Cat name -> (display (string-append name " meowed loudly.")))
    ('Food food -> (display (string-append "I love to eat " food))))
)

; Term_{\uparrow} -> Env -> Value
(define (eval-inferable-term inferable-term env)
    (annotated-match inferable-term
      ('Ann pair -> (eval-checkable-term (car pair) env))
      ('Free x -> (vfree x))
      ('Bound i -> (list-ref env i))
      ('Apply term1 term2 ->
        (vapp (eval-inferable-term term1) (eval-inferable-term term2)))
    )
)

; Value -> Value -> Value
(define (vapp val1 val2)
  (annotated-match val1
    ('VLam f -> (f val2))
    ('VNeutral n) -> (cons 'VNeutral (cons 'NApp (cons n val2)))
  )
)

; Term_{\downarrow} -> Env -> Value
(define (eval-checkable-term checkable-term env)
  (annotated-match checkable-term
    ('Inf i -> (eval-inferable-term i env))
    ('Lam e -> (cons 'VLam (lambda (x) (eval-checkable-term e (cons x env)))))
  )
)

; Before we can proceed to type-checking we need to define contexts.
; In this simple (unsound) example, there is only one Kind, that of Types, so
; we can say
(define (kind-object? scheme-object)
  (equal? scheme-object '*)
)

; Names in our simply-typed lambda calculus can either have a type or have a
; kind; we introduce a datatype accordingly
(define (info-object? scheme-object)
  (check-is-tagged-term scheme-object (lambda (prefix term)
    (cond
        [(equal? prefix 'HasKind) (kind-object? term)]
        [(equal? prefix 'HasType) (type-object? term)]
        [else #f]
    ))
  )
)
; The context then is just a list of (Name, Info)
(define (context? scheme-object)
    (and
        (list? scheme-object)
        (andmap
          (lambda (x) (and (name-object? (car x)) (info-object? (cdr x))))
        )
    )
)
;
; Type-checking can fail; to do so gracefully we return a result in the Result
; monad. Implementing this in Scheme:
(define (is-result? scheme-object)
  (check-is-tagged-term scheme-object (lambda (prefix term))
    (cond
      [(equal? prefix 'OK) #t]
      [(equal? prefix 'Error) (string? term)]
      [else #f]
    )
  )
)

(define (ok-result? result)
    (equal? (car result) 'OK)
)

; syntax extension to bind results
(define-syntax bind-result
  (syntax-rules ()
    [(_ e1) e1]
    [(_ e1 e2 ...) (if (ok-result? e1) (bind-result e2 ...) e1)]
  )
)

; Check the well-formedness of types
; If successful, returns ('OK, '()), which here is semantically
; Context -> Type -> Kind -> Result<unit>
(define (check-type-well-formed ctx type kind)
    (annotated-match type
      ; If it is a Free type name, then we just need to make sure that
      ; 1) the name itself exists in the context ctx
      ; the tag associated with this name is HasKind (i.e. not HasType)
      ('TFree name -> (let ([lookup-result (assoc name ctx)])
                        (if (and
                              lookup-result
                              (equal? (cadr lookup-result) 'HasKind))
                          (cons 'OK '()) ;
                          ('Error "unknown identifier"))))
      ; If it is a function, check the well-formedness of the signature
      ; by checking the well-formedness of the subtypes
      ('Fun type1 type2 -> (bind-result
                             (check-type-well-formed ctx type1 kind)
                             (check-type-well-formed ctx type2 kind)))
    )
)

; Helper function for check-type-inferable-term
; takes in a TypeObject and either returns OK(Fun t t') if the object is a function,
; or Error("tried to apply tern to non-function type") if not
; TypeObject -> Result(TypeObject)
(define (check-is-function-type type-object)
  (let ([match-result (annnotated-match type-object
    ('Fun x y -> 'OK(type-object))
  )])
    (if match-result
      match-result
      (cons 'Error "invalid application of non-function type object")
    )
)

; InferableTerm -> Context -> Int -> Result(TypeObject)
(define (check-type-inferable-term term context num-encountered-bindings)
    (annotated-match inferable-term
      ('Ann checkable-term type-object -> (bind-result
                                            ; First we make sure the type is well-formed
                                            (check-type-well-formed context type-object 'HasKind)
                                            ; Then we make sure that the checkable term itself has the type we said it did
                                            (check-type-checkable-term checkable-term context type-object num-encountered-bindings)
                                          ))
      ('Free name ->
        (let ([lookup-result (assoc name ctx)])
          (if (and
                lookup-result
                (equal? (cadr lookup-result) 'HasType)
              )
            (cons 'OK (cdr lookup-result))
            (cons 'Error "unknown identifier")
          )))
      ('Bound i -> (list-ref env i))
      ('Apply term1 term2 ->
        ; We don't use  bind-result here because we want to inspect term1's type and not  just pass it along.
        (let  ([term1-result (check-type-checkable-term term1 context type-object num-encountered-bindings)])
          (if (equal? (car term1-result) 'OK)
              (let ([term1-type  (cdr term1-result)])
                (if (equal? 'Fun (car term1-type))
                  (check-type-checkable-term  (cddr term1-type))
                  (cons 'Error "did not get a function type when looking up an Apply term")
                )
              )
              term1-result
           )
        )
    )
  )
)


; CheckableTerm -> Context -> TypeObject -> Int -> Result()
(define (check-type-checkable-term term context provided-type num-encountered-bindings)

)