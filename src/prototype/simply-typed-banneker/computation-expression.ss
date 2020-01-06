(library (simply-typed-banneker computation-expression)

(export ())
(import ())

(define-record-type result (fields ok error))

(define (chain-result-functions lsfuncs)
  (cond
    [(null? lsfuncs) (lambda (x) (make-result x '()))]
    [else
      (lambda (x)
        (cond
         [(null? (result-ok x)) x]
         [else ((chain-result-functions (cdr lsfuncs)) ((car lsfuncs) (result-ok x)))]
        )
      )
    ]
  )
)

(define-syntax execute-result-chain
  (syntax-rules ()
    [(_) '()]
    [(_ e f) (e f)]
    [(_ (e f ...) h)
      (let ([res (e h)])
        (cond
          [(null? (result-ok res)) (result-error res)]
          [else (execute-result-chain (f ... (result-ok res))]
        )
      )
    ]
  )
)

(define (ex-fun-1 int-val)
  (if (= int-val 0)
    (make-result '() "can't divide by zero")
    (make-result (/ 20 int-val) '())
  )
)

(define (ex-fun-2 int-val)
  (if (= int-val 5)
    (make-result '() "5 is bad for some reason")
    (make-result (- 10 int-val) '())
  )
)


)

; Inspired by F#, we introduce a *computation expression* as an alternative con-
; -struct to monadic / monoidal / etc typeclasses from Haskell and Scala.
; The syntax for define-computation-expression is
;
;   (define-computation-expression )


; (define-syntax define-computation-expression)

; )

; (define-syntax define-structure
;   (lambda (x)
;     (define gen-id
;       (lambda (template-id . args)
;         (datum->syntax template-id
;           (string->symbol
;             (apply string-append
;               (map (lambda (x)
;                      (if (string? x)
;                          x
;                          (symbol->string (syntax->datum x))))
;                    args))))))
;     (syntax-case x ()
;       [(_ name field ...)
;        (with-syntax ([constructor (gen-id #'name "make-" #'name)]
;                      [predicate (gen-id #'name #'name "?")]
;                      [(access ...)
;                       (map (lambda (x) (gen-id x #'name "-" x))
;                            #'(field ...))]
;                      [(assign ...)
;                       (map (lambda (x)
;                              (gen-id x "set-" #'name "-" x "!"))
;                            #'(field ...))]
;                      [structure-length (+ (length #'(field ...)) 1)]
;                      [(index ...)
;                       (let f ([i 1] [ids #'(field ...)])
;                         (if (null? ids)
;                             '()
;                             (cons i (f (+ i 1) (cdr ids)))))])
;          #'(begin
;              (define constructor
;                (lambda (field ...)
;                  (vector 'name field ...)))
;              (define predicate
;                (lambda (x)
;                  (and (vector? x)
;                       (= (vector-length x) structure-length)
;                       (eq? (vector-ref x 0) 'name))))
;              (define access
;                (lambda (x)
;                  (vector-ref x index)))
;              ...
;              (define assign
;                (lambda (x update)
;                  (vector-set! x index update)))
;              ...))])))

; The constructor accepts as many arguments as there are fields in the structure
; and creates a vector whose first element is the symbol name and whose remain-
; -ing elements are the argument values. The type predicate returns true if its
; argument is a vector of the expected length whose first element is name.

; Since a define-structure form expands into a begin containing definitions, it
; is itself a definition and can be used wherever definitions are valid.

; The generated identifiers are created with datum->syntax to allow the identif-
; -iers to be visible where the define-structure form appears.

; The examples below demonstrate the use of define-structure.

; (define-structure tree left right)
; (define t
;   (make-tree
;     (make-tree 0 1)
;     (make-tree 2 3)))

; t <graphic> #(tree #(tree 0 1) #(tree 2 3))
; (tree? t) <graphic> #t
; (tree-left t) <graphic> #(tree 0 1)
; (tree-right t) <graphic> #(tree 2 3)
; (set-tree-left! t 0)
; t <graphic> #(tree 0 #(tree 2 3))