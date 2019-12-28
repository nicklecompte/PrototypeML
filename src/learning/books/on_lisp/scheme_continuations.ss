; A continuation is a function representing the future of a computation.
; Whenever an expression is evaluated, something is waiting for the value it
; will return. For example:
;
;   (/ (- x 1) 2)
;
; the outer / is waiting for the value in (- x 1), its caller is waiting for its
; value, and so on, all the way to the top level print/readline/etc that
; invoked the function.
;
; We can think of the continuation at any given time as a function of one
; argument. Above, the continuation would be
;
;   (lambda (val) (/ val 2))
;
; The below example builds a list whose last element is the value returned
; by a call/cc expression:
(define frozen)
(append '(the call/cc returned)
        (list (call/cc
                (lambda (cc)
                   ; first call/cc takes the current continuation
                   ; and sets the global variable frozen to whatever that is
                  (set! frozen cc)
                  ; then returns 'a
                  'a)
              )
        )
)
; The continuation is (lambda (x) (append '(the call/cc returned) (list x)))
; The value frozen was set to this function
; so when we call
(frozen 'kitten)
; this will return '(the call/cc returned kitten).
;
; call/cc contains context about its continuation, not just a single simple
; lambda. For instance
(frozen 'dog)
; will return '(the call/cc returned dog). But
(+ 1 (frozen 'dog))
; will return '(the call/cc returned dog) - the (+ 1) is ignored
; (frozen 'dog) returns up the call stack, but specifically the call stack that
; was pending at the time frozen was first set - it goes to list, then append,
; and bypasses the (+ 1) since that was not in the stack.
;
; But continuations do not get unique copies of the stack. They may share
; variables with other continuations, or with the computation currently in
; progress. For example, these two continuations share the same stack:
;
(define froz1)
(define froz2)
(let ((x 0))
  (call/cc
    (lambda (cc)
      (set! froz1 cc)
      (set! froz2 cc)
    )
  )
  (set! x (+ 1 x))
  x
)
; Here, froz1 and froz2 are [fill in the details]

; Trees can be represented as nested lists.

(define t1
  '(a (b (d h)) (c e (f i ) g))
)
(define t2
  '(a (2 (3 6 7) 4 5))
)
; Using call/cc can make a depth-first traversal implementation much easier:
; First the naive recursive implementation
(define (dft tree)
  (cond [(null? tree) '()]
        [(not (pair? tree)) (write tree)]
        [else
          (dft (car tree))
          (dft (cdr tree))
        ]
  )
)

; mutable state
(define *saved* ())

(define (dft-node tree)
  (cond
    [(null? tree) (restart)]
    ; walk this node
    [(not (pair? tree)) tree]
    [else (call/cc
            (lambda (cc)
              (set! *saved* (cons
                    ; update the continuations saved in saved
                    ;
                    (lambda () (cc (dft-node (cdr tree))))
                    *saved*))
              (dft-node (car tree))))]))

(define (restart)
  (if (null? *saved*) 'done
    (let [(cont (car *saved*))]
      (set! *saved* (cdr *saved*))
      (cont))
  )
)

(define (dft2 tree)
  (set! *saved* '())
  (let ((node (dft-node tree)))
    (cond [(eq? node 'done) '()]
          [else (write node) (restart)]
    )
  )
)