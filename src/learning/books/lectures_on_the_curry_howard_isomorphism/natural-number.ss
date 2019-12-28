(define natural-number
  (lambda (n)
    (cond
    [(= n 0) 'Z]
    (else (cons 'S (natural-number (- n 1))))
  )
))

(define natural-number->int
  (lambda (nat)
    (cond
      [(equal? nat 'Z) 0]
      [else (+ 1 (nat->int (cdr nat)))])))

(define natural-number-plus
  (lambda (natA natB)
    (cond
      [(equal? natA 'Z) natB]
      [else (cons 'S (nat-plus (cdr natA) natB))]
    )
  )
)

(define natural-number-multiply
  (lambda (natA natB)
    (cond
      [(equal? natA 'Z) 'Z]
      [(equal? natA '(S . Z)) natB]
      [else (natural-number-plus natB (natural-number-multiply (cdr natA) natB))]
    )
  )
)

(define natural-number-exp
  (lambda (base exponent)
    (cond
      [(equal? exponent 'Z) '('S 'Z)] ; ignore 0^0, maybe should throw an error.
      [(equal? exponent '(S . Z)) base]
      [else (natural-number-multiply base (natural-number-exp base (cdr exponent)))]
    )
  )
)


; (define bounded-numeric-function
;   (lambda (bound )))
