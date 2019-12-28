; are you acquainted with member?
(define my-member?
  (lambda (a lat)
    (cond
      [(null? lat) #f]
      [else (or (eq? a (car lat)) (my-member? a (cdr lat)))]
    )))

(define two-in-a-row?
  (lambda (lat)
    (letrec ([helper (lambda (ls builder)
    (cond
      [(null? ls) #f]
      [(equal? (car ls) builder) #t]
      [else (helper (cdr ls) (car ls))]
      ))
    ])
    (helper lat '()))
  )
)