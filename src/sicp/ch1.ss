(define sum-of-squares
  (lambda (a b) (+ (* a a) (* b b))
  )
)

(define-syntax uncurry2
  (syntax-rules ()
    ((_ f arg) (f (car arg) (car (cdr arg)))))
)

(define two-largest
  (lambda (ls)
    (letrec ([helper (lambda (ls a b)
      (cond
        [(null? ls) (list a b)]
        [(and (>= a (car ls)) (>= b (car ls))) (helper (cdr ls) a b)]
        [(and (>= a (car ls)) (< b (car ls))) (helper (cdr ls) a (car ls))]
        [(and (< a (car ls)) (>= b (car ls))) (helper (cdr ls) b (car ls))]
        [(and (< a (car ls)) (< b (car ls))) (cond
                                                [(>= a b) (helper (cdr ls) a (car ls))]
                                                [(> b a) (helper (cdr ls) b (car ls))]
        )]
      )
    )])
    (cond
      [(null? ls) '()]
      [(null? (cdr ls)) (car ls)]
      [else (helper (cddr ls) (car ls) (cadr ls))]
    )
  )
))

(define ex-one-three
  (lambda (a b c)
      (uncurry2 sum-of-squares (two-largest (list a b c)))
  )
)