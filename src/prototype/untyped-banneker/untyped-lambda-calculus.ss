(library (untyped-banneker untyped-lambda-calculus)

(export
  lambda-preterm?
  alpha-preterm?
)
(import (untyped-banneker utils))

; Alpha preterms that are parsed from untyped-banneker
; are turned to Scheme symbols or Scheme primitives for CPU-ish types.
; Define the symbol 'blambda to be the lambda term.
(define lambda-token 'blambda)

; Util for seeing if a preterm is a lambda preterm.
(define (lambda-preterm? preterm)
  (and
    (pair? preterm)
    (equal? lambda-token (car preterm))
    (symbol? (cdr preterm))
    (not (equal? lambda-token (cdr preterm)))
  )
)


(define-enumeration preterm-type
  (constant variable application lambda)
  preterm-description)

; The type of constants within the system.
; These include primitive types (ints/floats/strings),
; along with things that are called directly by Chez
; with a thin untyped-banneker wrapper (for instance,
; primitive arithmetic)
(define-enumeration constant-type
  ; datatypes
  (integer float string char
  ; infix  operations (we won't be using prefix notation)
  plus minus times divide modulo
  ; print to console / interpreter
  print
  ; ffi for Chez functions
  ffi)
  constant-types)


; Scheme object -> Union[constant-type,#f]
; Returns #f if the object maybe-preterm is not
; one of a few constant symbols
(define (classify-constant-operation maybe-preterm)
  (if (symbol? maybe-preterm)
    (cond
      [(equal? maybe-preterm 'plus) (constant-type plus)]
      [(equal? maybe-preterm 'times) (constant-type times)]
      [(equal? maybe-preterm 'minus) (constant-type minus)]
      [(equal? maybe-preterm 'times) (constant-type times)]
    )
    #f
  )
)

; EXP -> UNION[constant-type, False] [returns #f if maybe-preterm isn't a contant]
(define (classify-constant maybe-preterm)
    (cond
      [(integer? maybe-preterm) (constant-type integer)]
      [(fixnum? maybe-preterm) (constant-type integer)]
      [(flonum? maybe-preterm) (constant-type float)]
      [(string? maybe-preterm) (constant-type string)]
      [(char? maybe-preterm) (constant-type char)]
      [(symbol? maybe-preterm)]
      [else #f]
    )
)

(define (classify-alpha-preterm maybe-preterm)
  (cond
    []
  )
)

; an alpha preterm after parsing is either
; a primitive Scheme type like an int, flonum, etc
(define (alpha-preterm? maybe-preterm)
    (or
        (and
            (symbol? maybe-preterm)
            (not (equal? lambda-token maybe-preterm))
        )
        (string? maybe-preterm)
        (number? maybe-preterm)
        (and
            (pair? maybe-preterm)
            (or
                (and
                (lambda-preterm? (car maybe-preterm))
                (alpha-preterm? (cdr maybe-preterm))
                )
                (and
                (alpha-preterm? (car maybe-preterm))
                (alpha-preterm? (cdr maybe-preterm))
                )
            )
        )
    )
)
)