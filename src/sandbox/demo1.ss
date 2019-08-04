;;; Data types ;;;

(define-enumeration SchemeCompileTimeAtom
    (int real bool string char) atom)

(define-)

(define-record-type TypeZero
    (fields id underlying-type) (nongenerative))

(define (f p)
  (define-record-type TypeZero
    (fields id underlying-type) (nongenerative))
  (if (eq? p 'make) (make-TypeZero 3 4) (TypeZero? p)))

; process-let-binding takes a list of tokens
; which appear in a source file after a "let",
; and builds an expression tree from them.
; Semantics for let:
;   - must be a valid expression
;   - MUST be prepended with a type (no inference here)
(define process-let-binding
    (lambda (rest-of-tokens)
        (cond
            [(null? rest-of-tokens) ])))

(define parse-list-of-tokens
    (lambda (ls)
        (cond
            [(null? ls) ls]
            [(string=? (car ls) "let")
                (list "let" (parse-list-of-tokens (cdr ls)))]
        )
    )
)