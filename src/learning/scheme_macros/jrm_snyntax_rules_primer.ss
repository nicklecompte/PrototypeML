; http://www.phyast.pitt.edu/~micheles/syntax-rules.pdf
; JRM's Syntax-rules primer for the merely eccentric
; Transcribed by N LeCompte 2019

; syntax-rules provides very pwoerful pattern matching and
; destructuring facilities. With very simple macros,
; however, most of this ppwer is unused.
; Here is an example:
(define-syntax nth-value
  (syntax-rules ()
    ((nth-value n values-producing-form)
     (call-with-values
       (lambda () values-producing-form)
       (lambda all-values
         (list-ref all-values n))))))