; Nick LeCompte - 2019
; This software is free and open source. Please see LICENSE.md.
;
; The lexer module of untyped-banneker processes string data
; and translates them into lists of lists of "raw" s-expressions.
; Syntax:
; Only allow alpha preterms to be defined (no fancy define defun etcs)
; Lambdas are denoted by
;   fun arg1 ... ->
;       body
; yes this is whitespace delimited deal with it.
; whitespace delimiters are either 2 spaces, \t, or lists of these tokens.
(library (untyped-banneker lexer)
(export banneker-whitespace?)
(import (untyped-banneker utils))

(define text-tokens
  '(
      "let"
      "in"
      "="
      "if"
      "then"
      "else"
      "mutable"
      ":"
      "->"
      "<-"
  )
)

(define whitespace-characters
  '(
      #\tab
      #\space
  )
)

(define (nested-sexp-starts-token str)
  (or
    (string=? str "in")
    (string=? str "then")
    (string=? str "else")
    (string=? str "if")
  )
)

(define (get-starting-whitespace-count character-list)
  (cond
    [(< (length character-list) 2) 0]
    [(char=? #\tab (car character-list)) 1 + (get-starting-whitespace-count (cdr character-list))]
    [(and
       (char=? #\space (car character-list))
       (char=? #\space (cadr character-list))
      ) (+ 1 (get-starting-whitespace-count (cddr character-list)))]
    [else 0]
  )
)

(define (starts-with-whitespace? arg)
  (and
    (> (length arg) 1)
    (or

    )
    )
  )
)

;; LIST String -> boolean
(define (banneker-whitespace? arg)
  (
      (or
        (char=? arg #\tab)
        (char=? arg #\space)
        ()
      )
  )
)

;; String -> LIST [LIST String]
(define (split-to-expressions body-text))

)