(library (untyped-banneker utils)
(export
  ; LIST T -> boolean WHERE T : equal>?
  two-in-a-row?
  ; String -> Char -> LIST String
  split-string
  ; String -> (Char -> boolean) -> LIST String
  split-string-core
  ; LIST T -> (T -> boolean) -> LIST (LIST T)
  split-core
)
(import (rnrs))

; CPS two-in-a-row from Little/Seasoned Schemer
; LIST T -> (T,T -> boolean) -> boolean
(define (two-in-a-row? lat comparer)
           ; helper : LIST T -> T -> boolean
  (letrec ([helper (lambda (ls builder)
      (cond
        [(null? ls) #f]
        [(comparer (car ls) builder) #t]
        [else (helper (cdr ls) (car ls))]
      )
    )
  ])
(helper lat '()))
)

; Recursive CPS split method
; LIST T -> (T -> bool) -> LIST (LIST T)
(define (split-core ls comparison-method)
  (letrec ([
    builder ; helper function for recursively building a list of lists
      ; LIST T -> (LIST (LIST T) -> LIST (LIST T)) -> LIST (LIST T)
      (lambda (lis list-of-list-cont)
        (cond
          ; if lis is empy apply the continuation to the empty list
          ; to "unwind" the calls
          [(null? lis) (list-of-list-cont '(()))]
          ; If the head of the list matches the comparison method,
          ; build the continuation by appending an empty list to the new list of lists
          ; List elements will be added to this new sublist unttil either
          ; the comparison-method returns #t or the list is empty
          [(comparison-method (car lis))
            (builder (cdr lis) (lambda (l) (list-of-list-cont (cons '() l))))]
          [else
            ; add the head of lis to the head of the head of the sublist
            ; (in the continuation so it preserves order)
            (builder
              (cdr lis)
              (lambda (l)
                (list-of-list-cont
                  (cons
                    (cons (car lis) (car l))
                    (cdr l)
                  )
                )
              )
            )]
        )
      )
  ])
  (builder ls (lambda (l) l))
  )
)

; String -> (Char -> bool) -> List String
(define (split-string-core string char-comp-method)
    (map list->string (split-core (string->list string) char-comp-method))
)

; String -> Char -> LIST String
(define (split-string string split-char)
   (split-string-core string (lambda (x) (char=? x split-char))))
)



)