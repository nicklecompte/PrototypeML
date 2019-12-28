;;; Helper functions ;;;

(define list-starts-with?
  (lambda (inputlist sublist)
      (cond
          [(null? sublist) #t]
          [(null? inputlist) #f]
          [(atom? sublist) (equal? sublist (car inputlist))]
          [else (and (equal? (car sublist) (car inputlist))
                       (list-starts-with? (cdr inputlist) (cdr sublist)))])))

(define remove-from-start-of-list
  (lambda (inputlist sublist)
    (cond
      [(null? sublist) inputlist]
      [(null? inputlist) inputlist]
      [(list-starts-with? inputlist sublist) (remove-from-start-of-list (cdr inputlist) (cdr sublist))]
      [else inputlist])))

(define list-split
  (lambda (inputlist sublist)
    (letrec ([helper (lambda (ls matchls buildlsls)
                    (cond
                      [(null? ls) buildlsls]
                      [(null? matchls) buildlsls]
                      [(list-starts-with? ls matchls) (helper (remove-from-start-of-list ls matchls) matchls (cons '() buildlsls))]
                      [else (helper (cdr ls) matchls (cons (cons (car ls) (car buildlsls)) (cdr buildlsls)))]
                      ))])
        (let ([rev (helper inputlist sublist (list '()) )])
          (reverse (map reverse rev))))))

(define string-split
  (lambda (inputstr substr)
    (let ([listresult (list-split (string->list inputstr) (string->list substr))])
            (map list->string listresult))))


;;; Data types ;;;

;
(define-enumeration SchemeCompileTimeAtom
    (int real bool string char) atom)

; PrimitiveTypes are inherent to any PrototypeML language in the compiler.
; Values in PrototypeML with PrimitiveType are evaluated
; in a direct, simple Scheme expression.
(define-enumeration PrimitiveType
  (MLInt MLFloat MLBool MLString MLChar) primtype)

(define parse-primitive-type
  (lambda (token)
    (case token
      [("str") (PrimitiveType MLString)]
      [("int") (PrimitiveType MLInt)]
      [("bool") (PrimitiveType MLBool)]
      [("float") (PrimitiveType MLFloat)]
      [("char") (PrimitiveType MLChar)]
      [else #f])))

; PrototypeML type signatures:
; Type
; Type -> Type

(define parse-type-signature
  (lambda (token)
    (case token)))

(define-record-type MLRecordTypeElement
  (fields property-name type value) (nongenerative))

; An MLRecordType is simply an association list of MLRecordTypeElements.
; For thread-safety we really don't want to use a hashtable.
; Ideally with record there won't be enough fields for compile times
; to be too terribly slow.

; let MyRecordType : Type =
;   record {
;     name : String
;     hash : Int
;
; }

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