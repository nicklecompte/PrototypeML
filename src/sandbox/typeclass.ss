
;;
;;  Type classes for Scheme. Based on code from the comp.lang.scheme
;;  post by Andre van Tonder entitled "Typeclass envy".
;;
;;  Ported to Chicken Scheme by Ivan Raikov.
;;
;;  Copyright 2004-2018 Andre van Tonder, Ivan Raikov.
;;
;;  Permission is hereby granted, free of charge, to any person
;;  obtaining a copy of this software and associated documentation
;;  files (the "Software"), to deal in the Software without
;;  restriction, including without limitation the rights to use, copy,
;;  modify, merge, publish, distribute, sublicense, and/or sell copies
;;  of the Software, and to permit persons to whom the Software is
;;  furnished to do so, subject to the following conditions:
;;
;;  The above copyright notice and this permission notice shall be
;;  included in all copies or substantial portions of the Software.
;;
;;  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;  HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;  WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;;  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;  DEALINGS IN THE SOFTWARE.
;;
;;

(module typeclass

	((define-class filter)
	 (with-instance cadr) import-instance
	 lambda=> define=>
	 )


;    (define-class <field-form> ...)

;    (define=> (<procedure-name> <class-form> ...) . body)

;    (lambda=> (<class-form> ...) . body)

;    (with-instance (<instance-form> ...) . body)

;    (import-instance <instance-form> ...)

;    <field-form> = field-label
;                 | (<superclass-name> field-label)

;    <class-form> = <class-name>
;                 | (<class-name> <prefix-symbol>)

;    <instance-form> = (<class-name> <instance-expr>)
;                    | (<class-name> <instance-expr> <prefix-symbol>)

(define-syntax define-class
  (er-macro-transformer
   (lambda (x r c)
    (let ((name   (cadr x))
	  (fields (cddr x)))
      (let ((k       (r 'k))
	    (args    (r 'args))
	    (formals (map (lambda (field) (gensym)) fields))
	    (supers  (filter pair? fields))
	    (labels  (map (lambda (field)
			    (match field
				   ((super label) label)
				   (label         label)))
			  fields))
	    (%cadr   (r 'cadr))
	    (%cddr   (r 'cddr))
	    (%begin   (r 'begin))
	    (%define  (r 'define))
	    (%lambda  (r 'lambda))
	    (%let     (r 'let))
	    (%define-syntax  (r 'define-syntax))
	    (%er-macro-transformer  (r 'er-macro-transformer))
	    )

	`(,%begin
	   (,%define ,(string->symbol
		       (string-append "make-" (symbol->string name)))
	     (,%lambda ,formals
	       (,%lambda (,k) (,k . ,formals))))
	   (,%define-syntax ,name
            (,%er-macro-transformer
             (,%lambda (x r c)
                       (let ((k    (cadr x))
                             (args (cddr x)))
                         `(,k "descriptor" ,',supers ,',labels . ,args)))))))
    ))
  ))

(define-syntax with-instance
  (er-macro-transformer
  (lambda (x r c)
    (let ((body (cdr x))
	  (%let (r 'let)))
      (match body
	     ((() . exps)
	      `(,%let () . ,exps))

	     ((((name instance) . rest) . exps)
	      `(,name with-instance
		      ,name "" ,instance ,rest . ,exps))

	     ((((name instance prefix) . rest) . exps)
	      `(,name with-instance
		      ,name ,(symbol->string prefix)
		      ,instance ,rest . ,exps))

	     (("descriptor" supers labels name pre instance rest . exps)
	      (let ((pre-labels
		     (map (lambda (label)
			    (string->symbol
			     (string-append pre (symbol->string label))))
			  labels))
		    (super-bindings
		     (map (lambda (class-label)
			    `(,(car class-label)
			      ,(string->symbol
				(string-append pre
					       (symbol->string
						(cadr class-label))))
			      ,(string->symbol pre)))
			  supers)))
		`(,instance (lambda ,pre-labels
			      (with-instance ,super-bindings
				    (with-instance ,rest . ,exps))))))
	     (else
	      (error 'with-instance "with-instance argument mismatch: " body))
      ))
    ))
  )

(define-syntax import-instance
  (er-macro-transformer
  (lambda (x r c)
    (let ((bindings (cdr x))
	  (%begin     (r 'begin)))
      (match bindings
	     (()
	      "Bindings imported")

	     (((name instance) . rest)
	      `(,name import-instance
		      ,name "" ,instance ,rest))

	     (((name instance prefix) . rest)
	      `(,name import-instance
		      ,name ,(symbol->string prefix)
		      ,instance ,rest))

	     (("descriptor" supers labels name pre instance rest)
	      (let ((pre-labels.temps
		     (map (lambda (label)
			    (cons
			     (string->symbol
			      (string-append pre (symbol->string label)))
			     (gensym)))
			  labels))
		    (super-bindings
		     (map (lambda (class-label)
			    `(,(car class-label)
			      ,(string->symbol
				(string-append pre
					       (symbol->string
						(cadr class-label))))
			      ,(string->symbol pre)))
			  supers)))

		`(,%begin ,@(map (lambda (pre-label.temp)
				 `(define ,(car pre-label.temp) #f))
			       pre-labels.temps)
			(,instance (lambda ,(map cdr pre-labels.temps)
				     ,@(map (lambda (pre-label.temp)
					      `(set! ,(car pre-label.temp)
						     ,(cdr pre-label.temp)))
					    pre-labels.temps)))
			(import-instance . ,super-bindings)
			(import-instance . ,rest))))))
    ))
  )

(define-syntax lambda=>
  (er-macro-transformer
  (lambda (x r c)
    (let ((quals (cadr x))
	  (body (cddr x))
	  (%lambda (r 'lambda))
	  (%with-instance (r 'with-instance)))
      (let ((quals-binds (map (lambda (qual)
				(match qual
				       ((cls prefix) (list cls (gensym) prefix))
				       (cls          (list cls (gensym)))))
			      quals)))
	`(,%lambda ,(map cadr quals-binds)
		   (,%with-instance ,quals-binds
				  . ,body))))
    ))
  )


(define-syntax define=>
  (er-macro-transformer
  (lambda (x r c)
    (let ((name.quals (cadr x))
	  (body (cddr x))
	  (%define (r 'define)))
      (let ((name  (car name.quals))
	    (quals (cdr name.quals)))
 	`(,%define ,name (lambda=> ,quals . ,body))))
    ))
  )
)
