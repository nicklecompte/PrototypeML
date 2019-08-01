;;; parsing-combinators.scm
;;; An implementation of parsing combinators
;;;
;;; Programmer: Mayer Goldberg, 2013

(define get-callback
  (lambda (fs)
    (cond ((null? fs) (lambda (x) x))
	  ((null? (cdr fs)) (car fs))
	  (else (error 'get-callback "Only one callback!")))))

(define test
  (lambda (parser tokens)
    (parser tokens
	    (lambda (pe tokens)
	      `((expression: ,pe) (tokens left: ,tokens)))
	    (lambda () 'no-match!))))

(define const
  (lambda (match? . cbs)
    (let ((cb (get-callback cbs)))
      (lambda (s match fail)
	(cond ((null? s) (fail))
	      ((match? (car s))
	       (match (cb (car s)) (cdr s)))
	      (else (fail)))))))

(define caten
  (letrec ((loop
	    (lambda (parsers)
	      (if (null? parsers)
		  (lambda (s match fail)
		    (match '() s))
		  (let ((parser1 (car parsers))
			(parser2 (loop (cdr parsers))))
		    (lambda (s match fail)
		      (parser1 s
		       (lambda (e s)
			 (parser2 s
			  (lambda (es s)
			    (match (cons e es) s))
			  fail))
		       fail)))))))
    (lambda parsers
      (lambda cbs
	(let ((parser (loop parsers))
	      (cb (if (null? cbs) list (get-callback cbs))))
	  (lambda (s match fail)
	    (parser s
	     (lambda (es s) (match (apply cb es) s))
	     fail)))))))

(define disj
  (letrec ((loop
	    (lambda (parsers)
	      (if (null? parsers)
		  (lambda (s match fail)
		    (fail))
		  (let ((parser1 (car parsers))
			(parser2 (loop (cdr parsers))))
		    (lambda (s match fail)
		      (parser1 s
		       match	       
		       (lambda ()
			 (parser2 s match fail)))))))))
    (lambda parsers
      (lambda cbs
	(let ((parser (loop parsers))
	      (cb (get-callback cbs)))
	  (lambda (s match fail)
	    (parser s
	     (lambda (e s)
	       (match (cb e) s))
	     fail)))))))

(define star
  (lambda (parser . cbs)
    (let ((cb (get-callback cbs)))
      (letrec ((special-star
		(lambda $
		  (apply
		   ((disj
		     ((caten parser special-star) cons)
		     ((caten))))
		   $))))
	((disj special-star) cb)))))

(define plus
  (lambda (parser . cbs)
    (let ((cb (get-callback cbs)))
      ((disj ((caten parser (star parser)) cons))
       cb))))

(define maybe
  (lambda (parser . cbs)
    (let ((cb (get-callback cbs)))
      ((disj ((disj parser) list)
	     ((caten)))
       cb))))

(define diff
  (lambda (parser-in parser-out)
    (lambda (s match fail)
      (parser-out s
       (lambda _ (fail))
       (lambda () (parser-in s match fail))))))

;;;

(define ^char
  (lambda (char=?)
    (lambda (ch)
      (const (lambda (c) (char=? c ch))))))

(define char (^char char=?))
(define char-ci (^char char-ci=?))

(define ^^char-between
  (lambda (char<=?)
    (lambda (char-from char-to)
      (const
       (lambda (ch)
	 (and (char<=? char-from ch)
	      (char<=? ch char-to)))))))

(define ^one-of-chars
  (lambda (string . cbs)
    (let ((cb (get-callback cbs)))
      ((apply disj (map char (string->list string))) cb))))

(define <any-char> (const char?))

(define ^word
  (lambda (char=?)
    (lambda (string . cbs)
      (let ((cb (get-callback cbs)))
	((disj
	  ((apply caten
		  (map (lambda (ch) (const (lambda (c) (char=? ch c))))
		    (string->list string)))
	   (lambda s
	     (cb (list->string s))))))))))

(define word (^word char=?))

(define word-ci (^word char-ci=?))
