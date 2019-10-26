#lang plai


(define-type WAE
	[num (n number?)]
	[add (lhs WAE?) (rhs WAE?)]
	[sub (lhs WAE?) (rhs WAE?)]
	[with (name symbol?) (named-expr WAE?) (body WAE?)]
	[id (name symbol?)])

(define (parse sexp)
  (match sexp
   	[(? number?) 			(num sexp)]
   	[(list '+ l r)			(add (parse l) (parse r))]
   	[(list '- l r)			(sub (parse l) (parse r))]
    	[(list 'with (list i v) e)	(with i (parse v) (parse e))]
	[(? symbol?)			(id sexp)]
   	[else (error 'parse "bad syntax:~a" sexp)]))


(parse '{+ {- 3 4} 7})