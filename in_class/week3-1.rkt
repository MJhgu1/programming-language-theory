#lang plai


(define-type AE
  [num (n number?)]
  [add (lhs AE?) (rhs AE?)]
  [sub (lhs AE?) (rhs AE?)]
  )

(define ae1 (add (sub (num 2) (num 1)) (num 4)))

;;parse : sexp->AE
;;to convert s-expressions into AEs in abstract syntax.
(define (parse sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(eq? (first sexp) '+) (add (parse (second sexp)) (parse (third sexp)))]
    [(eq? (first sexp) '-) (sub (parse (second sexp)) (parse (third sexp)))]))

(parse '(+ 3 3))
(parse '3)
(parse '{+ 3 4})
(parse '{- 4 3})
(parse '{+ {+ 4 3} {- 4 3}})

;; parse : sexp -> AE
;; to convert s-expressions into AEs
(define (parse1 sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(and (= 3 (length sexp)) (eq? (first sexp '+))) (add (parse1 (second sexp)) (parse1 (third sexp)))]
    [(and (= 3 (length sexp)) (eq? (first sexp '-))) (sub (parse1 (second sexp)) (parse1 (third sexp)))]
    [else (error 'parse "bad syntax: ~a" sexp)]))

;(parse1 '{+ 3 3 4})

(define (interp an-ae)
  (type-case AE an-ae
    [num (n) n]
    [add (l r) (+ (interp l) (interp r))]
    [sub (l r) (- (interp l) (interp r))]
    ))

(interp (parse '3))
(interp (parse '(+ 3 4)))
(interp (parse '(- (+ 3 4) 1)))
