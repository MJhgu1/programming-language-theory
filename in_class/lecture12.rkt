#lang plai

(define-type FunDef
	[fundef 	(fun-name symbol?)
			(arg-name symbol?)
			(body FAE?)])
(define-type FAE
    [num    (n number?)]
    [add     (lhs FAE?) (rhs FAE?)]
    [sub     (lhs FAE?) (rhs FAE?)]
    [with    (name symbol?) (named-expr FAE?) (body FAE?)]
    [id         (name symbol?)]
    [fun      (param symbol?) (body FAE?)]
    [app     (ftn FAE?) (arg FAE?)])

(define (num-op op)
     (lambda (x y)
          (num (op (num-n x) (num-n y)))))
(define num+ (num-op +))
(define num- (num-op -))

(define-type FAE-Value
    [numV         (n number?)]
    [closureV    (param symbol?) (body FAE?) (ds DefrdSub?)])


; interp : WAE DefrdSub -> number

      (define-type DefrdSub
            [mtSub]
            [aSub      (name symbol?)
                            (value number?)
                            (saved DefrdSub?)])

; lookup: symbol DefrdSub -> number
(define (lookup name ds)
      (type-case DefrdSub ds
            [mtSub       ()                  (error 'lookup "free identifier")]
            [aSub      (i v saved)      (if (symbol=? i name)
                                             v
                                            (lookup name saved))]))

; parse: sexp -> FWAE
; purpose: to convert sexp to FWAE
(define (parse sexp)
   (match sexp
        [(? number?)                (num sexp)]
        [(list '+ l r)                     (add (parse l) (parse r))]
        [(list '- l r)                      (sub (parse l) (parse r))]
        [(list 'with (list i v) e)  (app (fun ((parse i) (parse e))) (parse v))]
        [(? symbol?)                (id sexp)]
        [(list 'fun (list p) b)     (fun p (parse b))]  ;; e.g., {fun {x} {+ x 1}}
        [(list f a)                       (app (parse f) (parse a))]
        [else                             (error 'parse "bad syntax: ~a" sexp)]))

; interp: FAE DefrdSub -> FAE-Value
(define (interp fae ds)
    (type-case FAE fae
        [num   (n)      (numV n)]
       [add    (l r)    (num+ (interp l ds) (interp r ds))]
       [sub    (l r)    (num- (interp l ds) (interp r ds))]
       [id       (s)     (lookup s ds)]
       [fun     (p b)  (closureV p b ds)]
       [app    (f a)   (local [(define f-val (interp f ds))
                                      (define a-val (interp a ds))]
                               (interp (closureV-body f-val)
                                           (aSub (closureV-param f-val)
                                                      a-val
                                                      (closureV-ds f-val))))]))

(closureV 'y (add (id 'x) (id 'y)) (aSub 'x (numV 3) (mtSub)))

(interp (app (fun 'x (app (id 'f) (num 4))) (num 5))
                   (aSub 'f (closureV 'y (add (id 'x) (id 'y))  (aSub 'x (numV 3) (mtSub)))
                                (aSub 'x (numV 3) (mtSub))))

(closureV 'x (app (id 'f) (num 4)) 
(aSub 'f (closureV 'y (add (id 'x) (id 'y))
 (aSub 'x (numV 3) (mtSub))) 
 (aSub 'x (numV 3) (mtSub))))


(interp (app (id 'f) (num 4)) 
                   (aSub 'x (numV 5) 
                   (aSub 'f (closureV 'y (add (id 'x) (id 'y)) (aSub 'x (numV 3) (mtSub)))
                    (aSub 'x (numV 3)(mtSub)))))


(interp (app (fun 'x (app (fun 'f (app (fun 'x (app (id 'f) (num 4))) (num 5))) (fun 'y (add (id 'x) (id 'y))))) (num 3)) (mtSub))
(interp (parse '{with {x 3} {with {f {fun {y} {+ x y}}} {with {x 5} {f 4}}}}) (mtSub))

