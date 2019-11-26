#lang plai

;Problem 1,2:
;Solved by myself: Y
;Time taken: about 3days
;[test] (test (run '{rec {count {fun {n} {if0 n 0 {+ 1 {count {- n 1}}}}}} {count 8}} (mtSub)) (numV 8))
;       (test (run '{rec {fac {fun {n} {if0 n 1 {* n {fac {- n 1}}}}}}{fac 3}} (mtSub)) (numV 6))
;       (test (run '{{fun {f} {f 1}} {fun {x} {+ x 1}}} (mtSub)) (numV 2))
;       (test (run '{{fun {x} {+ 1 x}} 10} (mtSub)) (numV 11))
;       (test (run '{{fun {x} x} 1} (mtSub)) (numV 1))
;       (test (run '{{fun {x} {+ x x}} {+ 1 {{fun {y} 2} 1}}} (mtSub)) (numV 6))
;       (test (run '{{fun {x} 0} {+ 1 {fun {y} 2}}} (mtSub)) (numV 0)) 



;[contract] : is it RCLFAE?
;[purpose] : Discriminate type
(define-type RCLFAE
    [num (n number?)]
    [add (lhs RCLFAE?) (rhs RCLFAE?)]
    [sub (lhs RCLFAE?) (rhs RCLFAE?)]
    [mul (lhs RCLFAE?) (rhs RCLFAE?)]
    [id (name symbol?)]
    [fun (param symbol?) (body RCLFAE?)]
    [app (fun-expr RCLFAE?) (arg-expr RCLFAE?)]
    [if0 (test-expr RCLFAE?)
           (then-expr RCLFAE?) (else-expr RCLFAE?)]
    [rec (name symbol?) (named-expr RCLFAE?) (fst-call RCLFAE?)])

;[contract] : is it DefrdSub?
;[purpose] : Discriminate type
(define-type DefrdSub
    [mtSub]
    [aSub         (name symbol?)
                       (value RCLFAE-Value?)
                       (ds DefrdSub?)]
    [aRecSub  (name symbol?)
                       (value-box (box/c RCLFAE-Value?))
                       (ds DefrdSub?)])
;[contract] : is it RCLFAE-Value?
;[purpose] : Discriminate type
(define-type RCLFAE-Value
    [numV        (n number?)]
    [closureV   (param symbol?) (body RCLFAE?) (ds DefrdSub?)]
    [exprV      (expr RCLFAE?) (ds DefrdSub?)
                            (value (box/c (or/c false RCLFAE-Value?)))])

;[contract] : RCLFAE-Value -> RCLFAE-Value
;[purpose] : implement exprV 
(define (strict v)
    (type-case RCLFAE-Value v
        [exprV (expr ds v-box)
                     (if (not (unbox v-box))
                          (local [(define v (strict (interp expr ds)))]
                              (begin (set-box! v-box v)
                                           v))
                          (unbox v-box))] 
        [else v]))



;[contract] : symbol DefrdSub -> RCLFAE-Value
;[purpose] : To found value
(define (lookup name ds)
    (type-case DefrdSub ds
        [mtSub  () (error "free variable")]
        [aSub    (sub-name val rest-ds)
                                  (if (symbol=? sub-name name)
                                        val
                                        (lookup name rest-ds))]
        [aRecSub (sub-name val-box rest-ds)
                          (if (symbol=? sub-name name)
                                    (unbox val-box)
                               (lookup name rest-ds))]))

;[contract] :  RCLFAE-Value -> boolean
;[purpose] : Discriminate if n is 0
(define (numzero? n)
    (zero? (numV-n n)))

;[contract] : RCLFWAE RCLFWAE -> RCLFWAE
;[purpose] : calculate num-op
(define (num-op op)
     (lambda (x y)
          (numV (op (numV-n (strict x)) (numV-n (strict y))))))

;[contract] : RCLFAE RCLFAE -> RCLFAE
;[purpose] : convert num-op to operations
(define num+ (num-op +))
(define num- (num-op -))
(define num* (num-op *))

;[contract] : sexp -> parse -> interp
;[purpose] : convert concrete syntax to abstract sytax, parse and interp
(define (run sexp ds)
     (interp (parse sexp) ds))

;[contract] : sexp->RCLFAE DefrdSub
;[purpose] : convert concrete syntax to abstract sytax
(define (parse sexp)
   (match sexp
        [(? number?)             (num sexp)]
        [(list '+ l r)                  (add (parse l) (parse r))]
        [(list '- l r)                   (sub (parse l) (parse r))]
        [(list '* l r)                   (mul (parse l) (parse r))]
        [(list 'with (list i v) e)   (app(fun i (parse e)) (parse v)) ]
        [(? symbol?)             (id sexp)]
        [(list 'fun (list p) b)    (fun p (parse b))]
     
        [(list 'if0 p b i)      (if0 (parse p) (parse b) (parse i))]
        [(list 'rec (list f e) b)   (rec f (parse e) (parse b))]
     
        [(list f a)            (app (parse f) (parse a))]
        [else                        (error 'parse "bad syntax: ~a" sexp)]
     ))


;[contract] : RCLFAE DefrdSub -> RCLFAE-Value
;[purpose] : consuming abstract sytax
(define (interp rcfae ds)
    (type-case RCLFAE rcfae
        [num (n) (numV n)]
        [add  (l r) (num+ (interp l ds) (interp r ds))]
        [sub  (l r) (num- (interp l ds) (interp r ds))]
        [mul (l r) (num* (interp l ds) (interp r ds))]
        [id     (name) (strict(lookup name ds))]
        [fun   (param body-expr) (closureV param body-expr ds)]
        [app  (f a) (local [(define ftn (strict(interp f ds)))
                            (define a-val (exprV a ds (box #f)))]
                                     (interp (closureV-body ftn)
                                                  (aSub (closureV-param ftn)
                                                              ;(interp a ds)
                                                              a-val
                                                              (closureV-ds ftn))))]
        [if0   (test-expr then-expr else-expr) 
                 (if (numzero? (interp test-expr ds))
                      (interp then-expr ds)
                      (interp else-expr ds))]
        [rec (f fun-expr fst-call)
           (local [(define value-holder (box (numV 198)))
                       (define new-ds (aRecSub f value-holder ds))]
                 (begin
                       (set-box! value-holder (interp fun-expr new-ds))
                       (interp fst-call new-ds)))]
      ))

