#lang plai

;Problem 1
;Solved by myself: Y
;Time taken: about 3days
;[test]
;(test (run '{with {a 7} a} (mtSub) (mtSto)) (v*s (numV 7) (aSto 1 (numV 7) (mtSto))))
;(test (run '{with {a 3} {setvar a 5}} (mtSub) (mtSto)) (v*s (numV 5) (aSto 1 (numV 5) (aSto 1 (numV 3) (mtSto)))))
;(test (run '{with {a 3} {seqn {{fun {x} {setvar x 5}} a} a}} (mtSub) (mtSto)) (v*s (numV 3) (aSto 2 (numV 5) (aSto 2 (numV 3) (aSto 1 (numV 3) (mtSto))))))
;(test (run '{with {b {newbox 7}} {seqn {setbox b 10} {openbox b}}} (mtSub) (mtSto)) (v*s (numV 10) (aSto 1 (numV 10) (aSto 2 (boxV 1) (aSto 1 (numV 7) (mtSto))))))
;(test (run '{with {a 3} {seqn {{refun {x} {setvar x 5}} a} a}} (mtSub) (mtSto)) (v*s (numV 5) (aSto 1 (numV 5) (aSto 1 (numV 3) (mtSto)))))
;(test (run '{with {a {newbox 3}} {seqn {{fun {x} {setbox x 5}} a} {openbox a}}} (mtSub) (mtSto)) (v*s (numV 5) (aSto 1 (numV 5) (aSto 3 (boxV 1) (aSto 2 (boxV 1) (aSto 1 (numV 3) (mtSto)))))))
;(test (run '{with {swap {fun {x}{fun {y}{with {z x}{seqn {setvar x y}{setvar y z}}}}}}{with {a 10}{with {b 20}{seqn {{swap a} b}a}}}} (mtSub)(mtSto))
;(v*s (numV 10) (aSto 5 (numV 10) (aSto 4 (numV 20) (aSto 6 (numV 10) (aSto 5 (numV 20) (aSto 4 (numV 10) (aSto 3 (numV 20) (aSto 2 (numV 10)
;(aSto 1 (closureV 'x (fun 'y (app (fun 'z (seqn (setvar 'x (id 'y)) (setvar 'y (id 'z)))) (id 'x))) (mtSub)) (mtSto)))))))))))

;[contract] : is it RBMFAE?
;[purpose] : Discriminate type
(define-type RBMFAE
    [num (n number?)]
    [add (lhs RBMFAE?) (rhs RBMFAE?)]
    [sub (lhs RBMFAE?) (rhs RBMFAE?)]
    [id (name symbol?)]
    [fun (param symbol?) (body RBMFAE?)]
    [refun (param symbol?) (body RBMFAE?)] 
    [app (fun-expr RBMFAE?) (arg-expr RBMFAE?)]
    [newbox (val RBMFAE?)]
    [setbox   (bx-expr RBMFAE?) (val-expr RBMFAE?)]
    [openbox (bx-expr RBMFAE?)]
    [seqn (a RBMFAE?) (b RBMFAE?)]
    [setvar (id symbol?) (val-expr RBMFAE?)])

(define-type Value*Store
    [v*s (value RBMFAE-Value?) (store Store?)])

;[contract] : is it DefrdSub?
;[purpose] : determine of DefrdSub
(define-type DefrdSub
    [mtSub]
    [aSub  (name symbol?)
                (address integer?)
                (ds DefrdSub?)])

;[contract] : is it Store?
;[purpose] : determine of Store
(define-type Store
    [mtSto]
    [aSto  (address integer?)
                (value RBMFAE-Value?)
                (rest Store?)])

;[contract] : is it RBMFAE-Value?
;[purpose] : Discriminate type
(define-type RBMFAE-Value
    [numV        (n number?)]
    [closureV   (param symbol?) (body RBMFAE?) (ds DefrdSub?)]
    [refclosV  (param symbol?) (body RBMFAE?) (ds DefrdSub?)]
    [exprV      (expr RBMFAE?) (ds DefrdSub?)
                            (value (box/c (or/c false RBMFAE-Value?)))]
    [boxV (address integer?)])

;[contract] : symbol DefrdSub -> RBMFAE-Value
;[purpose] : To found value
(define (lookup name ds)
    (type-case DefrdSub ds
        [mtSub  () (error "free variable")]
        [aSub    (sub-name val rest-ds)
                                  (if (symbol=? sub-name name)
                                        val
                                        (lookup name rest-ds))]))

;store-lookup address Store -> RBMFAE-Value
(define (store-lookup address sto)
  (type-case Store sto
    [mtSto ()           (error 'store-lookup "No value at address")]
    [aSto   (location value rest-store)
                               (if(= location address)
                                   value
                                  (store-lookup address rest-store))]))

;[contract] :  RBMFAE-Value -> boolean
;[purpose] : Discriminate if n is 0
(define (numzero? n)
    (zero? (numV-n n)))

;[contract] : RBMFAE RBMFAE -> RBMFAE
;[purpose] : calculate by using op 
(define (num-op op)
     (lambda (x y)
          (numV (op (numV-n (strict x)) (numV-n (strict y))))))

;[contract] : RBMFAE-Value -> RBMFAE-Value 
(define (strict v)
    (type-case RBMFAE-Value v
        [exprV (expr ds v-box)
                     (if (not (unbox v-box))
                          (local [(define v (strict (interp expr ds)))]
                              (begin (set-box! v-box v)
                                           v))
                          (unbox v-box))] 
        [else v]))

;[contract] : num+ -> + and num- -> -
;[purpose] : convert num-op to operations
(define num+ (num-op +))
(define num- (num-op -))

;[contract] : sexp -> parse -> interp
;[purpose] : convert concrete syntax to abstract sytax, parse and interp
(define (run sexp ds st)
     (interp (parse sexp) ds st))


; malloc : Store -> Integer
(define (malloc st)
    (+ 1 (max-address st))) 

; max-address: Store -> Integer
(define (max-address st)
    (type-case Store st
        [mtSto () 0]
        [aSto (n v st)
                  (max n (max-address st))]))

;[contract] : sexp->RBMFAE DefrdSub
;[purpose] : convert concrete syntax to abstract sytax
(define (parse sexp)
   (match sexp
        [(? number?)             (num sexp)]
        [(list '+ l r)                  (add (parse l) (parse r))]
        [(list '- l r)                   (sub (parse l) (parse r))]
        [(list 'with (list i v) e)   (app(fun i (parse e)) (parse v)) ]
        [(? symbol?)             (id sexp)]
        [(list 'fun (list p) b)    (fun p (parse b))]
        [(list 'setvar a b)  (setvar a (parse b))]
        [(list 'setbox a b)  (setbox (parse a) (parse b))]
        [(list 'openbox a)  (openbox (parse a))]
        [(list 'newbox a)  (newbox (parse a))]
        [(list 'seqn a b)  (seqn (parse a) (parse b))]
        [(list f a)            (app (parse f) (parse a))]
        [(list 'refun (list p) b)   (refun p (parse b))]
        [else                        (error 'parse "bad syntax: ~a" sexp)]
     ))


;[contract] : interp : RBMFAE DefrdSub Store -> Value*Store
;[purpose] : consuming abstract sytax
(define (interp expr ds st)
    (type-case RBMFAE expr
        [num (n)  (v*s (numV n) st)]
        [add  (l r) (type-case Value*Store (interp l ds st)
                           [v*s (l-value l-store)
                                (type-case Value*Store (interp r ds l-store)
                                        [v*s (r-value r-store)
                                               (v*s (num+ l-value r-value)
                                                              r-store)])])] 
        [sub  (l r) (type-case Value*Store (interp l ds st)
                           [v*s (l-value l-store)
                                (type-case Value*Store (interp r ds l-store)
                                        [v*s (r-value r-store)
                                               (v*s (num- l-value r-value)
                                                              r-store)])])]
        [id (name) (v*s (store-lookup (lookup name ds) st) st)] 
        [fun   (p b)  (v*s (closureV p b ds) st)]
        [refun (a b)  (v*s (refclosV a b ds) st)]
        [app (f a)  (type-case Value*Store (interp f ds st)
                           [v*s (f-value f-store)
                                (type-case RBMFAE-Value f-value
                                    [closureV (c-param c-body c-ds)
                                         (type-case Value*Store (interp a ds f-store)
                                               [v*s (a-value a-store)
                                                      (local ([define new-address (malloc a-store)])
                                                           (interp c-body
                                                                   (aSub c-param
                                                                         new-address
                                                                         c-ds)
                                                                   (aSto new-address
                                                                         a-value
                                                                         a-store))
                                                        
                                                        )])]
                                    [refclosV (rc-param rc-body rc-ds)
                                             (local ([define address (lookup (id-name a) ds)])
                                               (interp rc-body
                                                      (aSub rc-param
                                                       address
                                                       rc-ds)
                                               f-store)
                                               )]
                                                                                                                                            
                                    [else (error interp "trying to apply a number")])]
                      )]

        
        [seqn (a b)  (type-case Value*Store (interp a ds st)
                              [v*s (a-value a-store)
                                      (interp b ds a-store)])]
        [newbox (val)
                     (type-case Value*Store (interp val ds st)
                          [v*s   (vl st1)
                                    (local [(define a (malloc st1))]
                                               (v*s (boxV a)
                                                       (aSto a vl st1)))])]
        [setbox (bx-expr val-expr)
                   (type-case Value*Store (interp bx-expr ds st)
                       [v*s  (bx-val st2)
                                (type-case Value*Store (interp val-expr ds st2)
                                    [v*s (val st3)
                                            (v*s val
                                                    (aSto  (boxV-address bx-val)
                                                                val
                                                                st3))])])]
        [openbox (bx-expr)
                      (type-case Value*Store (interp bx-expr ds st)
                             [v*s (bx-val st1)
                                     (v*s (store-lookup (boxV-address bx-val) 
                                                                       st1)
                                              st1)])]
        [setvar (id val-expr)
                 (local [(define a (lookup id ds))]
                      (type-case Value*Store (interp val-expr ds st)
                            [v*s (val st)
                                    (v*s val
                                             (aSto a
                                                        val
                                                        st))]))]  
      ))


