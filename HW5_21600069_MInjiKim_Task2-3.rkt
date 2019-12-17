#lang plai

;Problem 2
;Solved by myself: Y
;Time taken: about 2days
;[test]
;(test (parse '{{fun {val a} a} 10}) (app (fun (prm 'val 'a) (id 'a)) (num 10)))
;(test (parse '{fun {ref a} a}) (fun (prm 'ref 'a) (id 'a)))
;(test (parse '{with {x 10} {{fun {ref a} a} x}}) (app (fun (prm 'val 'x) (app (fun (prm 'ref 'a) (id 'a)) (id 'x))) (num 10)))
;(test (parse '{with {x 5} x}) (app (fun (prm 'val 'x) (id 'x)) (num 5)))
;(test (parse '{with {a 3} {seqn {{fun {val x} {setvar x 5}} a} a}}) (app (fun (prm 'val 'a) (seqn (app (fun (prm 'val 'x) (setvar 'x (num 5))) (id 'a)) (id 'a))) (num 3)))
;(test (parse '{with {a 3} {seqn {{fun {ref x} {setvar x 5}} a} a}}) (app (fun (prm 'val 'a) (seqn (app (fun (prm 'ref 'x) (setvar 'x (num 5))) (id 'a)) (id 'a))) (num 3)))

;Problem 3
;Solved by myself: Y
;Time taken: about 1day
;[test]
;(test (run '{{fun {val a} a} 10} (mtSub) (mtSto)) (v*s (numV 10) (aSto 1 (numV 10) (mtSto))))
;(test (run '{fun {ref a} a} (mtSub) (mtSto)) (v*s (closureV (prm 'ref 'a) (id 'a) (mtSub)) (mtSto)))
;(test (run '{with {x 10} {{fun {ref a} a} x}} (mtSub) (mtSto)) (v*s (numV 10) (aSto 1 (numV 10) (aSto 1 (numV 10) (mtSto)))))
;(test (run '{with {x 5} x} (mtSub) (mtSto)) (v*s (numV 5) (aSto 1 (numV 5) (mtSto))))
;(test (run '{with {a 3} {seqn {{fun {val x} {setvar x 5}} a} a}}(mtSub) (mtSto)) (v*s (numV 3) (aSto 2 (numV 5) (aSto 2 (numV 3) (aSto 1 (numV 3) (mtSto))))))
;(test (run '{with {a 3} {seqn {{fun {ref x} {setvar x 5}} a} a}}(mtSub) (mtSto)) (v*s (numV 5) (aSto 1 (numV 5) (aSto 1 (numV 3) (aSto 1 (numV 3) (mtSto))))))
;(test (run '{with {swap {fun {ref x}
;                       {fun {ref y}
;                            {with {z x}
;                                  {seqn {setvar x y}
;                                        {setvar y z}}}}}}
;            {with {a 10}
;                  {with {b 20}
;                        {seqn {{swap a} b}
;                              a}}}} (mtSub) (mtSto))
;
;      (v*s (numV 20) (aSto 3 (numV 10) (aSto 2 (numV 20) (aSto 4 (numV 10) (aSto 3 (numV 20) (aSto 2 (numV 10) (aSto 3 (numV 20) (aSto 2 (numV 10) (aSto 1 (closureV (prm 'ref 'x) (fun (prm 'ref 'y) (app (fun (prm 'val 'z) (seqn (setvar 'x (id 'y)) (setvar 'y (id 'z)))) (id 'x))) (mtSub)) (mtSto)))))))))))

;(test (run '{with {swap {fun {ref x}
;                       {fun {ref y}
;                            {with {z x} ;;; z will be processed as call-by-reference.
;                                  {seqn {setvar x y}
;                                        {setvar y z}}}}}}
;            {with {a 10}
;                  {with {b 20}
;                        {seqn {{swap a} b}
;                              b}}}} (mtSub) (mtSto))
;      (v*s (numV 10) (aSto 3 (numV 10) (aSto 2 (numV 20) (aSto 4 (numV 10) (aSto 3 (numV 20) (aSto 2 (numV 10) (aSto 3 (numV 20) (aSto 2 (numV 10) (aSto 1 (closureV (prm 'ref 'x) (fun (prm 'ref 'y) (app (fun (prm 'val 'z) (seqn (setvar 'x (id 'y)) (setvar 'y (id 'z)))) (id 'x))) (mtSub)) (mtSto)))))))))))


  

;[contract] : is it RBMFAE?
;[purpose] : Discriminate type
(define-type RBMFAE
    [num (n number?)]
    [add (lhs RBMFAE?) (rhs RBMFAE?)]
    [sub (lhs RBMFAE?) (rhs RBMFAE?)]
    [id (name symbol?)]
    [fun (param RBMFAE?) (body RBMFAE?)]
    [app (fun-expr RBMFAE?) (arg-expr RBMFAE?)]
    [newbox (val RBMFAE?)]
    [setbox   (bx-expr RBMFAE?) (val-expr RBMFAE?)]
    [openbox (bx-expr RBMFAE?)]
    [seqn (a RBMFAE?) (b RBMFAE?)]
    [setvar (id symbol?) (val-expr RBMFAE?)]
    [prm (a symbol?)(b symbol?)]
    )



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
    [closureV   (param RBMFAE?) (body RBMFAE?) (ds DefrdSub?)]
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
        [(list 'with (list i v) e)   (app(fun (prm 'val i) (parse e)) (parse v)) ]
        [(? symbol?)             (id sexp)]
        [(list 'fun (list a b) c)   (fun (prm a b)(parse c))]
        [(list 'setvar a b)  (setvar a (parse b))]
        [(list 'setbox a b)  (setbox (parse a) (parse b))]
        [(list 'openbox a)  (openbox (parse a))]
        [(list 'newbox a)  (newbox (parse a))]
        [(list 'seqn a b)  (seqn (parse a) (parse b))]
        [(list f a)            (app (parse f) (parse a))]
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
        [app (f a)  (type-case Value*Store (interp f ds st)
                           [v*s (f-value f-store)
                                   (type-case Value*Store (interp a ds f-store)
                                       [v*s (a-value a-store)
                                            (cond
                                                 [(eq? (prm-a (closureV-param f-value)) 'val) (local  ([define new-address (malloc a-store)])
                                                                            
                                                      (interp (closureV-body f-value)
                                                                   (aSub (prm-b (closureV-param f-value))
                                                                               new-address
                                                                               (closureV-ds f-value))
                                                                  (aSto new-address
                                                                            a-value
                                                                             a-store)))]
                                                  [else
                                                         (local  ([define new-address (lookup (id-name a) ds)])
                                                                            
                                                      (interp (closureV-body f-value)
                                                                   (aSub (prm-b (closureV-param f-value))
                                                                               new-address
                                                                               (closureV-ds f-value))
                                                                  (aSto new-address
                                                                            a-value
                                                                             a-store)))]
                                                        )
                                              ])])]


      
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
      [prm (a b) a]
      ))


