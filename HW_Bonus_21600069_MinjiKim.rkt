#lang plai
;Problem 1:
;Solved by myself: Y
;Time taken: about 3days
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
;(test (run '{rec {count {fun {val n} {if0 n 0 {+ 1 {count {- n 1}}}}}} {count 8}} (mtSub)(mtSto)) (numV 8))
;(test (run '{rec {fac {fun {val n} {if0 n 1 {* n {fac {- n 1}}}}}}{fac 3}} (mtSub)(mtSto)) (numV 6))
;
;; What was the most difficult part when integrating BMFAE and RCFAE?
;BMFAE output is long as v * s type, but RCFAE output is only one value, so it was the most difficult part of how to implement it.
;; How could you solve the most difficult part in which way. (Explain your algorithm)
;At first I thought I needed to fix the 'app' part, so I tried to fix the app part but didn't.
;Next,I thought I needed to fix the 'rec' part, 'rec' have to find v * s type by type-case and then outputs one value by [v * s (val st) val].


; type definition for abstract syntax tree of BMRCFAE
(define-type BMRCFAE
    [num         (n number?)]
    [add          (lhs BMRCFAE?) (rhs BMRCFAE?)]
    [sub          (lhs BMRCFAE?) (rhs BMRCFAE?)]
    [mul          (lhs BMRCFAE?) (rhs BMRCFAE?)]
    [id             (name symbol?)]
    [fun          (param prm?) (body BMRCFAE?)]
    [refun       (param symbol?) (body BMRCFAE?)]
    [setvar     (name symbol?) (v BMRCFAE?)]
    [newbox  (v BMRCFAE?)]
    [setbox     (bn BMRCFAE?) (v BMRCFAE?)]
    [openbox (v BMRCFAE?)]
    [seqn       (ex1 BMRCFAE?) (ex2 BMRCFAE?)]
    [app         (ftn BMRCFAE?) (arg BMRCFAE?)]
    [if0           (test-expr BMRCFAE?)
                    (then-expr BMRCFAE?) (else-expr BMRCFAE?)]
    [rec          (name symbol?) (named-expr BMRCFAE?) (body BMRCFAE?)]
    [prm (a symbol?)(b symbol?)]
  )


; parse : sexp -> BMRCFAE
(define (parse sexp)
   (match sexp
        [(? number?)             (num sexp)]
        [(list '+ l r)                  (add (parse l) (parse r))]
        [(list '- l r)                   (sub (parse l) (parse r))]
        [(list '* l r)                   (mul (parse l) (parse r))]
        [(list 'with (list i v) e)   (app(fun (prm 'val i) (parse e)) (parse v)) ]
        ;[(list 'with (list i v) e)   (app(fun i (parse e)) (parse v)) ]
        [(? symbol?)             (id sexp)]
        [(list 'newbox v)        (newbox (parse v))]
        [(list 'setbox i v)        (setbox (parse i) (parse v))]
        [(list 'openbox i)        (openbox (parse i))]
        [(list 'seqn ex1 ex2)  (seqn (parse ex1) (parse ex2))]
        [(list 'fun (list a b) c)   (fun (prm a b)(parse c))]
        ;[(list 'fun (list a b d) c)   (fun (a 'val d)(parse c))]
        [(list 'fun (list p) b)    (fun p (parse b))]
        [(list 'refun (list p) b) (refun p (parse b))]
        [(list f a)                    (app (parse f) (parse a))]
        [(list 'setvar n v)        (setvar n (parse v))]
        [(list 'if0 te th el)       (if0 (parse te) (parse th)  (parse el))]
        [(list 'rec (list rfn ne) body)   (rec rfn (parse ne) (parse body))]
       ; [(list 'rec (list rfn ne) body)   (rec rfn (fun 'val ne) (parse body))]
        [else                        (error 'parse "bad syntax: ~a" sexp)]))

(define-type BMRCFAE-Value
  [numV      (n number?)]
  [closureV  (param BMRCFAE?) (body BMRCFAE?) (ds DefrdSub?)] ; for call-by-value
  [refclosV  (param BMRCFAE?) (body BMRCFAE?) (ds DefrdSub?)] ; for call-by-refrence
  [boxV      (address integer?)]
  [exprV      (expr BMRCFAE?) (ds DefrdSub?)
                            (value (box/c (or/c false BMRCFAE-Value?)))])
                             
; num-op: operator -> (numV numV -> numV) ;  
(define (num-op op)
     (lambda (x y)
          (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op +))
(define num- (num-op -))
(define num* (num-op *))

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (address integer?) (ds DefrdSub?)]
  [aRecSub (name symbol?)
           (value-box (box/c Value*Store?))  
           (ds DefrdSub?)])

(define-type Store
  [mtSto]               
  [aSto   (address integer?) (value BMRCFAE-Value?)
          (rest Store?)])

(define-type Value*Store
  [v*s (value BMRCFAE-Value?) (store Store?)])

;lookup: symbol DefrdSub -> address
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub ()           (error 'lookup "free identifier")]
    [aSub  (i adr saved) (if(symbol=? i name)
                                adr
                                (lookup name saved))]
    [aRecSub (id val-box rest-ds)
             (if (symbol=? id name)
                 (unbox val-box)
                 (lookup name rest-ds))]
    ))

;store-lookup: (address or Value*Store) Store -> BMRCFAE-Value
(define (store-lookup arg sto)
  (if (integer? arg)
      (type-case Store sto
         [mtSto ()           (error 'store-lookup "No value at address")]
         [aSto  (location value rest-store)
                 (if(= location arg)
                     value
                    (store-lookup arg rest-store))])
      
      (type-case Value*Store arg
        [v*s (v s) v])
  ))

(define (strict v)
    (type-case BMRCFAE-Value v
        [exprV (expr ds v-box)
                     (if (not (unbox v-box))
                          (local [(define v (strict (interp expr ds)))]
                              (begin (set-box! v-box v)
                                           v))
                          (unbox v-box))] 
        [else v]))


; memory-alloc: Store -> Integer
; purpose: to get new address
(define (memory-alloc st)
  (+ 1 (max-address st)))

; max-address: Store -> Integer
(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (n v st)
          (max n (max-address st))]))

; numzero? :  BMRCFAE-Value -> boolean
(define (numzero? n)
  (type-case Value*Store n
    [v*s (v s) (zero? (numV-n v))]))

; interp: BMRCFAE DefrdSub -> Value*Store
(define (interp rbmrcfae ds st)
  (type-case BMRCFAE rbmrcfae
    [num    (n)    (v*s (numV n) st)]
    [add    (l r)    (interp-two l r ds st (lambda (v1 v2 st1) (v*s (num+ v1 v2) st1)))]
    [sub    (l r)    (interp-two l r ds st (lambda (v1 v2 st1) (v*s (num- v1 v2) st1)))]
    [mul    (l r)    (interp-two l r ds st (lambda (v1 v2 st1) (v*s (num* v1 v2) st1)))]
    [id     (s)       (v*s (store-lookup (lookup s ds) st) st)]
    [fun    (p b)   (v*s (closureV p b ds) st)]
    [refun  (p b)  (v*s (refclosV p b ds) st)]
    [app (f a)  (type-case Value*Store (interp f ds st)
                           [v*s (f-value f-store)
                                   (type-case Value*Store (interp a ds f-store)
                                       [v*s (a-value a-store)
                                            (cond
                                                 [(eq? (prm-a (closureV-param f-value)) 'val) (local  ([define new-address (memory-alloc a-store)])
                                                                            
                                                      (interp (closureV-body f-value)
                                                                   (aSub (prm-b (closureV-param f-value))
                                                                               new-address
                                                                               (closureV-ds f-value))
                                                                  (aSto new-address
                                                                            a-value
                                                                             a-store)))]
                                                  [(eq? (prm-a (closureV-param f-value)) 'ref)
                                                     (local  ([define new-address (lookup (id-name a) ds)])
                                                                            
                                                      (interp (closureV-body f-value)
                                                                   (aSub (prm-b (closureV-param f-value))
                                                                               new-address
                                                                               (closureV-ds f-value))
                                                                  (aSto new-address
                                                                            a-value
                                                                             a-store)))]
                                                  [else
                                                   (local [(define ftn (strict(interp f ds st)))
                                                      (define a-val (exprV a ds (box #f)))]
                                                        (interp (closureV-body ftn)
                                                          (aSub (closureV-param ftn)
                                                              ;(interp a ds)
                                                              a-val
                                                              (closureV-ds ftn)) st))
                                                   ]

                                                        )
                                              ])])]
    [newbox  (val)    (type-case Value*Store (interp val ds st)
                     [v*s (vl st1)
                                   (local [(define a (memory-alloc st1))]
                                          (v*s (boxV a)
                                          (aSto a vl st1)))])]
    [setbox  (bx-expr val-expr)
                   (interp-two bx-expr val-expr ds st
                               (lambda (bx-val val st1)
                                       (v*s val
                                       (aSto (boxV-address bx-val)
                                             val
                                             st1))))]
    [openbox (bx-expr)
                   (type-case Value*Store (interp bx-expr ds st)
                     [v*s (bx-val st1)
                                       (v*s (store-lookup (boxV-address bx-val)
                                                           st1)
                                             st1)])]
    [seqn    (a b) (interp-two a b ds st (lambda (v1 v2 st1) (v*s v2 st1)))]
    [setvar  (id val-expr) (local [(define a (lookup id ds))]
                           (type-case Value*Store (interp val-expr ds st)
                             [v*s (val st)
                                  (v*s val
                                       (aSto a val st))]))]
    [if0 (test-expr then-expr else-expr)
                   (if(numzero? (interp test-expr ds st))
                           (interp then-expr ds st)
                           (interp else-expr ds st))]
    [rec (bound-id named-expr first-call)
                      
                       (local [(define value-holder (box (v*s (numV 198) (mtSto))))
                               (define new-ds (aRecSub bound-id
                                                       value-holder
                                                       ds))]
                              (begin
                                
                                (set-box! value-holder (interp named-expr new-ds st)) 
                                ;(interp first-call new-ds st)
                                ;((eq? (prm-a  (closureV-param value-holder)) 'ref)
                                ; (prm-a (closureV-param value-holder) 'val))
                                
                                (type-case Value*Store (interp first-call new-ds st)
                                   [v*s (val st)
                                     val])
                                ))]
    [prm (a b) a]
    ))


;interp-two: BMRCFAE BMRCFAE DefrdSub Store
;            (Value Value Store -> Value*Store)
;            -> Value*Store
(define (interp-two expr1 expr2 ds st handle)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st2)
         [type-case Value*Store (interp expr2 ds st2)
           [v*s (val2 st3)
                (handle val1 val2 st3)]]]))

;[contract] : sexp -> parse -> interp
;[purpose] : convert concrete syntax to abstract sytax, parse and interp
(define (run sexp ds st)
     (interp (parse sexp) ds st))





(test (run '{{fun {val a} a} 10} (mtSub) (mtSto)) (v*s (numV 10) (aSto 1 (numV 10) (mtSto))))
(test (run '{fun {ref a} a} (mtSub) (mtSto)) (v*s (closureV (prm 'ref 'a) (id 'a) (mtSub)) (mtSto)))
(test (run '{with {x 10} {{fun {ref a} a} x}} (mtSub) (mtSto)) (v*s (numV 10) (aSto 1 (numV 10) (aSto 1 (numV 10) (mtSto)))))
(test (run '{with {x 5} x} (mtSub) (mtSto)) (v*s (numV 5) (aSto 1 (numV 5) (mtSto))))
(test (run '{with {a 3} {seqn {{fun {val x} {setvar x 5}} a} a}}(mtSub) (mtSto)) (v*s (numV 3) (aSto 2 (numV 5) (aSto 2 (numV 3) (aSto 1 (numV 3) (mtSto))))))
(test (run '{with {a 3} {seqn {{fun {ref x} {setvar x 5}} a} a}}(mtSub) (mtSto)) (v*s (numV 5) (aSto 1 (numV 5) (aSto 1 (numV 3) (aSto 1 (numV 3) (mtSto))))))
(test (run '{with {swap {fun {ref x}
                       {fun {ref y}
                            {with {z x}
                                  {seqn {setvar x y}
                                        {setvar y z}}}}}}
            {with {a 10}
                  {with {b 20}
                        {seqn {{swap a} b}
                              a}}}} (mtSub) (mtSto))

      (v*s (numV 20) (aSto 3 (numV 10) (aSto 2 (numV 20) (aSto 4 (numV 10) (aSto 3 (numV 20) (aSto 2 (numV 10) (aSto 3 (numV 20) (aSto 2 (numV 10) (aSto 1 (closureV (prm 'ref 'x) (fun (prm 'ref 'y) (app (fun (prm 'val 'z) (seqn (setvar 'x (id 'y)) (setvar 'y (id 'z)))) (id 'x))) (mtSub)) (mtSto)))))))))))

(test (run '{with {swap {fun {ref x}
                       {fun {ref y}
                            {with {z x} ;;; z will be processed as call-by-reference.
                                  {seqn {setvar x y}
                                        {setvar y z}}}}}}
            {with {a 10}
                  {with {b 20}
                        {seqn {{swap a} b}
                              b}}}} (mtSub) (mtSto))
      (v*s (numV 10) (aSto 3 (numV 10) (aSto 2 (numV 20) (aSto 4 (numV 10) (aSto 3 (numV 20) (aSto 2 (numV 10) (aSto 3 (numV 20) (aSto 2 (numV 10) (aSto 1 (closureV (prm 'ref 'x) (fun (prm 'ref 'y) (app (fun (prm 'val 'z) (seqn (setvar 'x (id 'y)) (setvar 'y (id 'z)))) (id 'x))) (mtSub)) (mtSto)))))))))))



(test (run '{rec {count {fun {val n} {if0 n 0 {+ 1 {count {- n 1}}}}}} {count 8}} (mtSub)(mtSto)) (numV 8))
(test (run '{rec {fac {fun {val n} {if0 n 1 {* n {fac {- n 1}}}}}}{fac 3}} (mtSub)(mtSto)) (numV 6))