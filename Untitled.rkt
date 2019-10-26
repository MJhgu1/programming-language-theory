#lang plai

(define-type WAE
  [num (n number?)]
  [add (lhs WAE?)(rhs WAE?)]
  [sub (lhs WAE?)(rhs WAE?)]
  [with (name symbol?)(name-expr WAE?)(body WAE?)]
  [id (name symbol?)])

(define (symbol<? a b) (string<? (symbol->string a) (symbol->string b)))

;Problem 1:
;Solved by myself: Y
;Time taken: about 3days
;[contract] : free-ids : WAE -> free-ids
;[purpose] : find free-ids
;[test] (test (free-ids (with 'x (num 3) (add (id 'x) (sub (num 3) (id 'x))))) '())
;       (test (free-ids (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x))))) '(a))
;       (test (free-ids (with 'x (num 3) (sub (id 'b) (sub (id 'a) (id 'x))))) '(a b))
;       (test (free-ids (with 'x (num 3) (sub (id 'a) (sub (id 'b) (add (id 'x) (id 'b)))))) '(a b))
;       (test (free-ids (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b y))
;       (test (free-ids (with 'x (id 't) (sub (id 'x) (with 'y (id 'y) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b t y))
;       (test (free-ids (with 'x (with 'y (num 3) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y)))) '(x y))
;       (test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'a) (id 'a)))) '(a b c y))
;       (test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(b c d y))
;       (test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(b c d y z))

(define (subst wae idtf val)
	(type-case WAE wae
		[num(n) wae]
		[add(l r) (add (subst l idtf val) (subst r idtf val))]
		[sub(l r) (sub (subst l idtf val) (subst r idtf val))]
		[with(i v e) (with i (subst v idtf val)
                              (if (symbol=? i idtf) e (subst e idtf val)))]
		[id(s) (if (symbol=? s idtf) val wae)]
          ))

(define (free-ids wae)
	(type-case WAE wae
		[num (n) append '()]
		[add (l r) (sort (remove-duplicates(flatten (append (list(free-ids l)) (list(free-ids r)) ))) symbol<?)]
		[sub (l r) (sort (remove-duplicates(flatten (append (list(free-ids l)) (list(free-ids r)) ))) symbol<?)]
		[with (i v e) (remove-duplicates(flatten (append(list(free-ids(subst e i v))) (list(free-ids v)))))]
		[id (s) (append (list s))]))

(free-ids (with 'x (num 3) (add (id 'x) (sub (num 3) (id 'x)))))
(free-ids (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x)))))
(free-ids (with 'x (num 3) (sub (id 'b) (sub (id 'a) (id 'x)))))
(free-ids (with 'x (num 3) (sub (id 'a) (sub (id 'b) (add (id 'x) (id 'b))))))
(free-ids (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'b) (id 'a)))))))
(free-ids (with 'x (id 't) (sub (id 'x) (with 'y (id 'y) (add (id 'x) (sub (id 'b) (id 'a)))))))
(free-ids (with 'x (with 'y (num 3) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y))))
(free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'a) (id 'a))))
(free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a))))
(free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z))))



;Problem 2:
;Solved by myself: Y
;Time taken: about 2days
;[contract] : bining-ids : WAE -> binding-ids
;[purpose] : find binding-ids
;[tests] (test (binding-ids (add (num 3) (sub (id 'x) (id 'y)))) '())
;        (test (binding-ids (with 'y (num 3) (with 'x (id 'x) (id 'y)))) '(x y))
;        (test (binding-ids (with 'y (num 3) (with 'y (id 'x) (add (id 'x) (id 'y))))) '(y))
;        (test (binding-ids (with 'y (num 3) (with 'y (with 'x (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y))))) '(x y))
;        (test (binding-ids (with 'z (num 3) (with 'w (with 'z (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (with 'w (id 'y) (add (num 7) (id 'w)))))) '(w z))


(define (binding-ids wae)
  (type-case WAE wae
    [num (n) (append '())]
    [add (l r) (append (binding-ids l) (binding-ids r))]
    [sub (l r) (append (binding-ids l) (binding-ids r))]
    [with (i v e) (sort (remove-duplicates(flatten (list i (binding-ids v) (binding-ids e)))) symbol<? )]
    [id (s)	(append '())]))



(binding-ids (add (num 3) (sub (id 'x) (id 'y))))
(binding-ids (with 'y (num 3) (with 'x (id 'x) (id 'y))))
(binding-ids (with 'y (num 3) (with 'y (id 'x) (add (id 'x) (id 'y)))))
(binding-ids (with 'y (num 3) (with 'y (with 'x (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y)))))
(binding-ids (with 'z (num 3) (with 'w (with 'z (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (with 'w (id 'y) (add (num 7) (id 'w))))))


;Problem 3:
;solved by my self: Y
;Time taken: about 3 days
;[contract] bound-ids : WAE -> bound-ids
;[contract] subst: WAE symbol number -> WAE
;[purpose] find bound-ids
;[test](test (bound-ids (with 'x (num 3) (add (id 'y) (num 3)))) '())
;      (test (bound-ids (with 'x (num 3) (add (id 'x) (sub (id 'x) (id 'y))))) '(x))
;      (test (bound-ids (with 'x (num 3) (add (id 'x) (with 'y (num 7) (sub (id 'x) (id 'y)))))) '(x y))
;      (test (bound-ids (with 'x (num 3) (with 'y (id 'x) (sub (num 3) (id 'y))))) '(x y))
;      (test (bound-ids (with 'x (num 3) (add (id 'y) (with 'y (id 'x) (sub (num 3) (num 7)))))) '(x))
;      (test (bound-ids (with 'x (id 'x) (add (id 'y) (with 'y (id 'y) (sub (num 3) (with 'z (num 7) (sub (id 'z) (id 'x)))))))) '(x z))
;      (test (bound-ids (with 'x (with 'y (num 3) (add (id 'x) (id 'y))) (add (id 'y) (with 'y (id 'y) (sub (num 3) (num 7)))))) '(y))
;      (test (bound-ids (with 'x (id 'a) (with 'y (id 'b) (with 'z (id 'c) (add (id 'd) (sub (id 'x) (add (id 'y) (id 'z)))))))) '(x y z))
;      (test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(a x))
;      (test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(x))



(define (bound_subst wae idtf val)
	(type-case WAE wae
		[num(n) wae]
		[add(l r) (add (bound_subst l idtf val) (bound_subst r idtf val))]
		[sub(l r) (sub (bound_subst l idtf val) (bound_subst r idtf val))]
		[with(i v e) (with i (bound_subst v idtf val)
                              (if (symbol=? i idtf) e (bound_subst e idtf val)))]
		[id(s) (if (symbol=? s idtf) (with s (num 0) (num 0)) wae)]
          ))
(define (bound-ids wae)
	(type-case WAE wae
		[num (n) (if (equal? 0 n) n (append '()))]
		[add (l r) (sort (remove-duplicates(flatten (append (list(bound-ids l)) (list(bound-ids r))))) symbol<?) ]
		[sub (l r) (sort (remove-duplicates(flatten (append (list(bound-ids l)) (list(bound-ids r))))) symbol<?) ]
		[with (i v e) (if (and(equal? 0 (bound-ids e)) (equal? 0 (bound-ids v))) (append (list i)) (sort (remove-duplicates(flatten(append (list(bound-ids(bound_subst e i v))) (list (bound-ids v)))) ) symbol<?))]
		[id (s) (append '())]
          ))


(bound-ids (with 'x (num 3) (add (id 'y) (num 3))))
(bound-ids (with 'x (num 3) (add (id 'x) (sub (id 'x) (id 'y)))))
(bound-ids (with 'x (num 3) (add (id 'x) (with 'y (num 7) (sub (id 'x) (id 'y))))))
(bound-ids (with 'x (num 3) (with 'y (id 'x) (sub (num 3) (id 'y)))))
(bound-ids (with 'x (num 3) (add (id 'y) (with 'y (id 'x) (sub (num 3) (num 7))))))
(bound-ids (with 'x (id 'x) (add (id 'y) (with 'y (id 'y) (sub (num 3) (with 'z (num 7) (sub (id 'z) (id 'x))))))))
(bound-ids (with 'x (with 'y (num 3) (add (id 'x) (id 'y))) (add (id 'y) (with 'y (id 'y) (sub (num 3) (num 7))))))
(bound-ids (with 'x (id 'a) (with 'y (id 'b) (with 'z (id 'c) (add (id 'd) (sub (id 'x) (add (id 'y) (id 'z))))))))
(bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a))))
(bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z))))