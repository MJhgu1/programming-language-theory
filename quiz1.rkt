#lang plai

(define-type Starbucks
	[americano (price number?) (size string?)]
	[greenTea (price number?) (takeOut boolean?)]
	[frappuccino (price number?) (whippingCream boolean?) (kind string?)]
)

(define jc(americano 4300 "tall"))
(define hw(greenTea 5600 false))
(define hw2(americano 4300 "venti"))
(define sb(frappuccino 6800 true "strawberry"))

(define (print-price a)
  (type-case Starbucks a
    [americano (p s) p]
    [greenTea (p t) p] 
    [frappuccino (p w k) p]
    ))

(Starbucks? hw)
(greenTea? hw2)
(print-price jc)

(define (fibonacci a)
  (cond
    [(= a 0) 0]
    [(= a 1) 1]
    [else (fibonacci (- a 1)) + (fibonacci (- a 2))])
    )

(fibonacci 5)