#lang typed/racket/no-check

(provide (all-defined-out))

(struct Var
  ([name : Symbol])
  #:transparent)
(: fresh (→ Var Var))
(define (fresh x)
  (Var (gensym (Var-name x))))
(struct App
  ([rator : Term]
   [rand : Term])
  #:transparent)
(struct Tie
  ([var : Var]
   [body : Term])
  #:transparent)
(define-type Constant
  (U Null
     Number
     Symbol))
(: constant? (→ Any Boolean))
(define (constant? x)
  (or (null? x) (number? x) (symbol? x)))
(define-type Term
  (U Constant
     Var
     App
     Tie
     (Pairof Term Term)))
(struct ∀
  ([x : Var])
  #:transparent)
(struct ∃
  ([x : Var])
  #:transparent)
(define-type Quant
  (U ∀ ∃))

(define-type Sub
  (HashTable Var Term))
(define-type Eqn
  (List Term Term))

