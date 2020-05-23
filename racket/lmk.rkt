#lang racket
(require "data.rkt")
(require "unify.rkt")
(require (for-syntax racket/format
                     racket/syntax))

(provide (all-defined-out))

(struct State
  ([idx->f #:mutable]
   [name->idx #:mutable]
   [f->ext #:mutable]))
(define state
  (State
   (make-immutable-hasheqv)
   (make-immutable-hasheqv)
   (make-immutable-hasheqv)))

(define (append$ $₁ $₂)
  (cond
    [(null? $₁) $₂]
    [(pair? $₁) (cons (car $₁) (append$ (cdr $₁) $₂))]
    [else (λ () (append$ $₂ ($₁)))]))

(define (append-map$ f $)
  (cond
    [(null? $) '()]
    [(pair? $) (append$ (f (car $)) (append-map$ f (cdr $)))]
    [else (λ () (append-map$ f ($)))]))

(define ((conj₂ g₁ g₂) S)
  (append-map$ g₂ (g₁ S)))

(define ((disj₂ g₁ g₂) S)
  (append$ (g₁ S) (g₂ S)))

(define (fail S)
  '())
(define (succeed S)
  `(,S))

(define-syntax disj
  (syntax-rules ()
    [(disj) fail]
    [(disj g) g]
    [(disj g₀ g ...) (disj₂ g₀ (disj g ...))]))

(define-syntax conj
  (syntax-rules ()
    [(conj) succeed]
    [(conj g) g]
    [(conj g₀ g ...) (conj₂ g₀ (conj g ...))]))

(define-syntax conde
  (syntax-rules ()
    [(conde (g ...) ...) (disj (conj g ...) ...)]))

(define call/fresh
  (λ (name f)
    (λ (S)
      (match S
        [(list qs es σ name->idx)
         ((f name) (list (append qs (list (∃ name)))
                         es σ name->idx))]))))

(define call/all
  (λ (name f)
    (λ (S)
      (match S
        [(list qs es σ name->idx)
         ((f name) (list (append qs (list (∀ name))) es σ name->idx))]))))

(define-syntax fresh
  (syntax-rules ()
    [(fresh () g ...) (conj g ...)]
    [(fresh (x₀ x ...) g ...)
     (call/fresh (Var 'x₀)
                 (λ (x₀)
                   (fresh (x ...) g ...)))]))

(define-syntax all
  (syntax-rules ()
    [(all () g ...) (conj g ...)]
    [(all (x₀ x ...) g ...)
     (call/all (Var 'x₀)
               (λ (x₀)
                 (all (x ...) g ...)))]))

(define-syntax (defrel stx)
  (syntax-case stx ()
    [(_ (name formal ...) body ...)
     (with-syntax ([f (format-id #'name "-body")]
                   [ext (format-id #'name "-ext")])
       #'(begin
           (define f (make-parameter (λ (formal ...) (λ (S) (λ () ((conj body ...) S))))))
           (define ext (λ (f args) (λ (formal ...)
                                     (conde
                                      [(f formal ...)]
                                      [(all-== args (list formal ...))]))))
           (define name
             (λ (formal ...)
               ((f) formal ...)))))]))

(define-syntax (assume stx)
  (syntax-case stx ()
    [(_ () body ...)
     #'(conj body ...)]
    [(assume ([name arg ...] more ...) body ...)
     (with-syntax ([f (string->symbol (string-append (symbol->string #'name) "-body"))]
                   [ext (string->symbol (string-append (symbol->string #'name) "-ext"))])
       #'(parameterize ([f (ext (f) arg ...)])
           (conj body ...)))]))

#;
(define-syntax defrel 
  (syntax-rules ()
    [(_ (name formal ...) body ...)
     (begin
       (let ([idx (hash-count (State-idx->f state))])
         (set-State-idx->f! state (hash-set (State-idx->f state) idx (λ (formal ...) (λ (S) (λ () ((conj body ...) S))))))
         (set-State-name->idx! state (hash-set (State-name->idx state) 'name idx))
         (set-State-f->ext! state (hash-set (State-f->ext state) 'name (λ (f args) (λ (formal ...)
                                                                                     (conde
                                                                                      [(f formal ...)]
                                                                                      [(all-== args (list formal ...))]))))))
       (define name
         (λ (formal ...)
           (λ (S)
             (match S
               [(list qs es σ name->idx)
                (((hash-ref (State-idx->f state)
                            (hash-ref name->idx 'name))
                  formal ...) S)])))))]))

#;
(define-syntax assume
  (syntax-rules ()
    [(assume () body ...)
     (conj body ...)]
    [(assume [(name arg ...) more ...] body ...)
     (λ (S)
       (match S
         [(list qs es σ name->idx)
          (let* ([idx (hash-count (State-idx->f state))]
                 [f^ (hash-ref (State-idx->f state) (hash-ref name->idx 'name))]
                 [f ((hash-ref (State-f->ext state) 'name) f^ (list arg ...))])
            (begin (set-State-idx->f! state (hash-set (State-idx->f state) idx f))
                   ((assume (more ...) (conj body ...))
                    (list qs es σ (hash-set name->idx 'name idx)))))]))]))

(define-syntax app
  (syntax-rules ()
    [(app rator rand) (App rator rand)]
    [(app rator rand₀ rand ...) (app (App rator rand₀) rand ...)]))

(define-syntax tie
  (syntax-rules ()
    [(_ () t) t]
    [(_ (x₀ x ...) t)
     (let ([x₀ (Var 'x₀)])
       (Tie x₀ (tie (x ...) t)))]))

(define (all-== l₁ l₂)
  (cond
    [(null? l₁) succeed]
    [else
     (conj (== (car l₁) (car l₂))
           (all-== (cdr l₁) (cdr l₂)))]))

(define ((== t₁ t₂) S)
  (match S
    [`(,qs ,es ,σ ,name->idx)
     (match (unify qs `((,t₁ ,t₂)) σ)
       [#f '()]
       [`(,qs ,es ,σ) `((,qs ,es ,σ ,name->idx))])]))

(define ((print x) S)
  (match S
    [`(,qs ,es ,σ ,name->idx)
     (begin (displayln (walk* x σ))
            `(,S))]))

(define (take$ n $)
  (cond
    [(and n (zero? n)) '()]
    [(null? $) '()]
    [(pair? $) (cons (car $) (take$ (and n (sub1 n)) (cdr $)))]
    [else (take$ n ($))]))

(define (run-goal n g q)
  (take$ n
         (g (list (list (∃ q))
                  '()
                  (make-immutable-hasheqv)
                  (State-name->idx state)))))

(define (walk* t ρ)
  (let ([t (walk t ρ)])
    (match t
      [`,c
       #:when (constant? c)
       c]
      [`,y
       #:when (Var? y)
       y]
      [(Tie y body)
       (Tie (walk* y ρ) (walk* body ρ))]
      [(App rator rand)
       (App (walk* rator ρ) (walk* rand ρ))]
      [`(,a . ,d)
       `(,(walk* a ρ) . ,(walk* d ρ))])))
(define (walk*/pp t ρ)
  (let ([t (walk t ρ)])
    (match t
      [`,c
       #:when (constant? c)
       c]
      [`,y
       #:when (Var? y)
       y]
      [(Tie y body)
       `(tie (,(walk y ρ)) ,(walk*/pp body ρ))]
      [(App rator rand)
       `(app ,(walk*/pp rator ρ) ,(walk*/pp rand ρ))]
      [`(,a . ,d)
       `(,(walk*/pp a ρ) . ,(walk*/pp d ρ))])))

(define (reify-name n)
  (string->symbol (string-append "_" (number->string n))))


(define (reify-s v s)
  (let ([v (walk v s)])
    (cond
      [(Var? v)
       (let* ([n (hash-count s)]
              [rn (reify-name n)])
         (hash-set s v rn))]
      [(Tie? v)
       (let ([s (reify-s (Tie-var v) s)])
         (reify-s (Tie-body v) s))]
      [(App? v)
       (let ([s (reify-s (App-rator v) s)])
         (reify-s (App-rand v) s))]
      [(pair? v) (let ([s (reify-s (car v) s)])
                   (reify-s (cdr v) s))]
      [else s])))

(define (reify v)
  (λ (S)
    (match S
      [(list qs es ρ name->idx)
       (let ([v (walk* v ρ)])
         (let ([names (reify-s v (make-immutable-hasheqv))])
           (walk*/pp v names)))])))

(define-syntax run
  (syntax-rules ()
    [(run n (x₀ x ...) g ...)
     (run n q (fresh (x₀ x ...)
                (== `(,x₀ ,x ...) q)
                g ...))]
    [(run n q g ...)
     (let ([q (Var 'q)])
       (map (reify q) (run-goal n (conj g ...) q)))]))



