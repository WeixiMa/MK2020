#lang typed/racket/no-check

(require "data.rkt")
(provide unify ∀ ∃ walk)

(define debug #f)


(: take-symbol (→ Quant Var))
(define (take-symbol q)
  (match q
    [(∀ x) x]
    [(∃ x) x]))

(: walk (→ Term Sub Term))
(define (walk t ρ)
  (cond
    [(and (Var? t) (hash-ref ρ t #f))
     =>
     (λ (t) (walk t ρ))]
    [else t]))


(: occurs-free-in? (→ Var Term Boolean))
(define (occurs-free-in? x t)
  (match t
    [`,c
     #:when (constant? c)
     #f]
    [`,y
     #:when (Var? y)
     (eqv? y x)]
    [(Tie y body)
     (and (not (eqv? y x))
          (occurs-free-in? x body))]
    [(App rator rand)
     (or (occurs-free-in? x rator)
         (occurs-free-in? x rand))]
    [`(,a . ,d)
     (or (occurs-free-in? x a)
         (occurs-free-in? x d))]))
(: union (All (A) (→ (Listof A) (Listof A) (Listof A))))
(define (union xs ys)
  (cond
    [(null? xs) ys]
    [(memv (car xs) ys) (union (cdr xs) ys)]
    [else (cons (car xs) (union (cdr xs) ys))]))
(: free-vars (→ Term (Listof Var) (Listof Var)))
(define (free-vars t scope)
  (match t
    [`,c
     #:when (constant? c)
     '()]
    [`,y
     #:when (Var? y)
     (if (memv y scope) '() `(,y))]
    [(Tie y body)
     (free-vars body (cons y scope))]
    [(App rator rand)
     (union (free-vars rator scope)
            (free-vars rand scope))]
    [`(,a . , d)
     (union (free-vars a scope)
            (free-vars d scope))]))
(: β (→ Term Var Term Term))
(define (β target x e)
  (match target
    [`,c
     #:when (constant? c)
     c]
    [`,y
     #:when (Var? y)
     (cond
       [(eqv? y x) e]
       [else target])]
    [(Tie y body)
     (cond
       [(eqv? y x) target]
       [(occurs-free-in? y e)
        (let* ([y^ (fresh y)]
               [body^ (β body y y^)])
          (β (Tie y^ body^) x e))]
       [else (Tie y (β body x e))])]
    [(App rator rand)
     (App (β rator x e) (β rand x e))]
    [`(,a . ,d)
     `(,(β a x e) . ,(β d x e))]))
(: run-β (→ Term Term))
(define (run-β t)
  (match t
    [`,c
     #:when (constant? c)
     c]
    [`,y
     #:when (Var? y)
     y]
    [(Tie x body)
     (Tie x (run-β body))]
    [(App rator rand)
     (let ([rator (run-β rator)]
           [rand (run-β rand)])
       (match rator
         [(Tie x b) (β b x rand)]
         [else (App rator rand)]))]
    [`(,a . , d)
     `(,(run-β a) . ,(run-β d))]))
(: app-subst (→ Var Term (Listof Eqn)
                (Listof Eqn)))
(define (app-subst x t es)
  (match es
    ['() '()]
    [`((,t₁ ,t₂) . ,rest)
     (cons `(,(run-β (β t₁ x t)) ,(run-β (β t₂ x t)))
           (app-subst x t rest))]))

(: replace (All (A) (→ (Listof A) A A (Listof A))))
(define (replace l x x^)
  (cond
    [(null? l) '()]
    [(equal? (car l) x) (cons x^ (cdr l))]
    [else (cons (car l) (replace (cdr l) x x^))]))
(: split-at (All (A) (→ (→ A Boolean) (Listof A) (List (Listof A) (Listof A)))))
(define (split-at p l)
  (match l
    ['() `(() ())]
    [`(,a . ,d)
     (cond
       [(p a) `(() ,l)]
       [else (match (split-at p d)
               [`(,l₁ ,l₂) `(,(cons a l₁) ,l₂)])])]))

(: member (All (A) (→ A (Listof A) (U (Listof A) False))))
(define (member x xs)
  (cond
    [(null? xs) #f]
    [(equal? (car xs) x) xs]
    [else (member x (cdr xs))]))
(: r? (→ (Listof Quant) Term Boolean))
(define (r? qs t)
  (match t
    [`,c
     #:when (constant? c)
     #t]
    [`,y
     #:when (Var? y)
     (and (member (∀ y) qs) #t)]
    [(App rator rand)
     (r? qs rator)]
    [`,p
     #:when (pair? p)
     #t]
    [else #f]))
(: f? (→ (Listof Quant) Term Boolean))
(define (f? qs t)
  (match t
    [`,y
     #:when (Var? y)
     (and (member (∃ y) qs) #t)]
    [(App rator rand)
     (f? qs rator)]
    [else
     #f]))

(: ξ? (→ Eqn Boolean))
(define (ξ? e)
  (or (Tie? (car e))
      (Tie? (car (cdr e))))
  #;
  (match e
    [`((λ (,y₁) ,body₁) (λ (,y₂) ,body₂)) #t]
    [`((λ (,y₁) ,body₁) ,any) #t]
    [`(,any (λ (,y₂) ,body₂)) #t]
    [else #f]))
(: ξ (→ Eqn (List (Listof Quant) Eqn)))
(define (ξ e)
  (when debug (displayln 'ξ))
  (: rip (→ (Listof Var) (Listof Var) Term Term
            (List (Listof Var) (Listof Var) Term Term)))
  (define (rip xs₁ xs₂ body₁ body₂)
    (match `(,body₁ ,body₂)
      [`(,(Tie x₁ b₁) ,(Tie x₂ b₂))
       (rip `(,x₁ . ,xs₁) `(,x₂ . ,xs₂) b₁ b₂)]
      [`(,(Tie x₁ b₁) ,b₂)
       (rip `(,x₁ . ,xs₁) xs₂ b₁ b₂)] 
      [`(,b₁ ,(Tie x₂ b₂))
       (rip xs₁ `(,x₂ . ,xs₂) b₁ b₂)]
      [`(,b₁ ,b₂)
       `(,(reverse xs₁) ,(reverse xs₂) ,body₁ ,body₂)]))
  (: flat (→ (Listof Var) (Listof Var)
             (List (Listof Var) (Listof Var))))
  (define (flat xs ys)
    (cond
      [(eqv? (length xs) (length ys)) (list xs ys)]
      [(> (length xs) (length ys)) (list xs (append ys (list (fresh (Var 'x)))))]
      [else (list (append xs (list (fresh (Var 'x)))) ys)]))
  (: zip (→ (Listof Var) (Listof Var)
            (Listof (Pair Var Var))))
  (define (zip xs ys)
    (cond
      [(null? xs) '()]
      [else (cons `(,(car xs) . ,(car ys))
                  (zip (cdr xs) (cdr ys)))]))
  (match-let* ([`(,t₁ ,t₂) e]
               [`(,xs₁ ,xs₂ ,b₁ ,b₂) (rip '() '() t₁ t₂)]
               [`(,xs₁ ,xs₂) (flat xs₁ xs₂)]
               [ws (map (λ (x) (fresh x)) xs₁)]
               [b₁ (foldr (λ ([pr : (Pair Var Var)]
                              [t : Term])
                            (β t (car pr) (cdr pr)))
                          b₁ (zip xs₁ ws))]
               [b₂ (foldr (λ ([pr : (Pair Var Var)]
                              [t : Term])
                            (β t (car pr) (cdr pr)))
                          b₂ (zip xs₂ ws))]
               [qs (map (λ (x) (∀ x)) ws)])
    (list qs (list b₁ b₂))))
(: rr? (→ (Listof Quant) Eqn Boolean))
(define (rr? qs e)
  (match e
    [`(,t₁ ,t₂)
     (or (and (App? t₁) (App? t₂) (r? qs t₁) (r? qs t₂))
         (and (constant? t₁) (constant? t₂))
         (and (pair? t₁) (pair? t₂)))]))
(: rr (→ (Listof Quant) Eqn (U (Listof Eqn) False)))
(define (rr qs e)
  (when debug (displayln 'rr))
  (match e
    [`(,c₁ ,c₂)
     #:when (and (constant? c₁) (constant? c₂))
     (and (equal? c₁ c₂) '())]
    [`(,x ,t)
     #:when (Var? x)
     (if (equal? x t) '() `((,x ,t)))]
    [`(,t ,x)
     #:when (Var? x)
     (if (equal? x t) '() `((,x ,t)))]
    [`(,(App f₁ a₁) ,(App f₂ a₂))
     #:when (and (Var? f₁) (Var? f₂))
     (and (eqv? f₁ f₂)
          `((,a₁ ,a₂)))]
    [`(,(App f₁ a₁) ,(App f₂ a₂))
     (let ([ans (rr qs `(,f₁ ,f₂))])
       (and ans `((,a₁ ,a₂) . ,ans)))]
    [`((,a₁ . ,d₁) (,a₂ . ,d₂))
     (let ([a (rr qs `(,a₁ ,a₂))])
       (and a
            (let ([d (rr qs `(,d₁ ,d₂))])
              (and d (append a d)))))]
    [`(,(Tie x₁ b₁) ,(Tie x₂ b₂))
     `(,e)]
    [else
     #f]))
(: step1 (→ (Listof Quant) (Listof Eqn)
            (U (List (Listof Quant) (Listof Eqn)) False)))
(define (step1 qs es)
  (when debug (begin (displayln 'step1)
                     (displayln qs)
                     (displayln es)))
  (match (split-at ξ? es)
    [`(,any ())
     (match (split-at (λ ([e : Eqn]) (rr? qs e)) es)
       [`(,any ()) (list qs es)]
       [`(,some (,a . ,d))
        (let ([ans (rr qs a)])
          (and ans
               (step1 qs (append some (append ans d)))))])]
    [`(,some (,a . ,d))
     (match (ξ a)
       [`(,qs^ ,e)
        (step1 (append qs qs^) (append some (cons e d)))])]))

(: raise? (→ (Listof Quant) (U (List Var Var (Listof Var)) False)))
(define (raise? qs)
  (match (split-at (λ (q) (∃? q)) qs)
    [`(,alls (,ex₁ . ,rest))
     (match (split-at (λ (q) (∀? q)) rest)
       [`(,exs ,rest)
        #:when (not (null? rest))
        (match (split-at (λ (q) (∃? q)) rest)
          [`(,alls (,ex₂ . ,rest))
           (list (take-symbol ex₁)
                 (take-symbol ex₂)
                 (map take-symbol alls))]
          [else #f])]
       [else #f])]
    [else #f]))
(: remove (All (A) (→ A (Listof A) (Listof A))))
(define (remove x xs)
  (cond
    [(null? xs) '()]
    [(equal? (car xs) x) (cdr xs)]
    [else (cons (car xs) (remove x (cdr xs)))]))

(: add-after (All (A) (→ A A (Listof A) (Listof A))))
(define (add-after x y xs)
  (cond
    [(null? xs) '()]
    [(equal? (car xs) x) (cons x (cons y (cdr xs)))]
    [else (cons (car xs) (add-after x y (cdr xs)))]))
(: make-app (→ Term (Listof Term) Term))
(define (make-app x ys)
  (match ys
    ['() x]
    [`(,y) (App x y)]
    [`(,y . ,rest) (make-app (App x y) rest)]))
(: raise (→ (Listof Quant) (Listof Eqn) Sub
            (List (Listof Quant) (Listof Eqn) Sub)))
(define (raise qs es ρ)
  (when debug (displayln 'raise))
  (match (raise? qs)
    [`(,v ,u ,ws)
     (let* ([u^ (fresh u)]
            [qs (add-after (∃ v) (∃ u^) (remove (∃ u) qs))]
            [r (make-app u^ ws)]
            [ρ (hash-set ρ u r)]
            [es (map (λ ([e : Eqn])
                       (match e
                         [`(,t₁ ,t₂)
                          `(,(β t₁ u r) ,(β t₂ u r))]))
                     es)])
       (list qs es ρ))]
    [#f (list qs es ρ)]))
(: precedes? (All (A) (→ (Listof A) A A Boolean)))
(define (precedes? l x y)
  (match (split-at (λ (a) (equal? x a)) l)
    [`(,any ,rest)
     (and (member y rest) #t)]))
(: rands (→ Term (Listof Var)))
(define (rands t)
  (match t
    [(App rator rand)
     #:when (and (not (eqv? rator 'quote)) (Var? rand))
     (cons rand (rands rator))]
    [(App rator rand)
     #:when (not (eqv? rator 'quote))
     (rands rator)]
    [else '()]))
(: get-head (→ Term Var))
(define (get-head t)
  (match t
    [`,y
     #:when (Var? y)
     y]
    [(App rator rand)
     (get-head rator)]))
(: prune? (→ (Listof Quant) Eqn (U (Listof Var) False)))
(define (prune? qs e)
  (: get (→ Term Term (Listof Var)))
  (define (get t₁ t₂)
    (let* ([fv (free-vars t₁ '())]
           [fv (filter (λ ([x : Var]) (member (∀ x) qs)) fv)]
           [fv (filter (λ ([x : Var])
                         (precedes? qs
                                    (∃ (get-head t₂)) (∀ x)))
                       fv)]
           [fv (filter (λ ([x : Var])
                         (not (member x (rands t₂)))) fv)])
      fv))
  (let ([ans (match e
               [`(,t₁ ,t₂)
                (if (f? qs t₁)
                    (get t₂ t₁)
                    (get t₁ t₂))])])
    (and (not (null? ans)) ans)))
(: replace-head-and-remove-x (→ Term Var Var Term))
(define (replace-head-and-remove-x t hd x)
  (match t
    [(App rator rand)
     #:when (Var? rator)
     (if (eqv? rand x)
         hd
         (App hd rand))]
    [(App rator rand)
     (if (eqv? rand x)
         (replace-head-and-remove-x rator hd x)
         (App (replace-head-and-remove-x rator hd x) rand))]))
(: prune (→ (Listof Quant) (Listof Eqn) (Listof Var) Sub
            (U (List (Listof Quant) (Listof Eqn) Sub) False)))
(define (prune qs es vars ρ)
  (when debug (displayln 'pruning))
  (: p (→ Term Var Boolean))
  (define (p t x)
    (match t
      [(App rator rand)
       #:when (Var? rand)
       (or (eqv? rand x)
           (p rator x))]
      [else #f]))
  (: get-term (→ Term Var (U Term False)))
  (define (get-term t x)
    (if (and (f? qs t) (p t x))
        t
        (match t
          [(App rator rand)
           (or (get-term rator x)
               (get-term rand x))]
          [else #f])))
  (: add-binders (→ Term Term Term))
  (define (add-binders t t^)
    (match t
      [(App rator rand)
       #:when (Var? rand)
       (cond
         [(Var? rator) (Tie rand t^)]
         [else (add-binders rator (Tie rand t^))])]))
  (and (foldr (λ ([x : Var] [ans : Boolean])
                (match (split-at (λ ([q : Quant]) (∃? q))
                                 (or (member (∀ x) (reverse qs)) '()))
                  [`(,blah ,what) #t]
                  [else ans]))
              #f
              vars)
       (let* ([ans
               (foldr (λ ([e : Eqn]
                          [ans : (U (List Term Var) False)])
                        (match e
                          [`(,t₁ ,t₂)
                           (let ([e (if (r? qs t₁) `(,t₂ ,t₁) e)])
                             (foldr (λ ([t : Term]
                                        [ans : (U (List Term Var) False)])
                                      (or
                                       (foldr (λ ([x : Var]
                                                  [ans : (U (List Term Var) False)])
                                                (let ([result (get-term t x)])
                                                  (cond
                                                    [result (list result x)]
                                                    [else ans])))
                                              ans
                                              vars)))
                                    ans
                                    e))]))
                      #f
                      es)])
         (and ans
              (match-let* ([`(,t ,x) ans]
                           [hd (get-head t)]
                           [hd^ (fresh hd)]
                           [t^ (replace-head-and-remove-x t hd^ x)]
                           [ans (add-binders t t^)]
                           [ρ (hash-set ρ hd ans)]
                           [es (app-subst hd ans es)]
                           [qs (map (λ ([q : Quant])
                                      (match q
                                        [(∃ x)
                                         #:when (eqv? x hd)
                                         (∃ hd^)]
                                        [else q]))
                                    qs)])
                (list qs es ρ))))))
(: step2 (→ (Listof Quant) (Listof Eqn) Sub
            (U (List (Listof Quant) (Listof Eqn) Sub) False)))
(define (step2 qs es ρ)
  (when debug (begin (displayln 'step2)
                     (displayln qs)
                     (displayln es)))
  (cond
    [(raise? qs)
     (match (raise qs es ρ)
       [(list qs es ρ)
        (step2 qs es ρ)])]
    [else
     (let ([vars
            (ormap (λ ([e : Eqn])
                     (prune? qs e))
                   es)])
       (cond
         [vars
          (match (prune qs es vars ρ)
            [#f #f]
            [(list qs es ρ)
             (step2 qs es ρ)])]
         [else (list qs es ρ)]))]))

(: copy-lambda (→ Term Term Term))
(define (copy-lambda target body)
  (match target
    [(App rator rand)
     #:when (Var? rand)
     (cond
       [(Var? rator) (Tie rand body)]
       [else (copy-lambda rator (Tie rand body))])]))
(: ff (→ (Listof Quant) Eqn
         (U (List (Listof Quant) Var Term) False)))
(define (ff qs e)
  (: get-rands (→ Term (Listof Var) (U (Listof Var) False)))
  (define (get-rands t l)
    (match t
      [`,hd
       #:when (Var? hd)
       l]
      [(App rator rand)
       #:when (Var? rand)
       (get-rands rator (cons rand l))]
      [else
       #f]))
  (: get-same (→ (Listof Var) (Listof Var) (Listof Var)))
  (define (get-same l₁ l₂)
    (cond
      [(null? l₁) '()]
      [(eqv? (car l₁) (car l₂))
       (cons (car l₁) (get-same (cdr l₁) (cdr l₂)))]
      [else (get-same (cdr l₁) (cdr l₂))]))
  (match e
    [`(,hd₁ ,hd₂)
     #:when (and (Var? hd₁) (Var? hd₂))
     (cond
       [(eqv? hd₁ hd₂) (list qs (fresh (Var 'x)) (fresh (Var 'x)))]
       [else (let ([qs (remove (∃ hd₂) qs)])
               (list qs hd₂ hd₁))])]
    [`(,t₁ ,t₂)
     (let* ([hd₁ (get-head t₁)]
            [hd₂ (get-head t₂)]
            [rands₁ (get-rands t₁ '())]
            [rands₂ (get-rands t₂ '())])
       (and rands₁ rands₂ (eqv? (length rands₁) (length rands₂))
            (cond
              [(eqv? hd₁ hd₂)
               (let* ([rands (get-same rands₁ rands₂)]
                      [hd (fresh hd₁)]
                      [t (make-app hd rands)]
                      [t (copy-lambda t₁ t)]
                      [qs (replace qs (∃ hd₁) (∃ hd))])
                 (list qs hd₁ t))]
              [else
               (let ([ans (copy-lambda t₁ t₂)]
                     [qs (remove (∃ hd₁) qs)])
                 (list qs hd₁ ans))])))]))
(: all-different-vars (→ (Listof Var) (Setof Var)
                         Boolean))
(define (all-different-vars ls s)
  (cond
    [(null? ls) #t]
    [(set-member? s (car ls)) #f]
    [else (all-different-vars (cdr ls) (set-add s (car ls)))]))
(: fr (→ (Listof Quant) Eqn
         (U (List (Listof Quant) Var Term) False)))
(define (fr qs e)
  (when debug (displayln 'fr))
  (match e
    [`(,t₁ ,t₂)
     #:when (f? qs t₁)
     (if (Var? t₁)
         (and (not (occurs-free-in? t₁ t₂))
              (list (remove (∃ t₁) qs) t₁ t₂))
         (let* ([hd (get-head t₁)])
           (and (not (occurs-free-in? hd t₂))
                (all-different-vars (rands t₁) (set))
                (list (remove (∃ hd) qs)
                      hd
                      (copy-lambda t₁ t₂)))))]
    [`(,t₁ ,t₂)
     #:when (f? qs t₂)
     (if (Var? t₂)
         (and (not (occurs-free-in? t₂ t₁))
              (list (remove (∃ t₂) qs) t₂ t₁))
         (let* ([hd (get-head t₂)])
           (and (not (occurs-free-in? hd t₁))
                (all-different-vars (rands t₂) (set))
                (list (remove (∃ hd) qs)
                      hd
                      (copy-lambda t₂ t₁)))))]))
(: ff? (→ (Listof Quant) Eqn Boolean))
(define (ff? qs e)
  (match e
    [`(,t₁ ,t₂)
     (and (f? qs t₁) (f? qs t₂))]))
(: fr-rf? (→ (Listof Quant) Eqn Boolean))
(define (fr-rf? qs e)
  (match e
    [`(,t₁ ,t₂)
     (or (f? qs t₁) (f? qs t₂))]))
(: step3 (→ (Listof Quant) (Listof Eqn) Sub
            (U (List (Listof Quant) (Listof Eqn) Sub) False)))
(define (step3 qs es ρ)
  (when debug (begin (displayln 'step3)
                     (displayln qs)
                     (displayln es)
                     (displayln ρ)))
  (match (split-at (λ ([e : Eqn]) (ff? qs e)) es)
    [`(,any (,e . ,rest))
     (match (ff qs e)
       [(list qs x t)
        (let ([es (app-subst x t (append any rest))]
              [ρ (hash-set ρ x t)])
          (step3 qs es ρ))]
       [#f #f])]
    [else (match (split-at (λ ([e : Eqn]) (fr-rf? qs e)) es)
            [`(,any (,e . ,rest))
             (match (fr qs e)
               [(list qs x t)
                (let ([es (app-subst x t (append any rest))]
                      [ρ (hash-set ρ x t)])
                  (step3 qs es ρ))]
               [#f
                #f])]
            [else
             (list qs es ρ)])]))


(: unify (→ (Listof Quant) (Listof Eqn) Sub
            (U (List (Listof Quant) (Listof Eqn) Sub) False)))
(define (unify qs es ρ)
  (when debug (begin (displayln "")
                     (displayln '!!!!unify!!!)
                     (displayln qs)
                     (displayln es)
                     (displayln ρ)))
  (let* (#;[es (map (λ ([e : Eqn]) (map curry e)) es)]
         [es (foldr (λ ([key : Var]
                        [es : (Listof Eqn)])
                      (app-subst key (hash-ref ρ key) es))
                    es (hash-keys ρ))]
         [es (map (λ ([e : Eqn])
                    `(,(run-β (car e)) ,(run-β (car (cdr e))))
                    #;
                    (map run-β e))
                  es)])
    (match (step1 qs es)
      [(list qs es)
       (match (step2 qs es ρ)
         [(list qs es ρ)
          (match (step3 qs es ρ)
            [(list qs es ρ)
             (match (step1 qs es)
               [(list qs es) (list qs es ρ)]
               [#f (when debug (displayln 'fail)) #f])]
            [#f(when debug (displayln 'fail)) #f])]
         [#f(when debug (displayln 'fail)) #f])]
      [#f(when debug (displayln 'fail)) #f])))

#;
(let* ([f (Var 'f)]
      [u (Var 'u)]
      [v (Var 'v)]
      [y (Var 'y)]
      [x (Var 'x)]
      [w (Var 'w)]
      [e₁ (app f (tie (list x) (app f (app u x y))))]
      [e₂ (app f (tie (list w) (app v y)))])
  (unify (list (∀ f) (∃ u) (∃ v) (∀ y))
         (list `(,e₁ ,e₂))
         (make-immutable-hasheqv)))

#;
(unify (list (∀ 'f) (∃ 'u))
       (list '((λ (x) (u x)) (λ (y) (f y))))
       (make-immutable-hasheqv))

