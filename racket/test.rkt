#lang racket
(require "lmk.rkt")

#;
(run 1 f
  (== (tie (a) a)
      (tie (b) (app f b b))))

#;
(run 1 q
  (== (tie (a b) (app a b))
      (tie (x y) (app x y))))

#;
(run 1 q
  (== (tie (f) f)
      (tie (g) (tie (a) (app g a)))))

#;
(run 1 f
  (all (a)
    (== a
        (app f a))))


(defrel (appendo xs ys zs)
  (conde
   [(== '() xs) (== ys zs)]
   [(fresh (a d r)
      (== `(,a . ,d) xs)
      (== `(,a . ,r) zs)
      (appendo d ys r))]))

(run 1 q
  (appendo '(1 2 3) q '(1 2 3)))


(defrel (eq x y)
  (conde
   [(== x y)]
   [(fresh (z)
      (eq x z)
      (eq z y))]
   [(eq y x)]))

#;
(run 1 q
  (assume ((eq 'orange q))
          (eq 'apple 'orange)))

(defrel (taken name class)
  (conde
   [(== 'rtz name)
    (== '311 class)]
   [(== 'rtz name)
    (== '211 class)]))

(defrel (graduate name)
  (taken name '311)
  (taken name '211)
  (taken name '411))

#;
(run 1 q
  (assume ((taken 'rtz q))
          (graduate 'rtz)))

#;
(run 1 q
  (all (someone)
    (assume [(taken someone '311)
             (taken someone '411)
             (taken someone '211)]
            (graduate someone))))

#;
(run 1 q
  (all (x)
    (fresh (y)
      (== x y))))

#;
(run 1 f
  (all (x)
    (== x (app f x))))
