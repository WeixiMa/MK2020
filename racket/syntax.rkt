#lang racket

(define-syntax (def stx)
  (syntax-case stx ()
    [(_ name body)
     (with-syntax ([f (string->symbol (string-append (symbol->string 'name) "-body"))]
                   [ext (string->symbol (string-append (symbol->string 'name) "-ext"))])
       #'(begin
           (define f (λ () body))
           (define name f)))]))

(def x (displayln 5))
