#lang racket/base

(require racket/match
         racket/string
         racket/dict)

#|

Implementation of an AD system for the following (minimal) language:

<num> ::= number?
<var> ::= symbol?
<prim> ::= add | sub | neg | mul | div | exp

<expr> ::= <num>
         | <var>
         | (<prim> <expr> ...)
         | (let (<var> <expr>) <expr>)
|#


(struct Expr () #:transparent)
(struct Num Expr (val) #:transparent)
(struct Var Expr (var) #:transparent)
(struct App Expr (p args) #:transparent)
(struct Let Expr (var e1 e2) #:transparent)

(define (parse prog)
  (match prog
    [(? number? val) (Num val)]
    [(? symbol? var) (Var var)]
    [(list 'let (list (? symbol? var) e1) e2)
     (Let var (parse e1) (parse e2))]
    [(list p es ...) (App p (map parse es))]))

(define (unparse expr)
  (match expr
    [(Num val) (number->string val)]
    [(Var var) (symbol->string var)]
    [(App p es)
     (string-append "("
                    (string-join (cons (symbol->string p)
                                       (map unparse es)))
                    ")")]
    [(Let v e1 e2)
     (string-append "(let ("
                    (symbol->string v) " " (unparse e1) ") "
                    (unparse e2) ")")]))

(define (eval expr env prims)
  (match expr
    [(Num val) val]
    [(Var var) (dict-ref env var)]
    [(App p es)
     (let ([vs (map (λ (e) (eval e env prims)) es)])
       (apply (dict-ref prims p) vs))]
    [(Let var e1 e2)
     (let ([v (eval e1 env prims)])
       (eval e2 (dict-set env var v) prims))]))

(define libMaths
  (make-immutable-hash
   `(
     ;; Arithmetic
     [add . ,(λ (x y) (+ x y))]
     [sub . ,(λ (x y) (- x y))]
     [neg . ,(λ (x) (- x))]
     [mul . ,(λ (x y) (* x y))]
     [div . ,(λ (x y) (/ x y))]
     ;; Exponential
     [exp . ,(λ (x) (exp x))])))

;; (define (deriv expr var derivs)
;;   )


(define (mulE e1 e2)
  (App 'mul (list e1 e2)))

(define (reduce proc xs)
  (cond 
    [(null? xs) (raise-argument-error 'reduce "A non-empty list" xs)]
    [(null? (cdr xs)) (car xs)]
    [(proc (car xs) (reduce proc (cdr xs)))]))

(define (sumEs es)
  (reduce (λ (x y) (App 'add (list x y))) es))



;; (define (optimise expr) ...)



;; Testing

(module+ test

  (require plot)
  
  (define g-expr
    (parse '(exp (neg (let (d (mul x x)) (div d 2))))))

  (define (g x)
    (eval g-expr (list (cons 'x x)) libMaths))

  (plot
   (list (axes)
         (function g -3 3
                   #:y-min 0
                   #:label "y = g(x)")))


  )
