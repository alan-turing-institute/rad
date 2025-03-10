#lang racket/base

(require racket/match
         racket/string
         racket/dict)

;; TODO:
;; - Remove sub and div, replace with neg and inv

#|

Implementation of an AD system for the following (minimal) language:

<num>  ::= number?
<var>  ::= symbol?
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

(define Zero (Num 0))
(define One  (Num 1))
(define (Zero? e) (and (Num? e) (= (Num-val e) 0)))
(define (One? e) (and (Num? e) (= (Num-val e) 1)))


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

(define (deriv expr var derivs)
  (match expr
    [(Num _) 
     (Num 0)]
    [(Var v)
     (if (equal? v var) (Num 1) (Num 0))]
    [(App p args)
     (let ([dps (apply (dict-ref derivs p) args)]
           [dargs (map (λ (e) (deriv e var derivs)) args)])
       (sumEs (map mulE dps dargs)))]
    [(Let v E F)
     (if (equal? v var)
         (let ([newv (newsym)])
           (deriv (Let newv E (rename-in F v newv)) var derivs))
         ;; (let ([dFv (newsym)])
         ;; (Let v E
         ;;      (Let dFv (deriv F v derivs)
         ;;           (sumE (deriv F var derivs)
         ;;                 (mulE (Var dFv) (deriv E var derivs))))))
         (Let v E
              (sumE (deriv F var derivs)
                    (mulE (deriv F v derivs) (deriv E var derivs))))

         )]))

(define (mulE e1 e2)
  (App 'mul (list e1 e2)))

(define (sumE e1 e2)
  (App 'add (list e1 e2)))

(define (reduce proc xs)
  (cond 
    [(null? xs) (raise-argument-error 'reduce "A non-empty list" xs)]
    [(null? (cdr xs)) (car xs)]
    [(proc (car xs) (reduce proc (cdr xs)))]))

(define (sumEs es)
  (reduce (λ (x y) (sumE x y)) es))

(define newsym
  (let ([n 0])
    (λ ()
      (begin
        (set! n (+ n 1))
        (string->symbol
         (string-append "$" (number->string n)))))))

;; Rename free occurences of `from` in `expr`
;; Leave bound occurences alone 
(define (rename-in expr from to)
  (match expr
    [(Num _)
     expr]
    [(Var v)
     (if (equal? v from)
         (Var to)
         expr)]
    [(App p args)
     (App p (map (λ (e) (rename-in e from to)) args))]
    [(Let v E F)
     (let ([newE (rename-in E from to)])
       (cond
         [(equal? v from) ; `from` is bound in F (but not in E)
          (Let v newE F)]
         [(equal? v to)   ; renaming should not affect v, so need to rename `from` first
          (let ([freshv (newsym)])
            (Let freshv
                 newE
                 (rename-in (rename-in F v freshv) from to)))]
         [else
          (Let v newE (rename-in F from to))]))]
    [_ expr]))


;; Libraries of primitive functions

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

(define libDeriv
  (make-immutable-hash
   `(
     ;; Arithmetic
     [add . ,(λ (u v) (list (Num 1) (Num 1)))]
     [sub . ,(λ (u v) (list (Num 1) (App 'neg (list One))))]
     [neg . ,(λ (u) (list (App 'neg (list One))))]
     [mul . ,(λ (u v) (list v u))]
     [div . ,(λ (u v) (list
                       (App 'div (list One v))
                       (App 'neg
                            (list (App 'div
                                       (list u (App 'mul (list v v))))))))]
     ;; Exponential
     [exp . ,(λ (u) (list (App 'exp (list u))))]
     )))


;; Constant folding.
;; Any primitive applied to Num's is evaluated
;; let (x v) in E => E[v/x]

(define (optimise expr prims)
  (define (optim expr env)
    (match expr
      [(Num _) ; Numbers return themselves
       expr]
      [(Var v) ; Either look up a let-bound variable or return the variable
       (dict-ref env v expr)]
      [(App p args) 
       (let ([vs (map (λ (e) (optim e env)) args)])
         (if (andmap Num? vs)
             (Num (eval (App p vs) env prims))
             (optimise-primitive (App p vs))))]
      [(Let v E1 E2)
       (let ([e1 (optim E1 env)])
         (if (Num? e1)
           (optim E2 (dict-set env v e1))
           (let ([e2 (optim E2 env)])
             (if (Num? e2)
                 e2
                 (Let v e1 e2)))))])
    )
    ;; in
  (optim expr '()))

(define (optimise-primitive e)
  (match e
    [(App 'add (list (Num 0) x))                         x]
    [(App 'add (list x (Num 0)))                         x]
    [(App 'add (list (Var x) (App 'neg (list (Var x))))) Zero]
    [(App 'mul (list (Num 0) _))                         Zero]
    [(App 'mul (list _ (Num 0)))                         Zero]
    [(App 'mul (list (Num 1) x))                         x]
    [(App 'mul (list x (Num 1)))                         x]
    [(App 'div (list (Num 0) _))                         Zero]
    [(App 'div (list x (Num 1)))                         x]
    [(App 'div (list (Var x) (Var x)))                   One]
    [(App 'neg (list (App 'neg (list x))))               x]
    [_                                                   e]))




;; Testing

(module+ test



  (define libTestDeriv
    (make-immutable-hash
     `(
       ;; Arithmetic
       [f . ,(λ (u) (list (App 'df (list u))))]
       [g . ,(λ (u) (list (App 'dg (list u))))]
       [h . ,(λ (u) (list (App 'dh (list u))))]
       )))

  (require plot)
  
  (define g-expr
    (parse '(exp (neg (div (mul x x) 2)))))
  
  (define (g x)
    (eval g-expr (list (cons 'x x)) libMaths))

  (define dg-expr
    (deriv g-expr 'x libDeriv))
  
  (define (dg x)
    (eval dg-expr `((x . ,x)) libMaths))

  ;; (plot
  ;;  (list (axes)
  ;;        (function dg -3 3
  ;;                  #:label "y = dg(x)")))
  
  (define g-anf
    (parse '(let (x1 (mul x x))
              (let (x2 (div x1 2))
                (let (x3 (neg x2))
                  (exp x3))))))

  )
