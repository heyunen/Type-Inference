#lang scheme

(require "pmatch.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Core miniKanren

(define-syntax var
  (syntax-rules ()
    ((_ x) (vector x))))

(define-syntax var?
  (syntax-rules ()
    ((_ x) (vector? x))))

(define empty-s '())

(define ext-s-no-check
  (lambda (x v s)
    (cons `(,x . ,v) s)))

(define walk
  (lambda (v s)
    (cond
      [(var? v)
       (let [(a (assq v s))]
         (cond
           [a (walk (cdr a) s)]
           [else v]))]
      [else v])))

(define ext-s
  (lambda (x v s)
    (cond
      ((occurs x v s) #f)
      (else (ext-s-no-check x v s)))))

(define occurs
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v) (or (occurs x (car v) s) (occurs x (cdr v) s)))
        (else #f)))))

(define unify
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
        ((eq? u v) s)
        ((var? u)
         (cond
           ((var? v) (ext-s-no-check u v s))
           (else (ext-s u v s))))
        ((var? v) (ext-s v u s))
        ((and (pair? u) (pair? v))
         (let ((s (unify (car u) (car v) s)))
           (and s (unify (cdr u) (cdr v) s))))
        ((equal? u v) s)
        (else #f)))))

; In an idempotent substitution,
; a variable that appears on the left-hand-side of an association never appears on the rhs.

(define reify
  (lambda (x s)
    (car (reify-s x 0 s))))

(define reify-s
  (lambda (x n s)
    (let ((x (walk x s)))
      (cond
        ((var? x) (let ([v^ (reify-name n)])
                    (list v^ (add1 n) (ext-s x v^ s))))
        ((pair? x) (let* ([r (reify-s (car x) n s)]
                          [u (list-ref r 0)]
                          [n1 (list-ref r 1)]
                          [s1 (list-ref r 2)]
                          [r^ (reify-s (cdr x) n1 s1)]
                          [v (list-ref r^ 0)]
                          [n2 (list-ref r^ 1)]
                          [s2 (list-ref r^ 2)])
                     (list (cons u v) n2 s2)))
        (else (list x n s))))))

(define reify-name
  (lambda (n)
    (string->symbol
     (string-append "t" (number->string n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Environment

(define ext-env
  (lambda (x v s) `((,x . ,v) . ,s)))

(define lookup
  (lambda (x env)
    (let ((slot (assq x env)))
      (cond 
       [(not slot) (error 'lookup "unbound variable ~a" x)]
       [else (cdr slot)]))))

(define env0
  `((zero? . (int -> bool))
    (add1  . (int -> int))
    (sub1  . (int -> int))
    (=     . (int -> (int -> bool)))
    (<=    . (int -> (int -> bool)))
    (<     . (int -> (int -> bool)))
    (>=    . (int -> (int -> bool)))
    (>     . (int -> (int -> bool)))
    (*     . (int -> (int -> int)))
    (-     . (int -> (int -> int)))
    (+     . (int -> (int -> int)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inferencer

(define infer
  (lambda (exp)
    (define infer1
      (lambda (exp env s)
        (pmatch exp
                [`,x (guard (number? x)) (cons 'int s)]
                [`,x (guard (boolean? x)) (cons 'bool s)]
                [`,x (guard (string? x)) (cons 'string s)]
                [`,x (guard (symbol? x)) (cons (lookup x env) s)]
                [`(lambda (,x) ,body) (let* ([t1 (var x)]
                                             [env^ (ext-env x t1 env)]
                                             [r (infer1 body env^ s)]
                                             [t2 (car r)]
                                             [s^ (cdr r)])
                                        (cons `(,t1 -> ,t2) s^))]
                [`(,e1 ,e2) (let* ([r (infer1 e1 env s)]
                                   [t1 (car r)]
                                   [s1 (cdr r)]
                                   [r^ (infer1 e2 env s1)]
                                   [t2 (car r^)]
                                   [s2 (cdr r^)]
                                   [t3 (var 't3)]
                                   [t4 (var 't4)]
                                   [s3 (unify t1 `(,t3 -> ,t4) s2)])
                              (cond
                                [(not s3) `error]
                                [else
                                 (let ([s4 (unify t2 t3 s3)])
                                   (cond
                                     [(not s4) `error]
                                     [else (cons t4 s4)]))]))]
                )))
    (let* ([r (infer1 exp env0 empty-s)]
           [t (car r)]
           [s (cdr r)])
      (reify t s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests

(infer 1)
; => int

(infer #t)
; => bool

(infer '(lambda (v) v))
; => (t0 -> t0)

(infer '(lambda (f) (lambda (x) (f x))))
; => ((t0 -> t1) -> (t0 -> t1))