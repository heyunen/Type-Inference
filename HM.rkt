#lang scheme

(require "pmatch.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (union a b)
  (cond ((null? b) a)
        ((member (car b) a)
         (union a (cdr b)))
        (else (union (cons (car b) a) (cdr b)))))


(define (difference s1 s2)
  (cond ((null? s1)
         '())
        ((not (member (car s1) s2))
         (cons (car s1) (difference (cdr s1) s2)))
        (else
         (difference (cdr s1) s2))))


; mem_assoc : 'a -> ('a * 'b) list -> bool
; Same as List.assoc, but simply return true if a binding exists, and false if no bindings exist for the given key.
(define (mem_assoc v list)
  (if (assoc v list) #t #f))


; mem : 'a -> 'a list -> bool
; mem a l is true if and only if a is equal to an element of l.
(define (mem v list)
  (if (member v list) #t #f))


; zip : [List X] [List Y] -> [List (list X Y)]
; zip combines two lists into a list of 2-item lists
(define (zip l1 l2)
  (cond
    [(or (empty? l1) (empty? l2)) empty]
    [else (cons (list (first l1) (first l2))
                (zip (rest l1) (rest l2)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Hindley-Milner type inference
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A [Pair X Y] is a (make-pair X Y)
(define-struct pair (fst snd))


; remove-duplicates : [List X] -> [List X]
; removes all but the last copy of any duplicates in a list
(define (remove-duplicates lst)
  (cond
    [(empty? lst) lst]
    [(member (first lst) (rest lst)) (remove-duplicates (rest lst))]
    [else (cons (first lst) (remove-duplicates (rest lst)))]))
 

; A Type is one of
; – (make-const Symbol) – named types, like Number or Boolean
; – (make-arrow Type Type) – a one-argument arrow type, like [X -> Y]
; – (make-tyvar Symbol) – a type variable, like X
(define-struct const (name))
(define-struct arrow (arg ret))
(define-struct tyvar (name))


; type->string : Type -> String
; Outputs the type as an easily-readable string
(define (type->string type)
  (cond
    [(const? type) (format "~a" (const-name type))]
    [(tyvar? type) (format "~a" (tyvar-name type))]
    [(arrow? type) (format "[~a -> ~a]" (type->string (arrow-arg type)) (type->string (arrow-ret type)))]))


; A TypeScheme is a (make-scheme [Listof Symbol] Type)
; and is a polymorphic type of the form "Forall X, Y, Z, <some type>"
; Technically, the "type" [X -> X] is not well-formed, because X isn't defined
; but the type scheme "Forall X, [X -> X]" is well-formed.
(define-struct scheme (vars type))


; scheme->string : TypeScheme -> String
; Outputs a readable version of a TypeScheme
(define (scheme->string scm)
  (format "Forall ~a, ~a"
          (foldr (λ (s1 s2) (if (string=? s2 "")
                                s1
                                (string-append s1 ", " s2)))
                 ""
                 (map symbol->string (scheme-vars scm)))
          (type->string (scheme-type scm))))


; A TypeEnv is a [List (list Symbol Scheme)]
; A type environment records the (polymorphic) types for predefined functions, or
; the types of function parameters available in the bodies of functions
(define (make-TypeEnv symbol scheme)
  (list (list symbol scheme)))


(define (TypeEnv->string tenv)
  (map (lambda (s)
         (let ([symbol (car s)]
               [scheme (cadr s)])
           (format "~a: ~a" symbol (scheme->string scheme)))) tenv))


; A Subst is a [List (list Symbol Type)]
; This is where we keep track of all the type equations we build up while running
; type inference (aka "code detective")
(define (make-Subst symbol type)
  (list (list symbol type)))


(define nullSubst '())


(define (Subst->string subst)
  (map (lambda (s)
         (let ([symbol (car s)]
               [type (cadr s)])
           (format "~a: ~a" symbol (type->string type)))) subst))


; apply-subst/type : Subst Type -> Type
; Rewrites all types in the given type based on the definitions we have in the substitution
(define (apply-subst/type subst type)
  (cond
    [(const? type) type]
    [(tyvar? type) (let ([r (assq (tyvar-name type) subst)])
                     (if r
                         (cadr r)
                         type))]
    [(arrow? type) (make-arrow (apply-subst/type subst (arrow-arg type)) (apply-subst/type subst (arrow-ret type)))]))


;(type->string (apply-subst/type (list (list 'X (make-tyvar '1)) (list 'Y (make-tyvar '2))) (make-arrow (make-tyvar 'X) (make-tyvar 'Y))))


; a substitution δ = [X := Y]
; apply δ to the type X
; δ(X) = Y
;(type->string (apply-subst/type (make-Subst 'X (make-tyvar 'Y)) (make-tyvar 'X)))


; a substitution δ = [X := Y]
; apply δ to the type Z
; δ(X) = Z
; (type->string (apply-subst/type (make-Subst 'X (make-tyvar 'Y)) (make-tyvar 'Z)))


; a substitution δ = [X -> Bool]
; apply δ to the type X -> X
; δ(X -> X) = Bool -> Bool
; (type->string (apply-subst/type (make-Subst 'X (make-const 'Bool)) (make-arrow (make-tyvar 'X) (make-tyvar 'X))))

; (type->string (apply-subst/type (list (list 'α1 (make-tyvar 'β)) (list 'β (make-tyvar 'α2))) (make-tyvar 'β)))


; apply-subst/scheme : Subst TypeScheme -> TypeScheme
; Rewrites all the types inside the given type scheme based on the substitution
; but does *not* rewrite the type variables that are bound by the scheme itself
(define (apply-subst/scheme subst scm)
  (make-scheme (scheme-vars scm) (apply-subst/type subst (scheme-type scm))))


; (scheme->string (apply-subst/scheme (make-Subst 'X (make-const 'Bool)) (make-scheme '(X) (make-arrow (make-tyvar 'X) (make-tyvar 'X)))))


; apply-subst/env : Subst TypeEnv -> TypeEnv
; Rewrites all the types in the type environment
(define (apply-subst/env subst tenv)
  (map (lambda (x)
         (let ([symbol (car x)]
               [scheme (cadr x)])
           (list symbol (apply-subst/scheme subst scheme)))) tenv))


; (TypeEnv->string (apply-subst/env (make-Subst 'X (make-const 'Bool)) (make-TypeEnv 'X (make-scheme '(X) (make-arrow (make-tyvar 'X) (make-tyvar 'X))))))


; apply-subst/subst : Subst Subst -> Subst
; Rewrites all the types in the second substitution, using definitions from the first substitution
(define (apply-subst/subst subst1 subst2) '())


; compose-subst : Subst Subst -> Subst
; Combines two substitutions into one:
; first by applying the first substitution to the second,
; and then just appending that to the first

; s1 is any substitution in sub1
; s2 is any substitution in sub2
; if s2 associates symbol with type, then apply sub1 to type.
; if s1 associates symbol with type and symbol is not in the domain of sub2, then use s1.
(define (compose-subst sub1 sub2)
  (append (map (lambda (s)
                 (let ([symbol (car s)]
                       [type (cadr s)])
                   (list symbol (apply-subst/type sub1 type)))) sub2)
          (filter (lambda (s)
                    (let ([symbol (car s)]
                          [type (cadr s)])
                      (not (mem_assoc symbol sub2)))) sub1)))


; ("α: [α1 -> α2]" "β: τ")
; ("α1: β" "β: α2")
; (Subst->string (compose-subst (list (list 'α (make-arrow (make-tyvar 'α1) (make-tyvar 'α2))) (list 'β (make-tyvar 'τ)))
;                               (list (list 'α1 (make-tyvar 'β)) (list 'β (make-tyvar 'α2)))))


; ftv/type : Type -> [List Type]
; ftv/type, which will take in a Type and output all of the free type variables in it.
(define (ftv/type type)
  (cond
    [(const? type) '()]
    [(tyvar? type) (list type)]
    [(arrow? type) (union (ftv/type (arrow-arg type)) (ftv/type (arrow-ret type)))]))


; (map type->string (ftv/type (make-arrow (make-tyvar 'α1) (make-tyvar 'α2))))


; occurs? : Symbol -> Type -> Bool
; occurs?, which will take in a Symbol and a Type and determine if it occurs in the free type variables of the type.
(define (occurs? symbol type)
  (define (helper ftv-lst)
    (cond
      [(null? ftv-lst) #f]
      [(eq? (tyvar-name (car ftv-lst)) symbol) #t]
      [else (helper (cdr ftv-lst))]))
  (helper (ftv/type type)))


; ftv/scheme : TypeScheme -> [List Type]
; ftv/scheme, which will take in a TypeScheme and output all of the free type variables in its type that are not bound by the scheme’s variables.
(define (ftv/scheme scheme)
  (filter (lambda (type)
            (not (mem (tyvar-name type) (scheme-vars scheme)))) (ftv/type (scheme-type scheme))))

; (map type->string (ftv/scheme (make-scheme '(X) (make-arrow (make-tyvar 'X) (make-tyvar 'X)))))


; ftv/env : TypeEnv -> [List Type]
; ftv/env, which will compute all of the free type variables in a TypeEnv.
; Note that the symbols in the TypeEnv just give types to named terms,
; and those names have nothing to do with the free type variables in an environment.
(define (ftv/env tenv)
  (map (lambda (x)
         (let ([scheme (cadr x)])
           (ftv/type (scheme-type scheme)))) tenv))


; binding : Symbol -> Type -> Subst
; the function bind, which will take in a Symbol and Type,
; and will make a Subst binding the type that symbol.
(define (binding symbol type)
  (cond
    [(and (tyvar? type) (eq? (tyvar-name type) symbol)) nullSubst]
    [(occurs? symbol type) '(error (format "Infinite types: ~a and ~a" binding (type->string type)))]
    [else (make-Subst symbol type)]))


; (binding 'X (make-tyvar 'X))
; (binding 'X (make-arrow (make-tyvar 'X) (make-tyvar 'Y)))
; (Subst->string (binding 'X (make-tyvar 'Y)))


; unify : Type -> Type -> Subst
; the function unify, which will take in two Types and will determine whether or not the types are compatible.
; In other words, it will output a Subst, if possible, that will bind the free type variables inside the types so that they become identical.
(define (unify t1 t2)
  (cond
    [(tyvar? t1) (make-Subst (tyvar-name t1) t2)]
    [(tyvar? t2) (make-Subst (tyvar-name t2) t1)]
    [(and (const? t1) (const? t2)) (if (eq? (const-name t1) (const-name t2))
                                       nullSubst
                                       (error (format "Incompatible type constants: ~a and ~a" (type->string t1) (type->string t2))))]
    [(and (arrow? t1) (arrow? t2)) (let*
                                    ([s1 (unify (arrow-arg t1) (arrow-arg t2))]
                                     [s2 (unify (apply-subst/type s1 (arrow-ret t1)) (apply-subst/type s1 (arrow-ret t2)))])
                                    (compose-subst s1 s2))]
    [else (error (format "Incompatible types: ~a and ~a" (type->string t1) (type->string t2)))]))


; (unify (make-const 'Number) (make-const 'Boolean))
; (unify (make-arrow (make-tyvar 'A) (make-const 'Number)) (make-arrow (make-const 'Boolean) (make-tyvar 'A)))
; (unify (make-const 'Oops) (make-arrow (make-tyvar 'X) (make-tyvar 'Y)))

; (A -> B) -> C
; D -> E
; (Subst->string (unify (make-arrow (make-arrow (make-tyvar 'A) (make-tyvar 'B)) (make-tyvar 'C)) (make-arrow (make-tyvar 'D) (make-tyvar 'E))))


(define gensym
  (let ([counter 0])
    (lambda ([x 'g])
      (if (number? x)
        (set! counter x)
        (begin0 (string->unreadable-symbol
                 (format "~a~a" x counter))
          (set! counter (add1 counter)))))))


(define (fresh-tyvar)
  (make-tyvar (gensym 'X)))


; instantiate : TypeScheme -> Type
; Given a polymorphic type scheme, create some instantiation of it
; by making up brand new (gensym'ed) type variables for it, and substituting them where needed
(define (instantiate scm)
  (let* ([vars (scheme-vars scm)]
          [type (scheme-type scm)]
          [nvars (map (lambda (x) (make-tyvar (gensym x))) vars)]
          [subst (zip vars nvars)])
         (apply-subst/type subst type)))


; (type->string (instantiate (make-scheme '(X) (make-arrow (make-tyvar 'X) (make-tyvar 'X)))))


; generalize : TypeEnv Type -> TypeScheme
; produce a TypeScheme that binds the free variables in the type
; The function generalize abstracts a type over all type variables, which are free in the type but not free in the given type environment.
(define (generalize env type)
  (let ([vars (difference (ftv/type type) (ftv/env env))])
    (make-scheme vars type)))


; lookup-env : TypeEnv -> Symbol -> [Pair Subst Type]
(define (lookup-env tenv symbol)
  (cond
    [(null? tenv) (error (format "Unbound identifier: ~a" symbol))]
    [(eq? (caar tenv) symbol) (pair nullSubst (instantiate (cadar tenv)))]
    [else (lookup-env (cdr tenv) symbol)]))


; (lookup-env (make-TypeEnv 'X (make-scheme '(X) (make-arrow (make-tyvar 'X) (make-tyvar 'X)))) 'X)


; A Husky expression (HExp) is one of:
; – Boolean                           – booleans
; – Number                            – numbers
; – Ident                             – identifiers
; – (list 'if HExp HExp HExp)         – if expressions
; – (list 'fun Ident HExp)            – lambdas
; – (list HExp HExp)                  – function applications
; An Ident is a Symbol other than 'if, or 'fun


; ((fun (abs) (list (abs (- 5 7)) (abs (- 7 5)))))
; (fun (x) (if (< x 0) (- x) x))


(define NUM (make-const 'Number))
(define BOOL (make-const 'Bool))


; infer : TypeEnv -> HExp -> [Pair Subst Type]
(define (infer env exp)
  (pmatch exp
          [`,n (guard (integer? n)) (make-pair nullSubst NUM)]
          [`,x (guard (boolean? x)) (make-pair nullSubst BOOL)]
          [`,var (guard (symbol? var)) (lookup-env env var)]
          [`(fun (,id) ,body) (let* ([tv (fresh-tyvar)]
                                     [env^ (cons (list id (make-scheme '() tv)) env)]
                                     [r (infer env^ body)]
                                     [s1 (pair-fst r)]
                                     [t1 (pair-snd r)])
                                (make-pair s1 (make-arrow (apply-subst/type s1 tv) t1)))]
          [`(,rator ,rand) (let* ([tv (fresh-tyvar)]
                                  [r1 (infer env rator)]
                                  [s1 (pair-fst r1)]
                                  [t1 (pair-snd r1)]
                                  [r2 (infer (apply-subst/env s1 env) rand)]
                                  [s2 (pair-fst r2)]
                                  [t2 (pair-snd r2)]
                                  [s3 (unify (apply-subst/type s2 t1) (make-arrow t2 tv))])
                             (make-pair (compose-subst s3 (compose-subst s2 s1)) (apply-subst/type s3 tv)))]))


; cleanup-vars/scheme : TypeScheme -> TypeScheme
; takes the relatively ugly type names we get from gensym, and cleans them all up
(define (cleanup-vars/scheme scheme)
  (local ((define ftvs (ftv/type (scheme-type scheme)))
          (define new-vars (build-list (length ftvs) (lambda (n) (make-tyvar (string->symbol (format "X~a" n))))))
          (define subst (zip ftvs new-vars)))
    (make-scheme (map tyvar-name new-vars)
                 (apply-subst/type subst (scheme-type scheme)))))


(define (rename-vars/scheme scheme)
  (local ((define ftvs  (foldl (lambda (x y) (cons (tyvar-name x) y)) '() (ftv/type (scheme-type scheme))))
          (define new-vars (build-list (length ftvs) (lambda (n) (make-tyvar (string->symbol (format "X~a" n))))))
          (define subst (zip ftvs new-vars)))
    (make-scheme (map tyvar-name new-vars)
                 (apply-subst/type subst (scheme-type scheme)))))


; infer-type : TypeEnv HExp -> TypeScheme
; Computes the most general type scheme for the given Husky expression in the given environment
(define (infer-type env exp)
  (local ((define result (infer env exp)))
    (generalize empty (apply-subst/type (pair-fst result) (pair-snd result)))))


(define test (compose scheme->string rename-vars/scheme))


(define TYENV0 (list (list 'and (make-scheme '() (make-arrow BOOL (make-arrow BOOL BOOL))))
                     (list '+ (make-scheme '() (make-arrow NUM (make-arrow NUM NUM))))
                     (list '- (make-scheme '() (make-arrow NUM (make-arrow NUM NUM))))
                     (list '< (make-scheme '() (make-arrow NUM (make-arrow NUM BOOL))))
                     (list 'add1 (make-scheme '() (make-arrow NUM NUM)))
                     (list 'zero? (make-scheme '() (make-arrow NUM BOOL)))
                     (list 'compose (make-scheme '(X Y Z)
                                                 (make-arrow (make-arrow (make-tyvar 'Y) (make-tyvar 'Z))
                                                             (make-arrow (make-arrow (make-tyvar 'X) (make-tyvar 'Y))
                                                                         (make-arrow (make-tyvar 'X) (make-tyvar 'Z))))))))



;; I
(test (infer-type '() '(fun (x) x)))

;; K
(test (infer-type '() '(fun (x) (fun (y) x))))

;; S
(test (infer-type '() '(fun (x) (fun (y) (fun (z) ((x z) (y z)))))))

;; 2
(test (infer-type '() '(fun (f) (fun (x) (f (f x))))))

;; 2 * 2
(test (infer-type '() '((fun (f) (fun (x) (f (f x))))
         (fun (f) (fun (x) (f (f x)))))))


(test (infer-type '() '(fun (x) (x 1))))

;; compose
(test (infer-type '() '(fun (g) (fun (f) (fun (x) (g (f x)))))))
