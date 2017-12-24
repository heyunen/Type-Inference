#lang scheme

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax letv*
  (syntax-rules ()
    [(_ () body ...) (begin body ...)]
    [(_ ([(x0 ...) v0] [x1 v1] ...) body ...)
     (let-values ([(x0 ...) v0])
       (letv* ([x1 v1] ...) body ...))]
    [(_ ([x0 v0] [x1 v1] ...) body ...)
     (letv* ([(x0) v0] [x1 v1] ...) body ...)]))

; mem_assoc : 'a -> ('a * 'b) list -> bool
; Same as List.assoc, but simply return true if a binding exists, and false if no bindings exist for the given key.
(define (mem_assoc v list)
  (if (assoc v list) #t #f))


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
 

; A Husky expression (HExp) is one of:
; – Boolean                           – booleans
; – Number                            – numbers
; – Ident                             – identifiers
; – (list 'if HExp HExp HExp)         – if expressions
; – (list 'fun Ident HExp)            – lambdas
; – (list HExp HExp)                  – function applications
; An Ident is a Symbol other than 'if, or 'fun


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


; A TypeScheme is a (make-scheme [Listof Symbol] Type]
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


(define (TypeEnv->string scm)
  (map (lambda (s)
         (let ([symbol (car s)]
               [scheme (cadr s)])
           (format "~a: ~a" symbol (scheme->string scheme)))) scm))


; A Subst is a [List (list Symbol Type)]
; This is where we keep track of all the type equations we build up while running
; type inference (aka "code detective")
(define (make-Subst symbol type)
  (list (list symbol type)))


(define (lookup-subst subst target)
  (define (helper sub-subst target)
    (cond
      [(null? sub-subst) '()]
      [(eq? (car sub-subst) (tyvar-name target)) sub-subst]
      [else (helper (cdr sub-subst) target)]))
  (cond
    [(null? subst) '()]
    [else (letv* ([x (car subst)]
                  [xs (cdr subst)]
                  [r (helper x target)])
                 (if (null? r)
                     (helper xs target)
                     (cadr r)))]))


(define (Subst->string subst)
  (map (lambda (s)
         (let ([symbol (car s)]
               [type (cadr s)])
           (format "~a: ~a" symbol (type->string type)))) subst))


; (print (type->string (lookup-subst (make-Subst 'X (make-const 'Bool)) (make-tyvar 'X))))


; apply-subst/type : Subst Type -> Type
; Rewrites all types in the given type based on the definitions we have in the substitution
(define (apply-subst/type subst type)
    (cond
    [(const? type) type]
    [(tyvar? type) (let ([r (lookup-subst subst type)])
                     (if (null? r) type r))]
    [(arrow? type) (make-arrow (apply-subst/type subst (arrow-arg type)) (apply-subst/type subst (arrow-ret type)))]))


; a substitution δ = [X := Y]
; apply δ to the type X
; δ(X) = Y
; (type->string (apply-subst/type (make-Subst 'X (make-tyvar 'Y)) (make-tyvar 'X)))


; a substitution δ = [X := Y]
; apply δ to the type Z
; δ(X) = Z
; (type->string (apply-subst/type (make-Subst 'X (make-tyvar 'Y)) (make-tyvar 'Z)))


; a substitution δ = [X -> Bool]
; apply δ to the type X -> X
; δ(X -> X) = Bool -> Bool
; (type->string (apply-subst/type (make-Subst 'X (make-const 'Bool)) (make-arrow (make-tyvar 'X) (make-tyvar 'X))))


; apply-subst/scheme : Subst TypeScheme -> TypeScheme
; Rewrites all the types inside the given type scheme based on the substitution
; but does *not* rewrite the type variables that are bound by the scheme itself
(define (apply-subst/scheme subst scm)
  (make-scheme (scheme-vars scm) (apply-subst/type subst (scheme-type scm))))


; (scheme->string (apply-subst/scheme (make-Subst 'X (make-const 'Bool)) (make-scheme '(X) (make-arrow (make-tyvar 'X) (make-tyvar 'X)))))


; apply-subst/env : Subst TypeEnv -> TypeEnv
; Rewrites all the types in the type environment
(define (apply-subst/env subst tenv)
  (map (lambda (t)
         (let ([symbol (car t)]
               [scheme (cadr t)])
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


(Subst->string (compose-subst (list (list 'α (make-arrow (make-tyvar 'α1) (make-tyvar 'α2))) (list 'β (make-tyvar 'τ)))
                              (list (list 'α1 (make-tyvar 'β)) (list 'β (make-tyvar 'α2)))))
                             

