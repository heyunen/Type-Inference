(display "Type inference") (newline)

;;; Parser
(define parse
  (lambda (e)
    (cond
      ((symbol? e) `(var ,e))
      ((number? e) `(intc ,e))
      ((boolean? e) `(boolc ,e))
      (else (case (car e)
              ((zero?) `(zero? ,(parse (cadr e))))
              ((sub1) `(sub1 ,(parse (cadr e))))
              ((+) `(+ ,(parse (cadr e)) ,(parse (caddr e))))
              ((if) `(if ,(parse (cadr e)) ,(parse (caddr e)) ,(parse (cadddr e))))
              ((fix) `(fix ,(parse (cadr e))))
              ((lambda) `(lambda ,(cadr e) ,(parse (caddr e))))
              ((let) `(let ((,(car (car (cadr e))) ,(parse (cadr (car (cadr e))))))
                        ,(parse (caddr e))))
              (else `(app ,(parse (car e)) ,(parse (cadr e)))))))))

(define membero
  (relation (v lt lh)
            (to-show v `(,lh . ,lt))
            (if-some (== v lh) succeed
                     (membero v lt))))

(define env
  (relation (head-let g v t)
            (exists (tq)
                    (all!!
                     (membero `(,v . ,tq) g)
                     (any
                      (== tq `(non-generic ,t))
                      (exists (type-gen)
                              (all!!
                               (== tq `(generic ,type-gen))
                               (project (type-gen)
                                        (type-gen t)))))))))

;;; Rules
(define int 'int)
(define bool 'bool)

(define var-rel
  (relation (g v t)
            (to-show g `(var ,v) t)
            (all! (env g v t))))

(define int-rel
  (fact (g x) g `(intc ,x) int))

(define bool-rel
  (fact (g x) g `(boolc ,x) bool))

(define zero?-rel
  (relation (g x)
            (to-show g `(zero? ,x) bool)
            (all! (!- g x int))))

(define sub1-rel
  (relation (g x)
            (to-show g `(sub1 ,x) int)
            (all! (!- g x int))))

(define +-rel
  (relation (g x y)
            (to-show g `(+ ,x ,y) int)
            (all!! (!- g x int) (!- g y int))))

(define if-rel
  (relation (g t test conseq alt)
            (to-show g `(if ,test ,conseq ,alt) t)
            (all!! (!- g test bool) (!- g conseq t) (!- g alt t))))

(define lambda-rel
  (relation (g v t body type-v)
            (to-show g `(lambda (,v) ,body) `(--> ,type-v ,t))
            (all! (!- `((,v non-generic ,type-v) . ,g) body t))))

(define app-rel
  (relation (g t rand rator)
            (to-show g `(app ,rator ,rand) t)
            (exists (t-rand)
                    (all!! (!- g rator `(--> ,t-rand ,t)) (!- g rand t-rand)))))

(define fix-rel
  (relation (g rand t)
            (to-show g `(fix ,rand) t)
            (all! (!- g rand `(--> ,t ,t)))))

(define polylet-rel
  (relation (g v rand body t)
            (to-show g `(let ((,v ,rand)) ,body) t)
            (all!!
             (exists (some-type) (!- g rand some-type))
             (!- `((,v generic ,(relation (head-let t-rand)
                                          (all!!
                                           (!- g rand t-rand)
                                           (trace-vars 'poly-let (t-rand rand)))))
                   . ,g)
                 body t))))


(define !-
  (extend-relation (a1 a2 a3)
                   var-rel int-rel bool-rel zero?-rel sub1-rel +-rel 
                   if-rel lambda-rel app-rel fix-rel polylet-rel))

;;; Tests
(define test1 (solution (?)
                        (eigen (g)
                               (!- g (parse `(lambda (f)
                                               (lambda (x)
                                                 ((f x) x)))) ?))))

; ((?.0 (--> (--> _.0 (--> _.0 _.1)) (--> _.0 _.1))))
(display test1)
(newline)
(newline)

(define test2 (solution (?)
                      (eigen (g)
                             (!- g
                                 (parse
                                  `((fix (lambda (sum)
                                           (lambda (n)
                                             (+ n (sum (sub1 n))))))
                                    10))
                                 ?))))

; ((?.0 int))
(display test2)
(newline)
(newline)

(define test3 (solution (?)
                        (eigen (g)
                               (!- g
                                   (parse
                                    `(let ([f (lambda (x) x)])
                                       (if (f (zero? 5))
                                           (+ (f 4) 8)
                                           (+ (f 3) 7))))
                                   ?))))

;(if ((lambda (x) x) (zero? 5))
;    (+ ((lambda (x) x) 4) 8)
;    (+ ((lambda (x) x) 3) 7))

; poly-let t-rand: (--> bool bool)
; poly-let rand: (lambda (x) (var x))
; poly-let t-rand: (--> int int)
; poly-let rand: (lambda (x) (var x))
; poly-let t-rand: (--> int int)
; poly-let rand: (lambda (x) (var x))
; ((?.0 int))
(display test3)