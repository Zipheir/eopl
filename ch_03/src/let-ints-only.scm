;;;; The basic LET language from chapter 3, but with integers as its
;;;; only expressed values. (Ex. 3.13)

;;;; Parser not included.

(import (rnrs records syntactic (6)))

(define-record-type program
  (fields exp1))

;;; Expressions

;;; These exp- field names suck.

(define-record-type const-exp
  (fields num))

(define-record-type diff-exp
  (fields exp1 exp2))

(define-record-type zero?-exp
  (fields exp1))

(define-record-type if-exp
  (fields exp1 exp2 exp3))

(define-record-type var-exp
  (fields var))

(define-record-type let-exp
  (fields var exp1 body))

(define (expression? obj)
  (or (const-exp? obj)
      (diff-exp? obj)
      (zero?-exp? obj)
      (if-exp? obj)
      (var-exp? obj)
      (let-exp? obj)))

;;; Checking constructors.

(define (a-program exp1)
  (assert (expression? exp1))
  (make-program exp1))

(define (const-exp num)
  (assert (number? num))
  (make-const-exp num))

(define (diff-exp exp1 exp2)
  (assert (expression? exp1))
  (assert (expression? exp2))
  (make-diff-exp exp1 exp2))

(define (zero?-exp exp1)
  (assert (expression? exp1))
  (make-zero?-exp exp1))

(define (if-exp exp1 exp2 exp3)
  (assert (expression? exp1))
  (assert (expression? exp2))
  (assert (expression? exp3))
  (make-if-exp exp1 exp2 exp3))

(define (var-exp var)
  (assert (symbol? var))
  (make-var-exp var))

(define (let-exp var exp1 body)
  (assert (symbol? var))
  (assert (expression? exp1))
  (assert (expression? body))
  (make-let-exp var exp1 body))

;;; Expressed values

(define-record-type num-val
  (fields num))

(define (num-val num)
  (assert (number? num))
  (make-num-val num))

(define (expval? obj) (num-val? obj))

;; expval->num : Exp-val → Int
(define (expval->num val)
  (if (num-val? val)
      (num-val-num val)
      (report-expval-extractor-error 'num val)))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;;; A-list environments from earlier exercise

;; Budget list?.
(define (pair-or-null? obj)
  (or (pair? obj) (null? obj)))

;; empty-env : () → Env
(define (empty-env) '())

;; environment? : Scheme-val → Bool
(define (environment? obj)
  (pair-or-null? obj))

;; extend-env : Var × Scheme-val × Env → Env
(define (extend-env var val env)
  (assert (symbol? var))
  (assert (expval? val))
  (assert (pair-or-null? env))
  (cons (cons var val) env))

;; apply-env : Env × Var → Scheme-val
(define (apply-env env search-var)
  (assert (pair-or-null? env))
  (assert (symbol? search-var))
  (cond ((assv search-var env) => cdr)
        (else (report-no-binding-found search-var))))

(define (report-no-binding-found var)
  (error 'apply-env "no binding found" var))

;; Cheap conversion!
;; alist->env : List-of(Var × Scheme-val) → Env
(define (alist->env as)
  (assert (pair-or-null? as))
  as)

;;; Initial environment

;; init-env : () → Env
;; Usage: (init-env) = [i = ⌈1⌉, v = ⌈5⌉, x = ⌈10⌉]
(define (init-env)
  (alist->env `((i . ,(num-val 1))
                (v . ,(num-val 5))
                (x . ,(num-val 10)))))

;;; Main interpreter

;; Uncomment when a scanner/parser becomes available.
;; run : String → Exp-val
;; (define (run s)
;;   (value-of-program (scan&parse s)))

;; value-of-program : Program → Exp-val
(define (value-of-program pgm)
  (assert (program? pgm))
  (value-of (program-exp1 pgm) (init-env)))

;; value-of : Exp × Env → Exp-val
(define (value-of exp env)
  (assert (expression? exp))
  (assert (environment? env))
  (cond ((const-exp? exp) (num-val (const-exp-num exp)))
        ((var-exp? exp) (apply-env env (var-exp-var exp)))
        ((diff-exp? exp)
         (let ((val1 (value-of (diff-exp-exp1 exp) env))
               (val2 (value-of (diff-exp-exp2 exp) env)))
           (let ((num1 (expval->num val1))
                 (num2 (expval->num val2)))
             (num-val (- num1 num2)))))
        ((zero?-exp? exp)
         (let ((val (value-of (zero?-exp-exp1 exp) env)))
           (if (zero? (expval->num val))
               (num-val 1)
               (num-val 0))))
        ((if-exp? exp)
         (let ((test-val (value-of (if-exp-exp1 exp) env)))
           (if (zero? (expval->num test-val))
               (value-of (if-exp-exp3 exp) env)
               (value-of (if-exp-exp2 exp) env))))
        ((let-exp? exp)
         (let ((val (value-of (let-exp-exp1 exp) env)))
           (value-of (let-exp-body exp)
                     (extend-env (let-exp-var exp) val env))))
        (else (error 'value-of "invalid expression" exp))))
