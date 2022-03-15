;;;; LET extended with list operations (ex. 3.9)

(import (rnrs records syntactic (6)))

(include "pmatch.scm")

(define-record-type program
  (fields exp1))

;;; Expressions

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

;; Not bothering with checking constructors.

(define-record-type (empty-list-exp empty-list-exp empty-list-exp?))

(define-record-type (cons-exp cons-exp cons-exp?)
  (fields obj-exp list-exp))

(define-record-type (car-exp car-exp car-exp?)
  (fields exp1))

(define-record-type (cdr-exp cdr-exp cdr-exp?)
  (fields exp1))

(define-record-type (null?-exp null?-exp null?-exp?)
  (fields exp1))

(define (expression? obj)
  (or (const-exp? obj)
      (diff-exp? obj)
      (zero?-exp? obj)
      (if-exp? obj)
      (var-exp? obj)
      (let-exp? obj)
      (empty-list-exp? obj)
      (cons-exp? obj)
      (car-exp? obj)
      (cdr-exp? obj)
      (null?-exp? obj)))

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

(define-record-type bool-val
  (fields bool))

(define (bool-val bool)
  (assert (boolean? bool))
  (make-bool-val bool))

(define-record-type (list-val list-val list-val?)
  (fields list))

(define (expval? obj)
  (or (num-val? obj) (bool-val? obj) (list-val? obj)))

;; expval->num : Exp-val → Int
(define (expval->num val)
  (if (num-val? val)
      (num-val-num val)
      (report-expval-extractor-error 'num val)))

;; expval->bool : Exp-val → Bool
(define (expval->bool val)
  (if (bool-val? val)
      (bool-val-bool val)
      (report-expval-extractor-error 'bool val)))

;; expval->list : Exp-val → list
(define (expval->list val)
  (if (list-val? val)
      (list-val-list val)
      (report-expval-extractor-error 'list val)))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;;; The expressed empty list is a constant.

(define null-val (list-val '()))

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
               (bool-val #t)
               (bool-val #f))))
        ((if-exp? exp)
         (let ((test-val (value-of (if-exp-exp1 exp) env)))
           (if (expval->bool test-val)
               (value-of (if-exp-exp2 exp) env)
               (value-of (if-exp-exp3 exp) env))))
        ((let-exp? exp)
         (let ((val (value-of (let-exp-exp1 exp) env)))
           (value-of (let-exp-body exp)
                     (extend-env (let-exp-var exp) val env))))
        ;; List stuff (new)
        ((empty-list-exp? exp) null-val)
        ;; Note: The new car value is not converted!
        ((cons-exp? exp)
         (let ((ov (value-of (cons-exp-obj-exp exp) env))
               (lv (value-of (cons-exp-list-exp exp) env)))
           (list-val (cons ov (expval->list lv)))))
        ;; Note: The car value is not converted!
        ((car-exp? exp)
         (let* ((val (value-of (car-exp-exp1 exp) env))
                (xs (expval->list val)))
           (if (null? xs)
               (error 'value-of "car: empty list" xs)
               (car xs))))
        ((cdr-exp? exp)
         (let* ((val (value-of (cdr-exp-exp1 exp) env))
                (xs (expval->list val)))
           (if (null? xs)
               (error 'value-of "car: empty list" xs)
               (list-val (cdr xs)))))
        ((null?-exp? exp)
         (let ((xs (expval->list (value-of (null-exp-exp1 exp) env))))
           (if (null? xs) (bool-val #t) (bool-val #f))))
        (else (error 'value-of "invalid expression" exp))))

;; Parser for a simple S-exp representation.  The f(x, y) notation
;; is converted to the usual prefix form.
;; parse : List → Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) (const-exp n))
    ((- ,s ,t) (diff-exp (parse s) (parse t)))
    ((zero? ,s) (zero?-exp (parse s)))
    ((if ,t ,c ,a) (if-exp (parse t) (parse c) (parse a)))
    (,v (guard (symbol? v)) (var-exp v))
    ((let ,v = ,s in ,b) (let-exp v (parse s) (parse b)))
    (emptylist (empty-list-exp))
    ((cons ,e ,e-lis) (cons-exp (parse e) (parse e-lis)))
    ((car ,e-lis) (car-exp (parse e-lis)))
    ((cdr ,e-lis) (cdr-exp (parse e-lis)))
    ((null? ,e-lis) (null?-exp (parse e-lis)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-program : List → Program
(define (parse-program sexp)
  (make-program (parse sexp)))

;; Unparser for the syntax above.
;; unparse : Exp → List
(define (unparse exp)
  (assert (expression? exp))
  (cond ((const-exp? exp) (const-exp-num exp))
        ((diff-exp? exp) `(- ,(unparse (diff-exp-exp1 exp))
                             ,(unparse (diff-exp-exp2 exp))))
        ((zero?-exp? exp) `(zero? ,(unparse (zero?-exp-exp1 exp))))
        ((if-exp? exp) `(if ,(unparse (if-exp-exp1 exp))
                            ,(unparse (if-exp-exp2 exp))
                            ,(unparse (if-exp-exp3 exp))))
        ((var-exp? exp) (var-exp-var exp))
        ((let-exp? exp)
         `(let ,(let-exp-var exp) = ,(unparse (let-exp-exp1 exp))
           in ,(unparse (let-exp-body exp))))
        (else (error 'unparse "unknown expression type" exp))))

;; unparse-program : Program → List
(define (unparse-program pgm)
  (assert (program? pgm))
  (unparse (program-exp1 pgm)))
