;;;; The basic LETREC language from chapter 3, sec. 3.4.

;; Uncomment on Guile.  So much for R6RS compliance.
; (define-syntax assert
;   (syntax-rules ()
;     ((assert exp)
;      (or exp (error "assertion failed" 'exp)))))

(import (rnrs records syntactic (6))
        (rnrs lists (6)))

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

(define-record-type proc-exp
  (fields var body))

(define-record-type call-exp
  (fields rator rand))

(define-record-type letrec-exp
  (fields p-name b-var p-body letrec-body))

(define-syntax match-letrec
  (syntax-rules ()
    ((match-letrec exp (name var pb lb) body)
       (let ((exp* exp))
         (let ((name (letrec-exp-p-name exp*))
               (var (letrec-exp-b-var exp*))
               (pb (letrec-exp-p-body exp*))
               (lb (letrec-exp-letrec-body exp*)))
           body)))))

(define (expression? obj)
  (or (const-exp? obj)
      (diff-exp? obj)
      (zero?-exp? obj)
      (if-exp? obj)
      (var-exp? obj)
      (let-exp? obj)
      (proc-exp? obj)
      (call-exp? obj)
      (letrec-exp? obj)))

;;; Expressed values

(define-record-type num-val
  (fields num))

(define-record-type bool-val
  (fields bool))

(define-record-type proc-val
  (fields proc))

(define (expval? obj)
  (or (num-val? obj) (bool-val? obj) (proc-val? obj)))

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

;; expval->proc : Exp-val → Proc
(define (expval->proc val)
  (if (proc-val? val)
      (proc-val-proc val)
      (report-expval-extractor-error 'proc val)))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;;; Procs

(define-record-type proc
  (fields var body saved-env))

(define procedure make-proc)

;;; Environments

(define-record-type (empty-environment empty-env empty-env?))

(define-record-type (extended-env extend-env extended-env?)
  (fields var val rest-env))

(define-record-type (extended-env-rec extend-env-rec extended-env-rec?)
  (fields p-name b-var p-body env))

(define (environment? obj)
  (or (empty-env? obj)
      (extended-env? obj)
      (extended-env-rec? obj)))

;; apply-env : Env × Var → Scheme-val
(define (apply-env env search-var)
  (cond ((empty-env? env) (report-no-binding-found search-var))
        ((extended-env? env)
         (if (eqv? search-var (extended-env-var env))
             (extended-env-val env)
             (apply-env (extended-env-rest-env env) search-var)))
        ((extended-env-rec? env)
         (if (eqv? search-var (extended-env-rec-p-name env))
             (proc-val (procedure (extended-env-rec-b-var env)
                                  (extended-env-rec-p-body env)
                                  env))
             (apply-env (extended-env-rec-env env) search-var)))
        (else (error 'apply-env "invalid environment" env))))

(define (report-no-binding-found var)
  (error 'apply-env "no binding found" var))

;; alist->env : List-of(Var × Scheme-val) → Env
;; No recursive bindings.
(define (alist->env as)
  (fold-right (lambda (p env) (extend-env (car p) (cdr p) env))
              (empty-env)
              as))

;;; Initial environment

;; init-env : () → Env
;; Usage: (init-env) = [i = ⌈1⌉, v = ⌈5⌉, x = ⌈10⌉]
(define (init-env)
  (alist->env `((i . ,(make-num-val 1))
                (v . ,(make-num-val 5))
                (x . ,(make-num-val 10)))))

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
  (cond ((const-exp? exp) (make-num-val (const-exp-num exp)))
        ((var-exp? exp) (apply-env env (var-exp-var exp)))
        ((diff-exp? exp)
         (let ((val1 (value-of (diff-exp-exp1 exp) env))
               (val2 (value-of (diff-exp-exp2 exp) env)))
           (let ((num1 (expval->num val1))
                 (num2 (expval->num val2)))
             (make-num-val (- num1 num2)))))
        ((zero?-exp? exp)
         (let ((val (value-of (zero?-exp-exp1 exp) env)))
           (if (zero? (expval->num val))
               (make-bool-val #t)
               (make-bool-val #f))))
        ((if-exp? exp)
         (let ((test-val (value-of (if-exp-exp1 exp) env)))
           (if (expval->bool test-val)
               (value-of (if-exp-exp2 exp) env)
               (value-of (if-exp-exp3 exp) env))))
        ((let-exp? exp)
         (let ((val (value-of (let-exp-exp1 exp) env)))
           (value-of (let-exp-body exp)
                     (extend-env (let-exp-var exp) val env))))
        ((proc-exp? exp)
         (make-proc-val (procedure (proc-exp-var exp)
                                   (proc-exp-body exp)
                                   env)))
        ((call-exp? exp)
         (let ((proc (expval->proc (value-of (call-exp-rator exp) env)))
               (arg (value-of (call-exp-rand exp) env)))
           (apply-procedure proc arg)))
        ((letrec-exp? exp)
         (match-letrec exp (proc-name bound-var proc-body letrec-body)
           (value-of letrec-body
                     (extend-env-rec proc-name
                                     bound-var
                                     proc-body
                                     env))))
        (else (error 'value-of "invalid expression" exp))))

;; apply-procedure : Proc × Exp-val → Exp-val
(define (apply-procedure proc1 val)
  (value-of (proc-body proc1)
            (extend-env (proc-var proc1) val (proc-saved-env proc1))))

;; Parser for a simple S-exp representation.
;; parse : List → Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) (make-const-exp n))
    ;; A slightly nicer syntax for diff-exps in an S-exp context.
    ((- ,s ,t) (make-diff-exp (parse s) (parse t)))
    ((zero? ,s) (make-zero?-exp (parse s)))
    ((if ,t ,c ,a) (make-if-exp (parse t) (parse c) (parse a)))
    (,v (guard (symbol? v)) (make-var-exp v))
    ((let ,v = ,s in ,b) (make-let-exp v (parse s) (parse b)))
    ((proc (,v) ,body) (guard (symbol? v))
     (make-proc-exp v (parse body)))
    ((,e1 ,e2) (make-call-exp (parse e1) (parse e2)))
    ((letrec ,name (,v) = ,p-body in ,body)
     (guard (symbol? name) (symbol? v))
     (make-letrec-exp name v (parse p-body) (parse body)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-program : List → Program
(define (parse-program sexp)
  (make-program (parse sexp)))
