;;;; CPS interpreter (Ex. 5.16) for the BASICALLY language of Ch. 4.

(import (rnrs base (6)))

(include "pmatch.scm")
(include "../../src/test.scm")

;;;; Stores

;; Contains the current state of the store.
(define the-store 'uninitialized)

;; empty-store : () -> Sto
(define (empty-store) '())

;; initialize-store! : () -> Unspecified
(define (initialize-store!)
  (set! the-store (empty-store)))

;; reference? : Scheme-val -> Bool
(define (reference? x)
  (integer? x))

;; newref : Exp-val -> Ref
(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val)))
    next-ref))

;; deref : Ref -> Exp-val
(define (deref ref)
  (list-ref the-store ref))

;; setref! : Ref x Exp-val -> Unspecified
(define (setref! ref val)
  (letrec
    ((setref-inner
      (lambda (store1 ref1)
        (cond ((null? store1)
               (report-invalid-reference ref the-store))
              ((zero? ref1) (cons val (cdr store1)))
              (else (cons (car store1)
                          (setref-inner (cdr store1)
                                        (- ref1 1))))))))
    (set! the-store (setref-inner the-store ref))))

(define (report-invalid-reference ref store)
  (error 'report-invalid-reference
         "invalid reference"
         ref
         store))

;;;; Expressed values

;; expval->num : Exp-val -> Int
(define (expval->num val)
  (pmatch val
    ((num-val ,n) n)
    (? (report-expval-extractor-error 'num val))))

;; expval->bool : Exp-val -> Bool
(define (expval->bool val)
  (pmatch val
    ((bool-val ,b) b)
    (? (report-expval-extractor-error 'bool val))))

;; expval->func : Exp-val -> Func
(define (expval->proc val)
  (pmatch val
    ((func-val ,f) f)
    (? (report-expval-extractor-error 'func val))))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

(define the-unspecified-value '(num-val 27))

;;;; Functions

;; function : Var x Exp x Env -> Func
(define (function var body env)
  (list 'func var body env))

;; apply-function/k : Func x Exp-val x Cont -> Final-answer
;; TODO

;;;; Environments

;; empty-env : () -> Env
(define (empty-env) '())

;; extend-env : Var x Exp-val x Env -> Env
(define (extend-env var val env)
  (cons (list 'ext var val) env))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (pmatch env
    (() (report-no-binding-found search-var))
    (((ext ,var ,val) . ,env*)
     (if (eqv? search-var var) val (apply-env env* search-var)))
    (? (error 'apply-env "invalid environment" env))))

(define (report-no-binding-found var)
  (error 'apply-env "no binding found" var))

;; alist->env : List-of(Var x Scheme-val) -> Env
;; No recursive bindings.
(define (alist->env as)
  (fold-right (lambda (p env)
                (extend-env (car p) (newref (cdr p)) env))
              (empty-env)
              as))

;;; Initial environment

;; init-env : () -> Env
(define (init-env)
  (alist->env `((i . (num-val 1))
                (v . (num-val 5))
                (x . (num-val 10)))))

;;;; Continuations

;;; A command continuation (Com-cont) accepts zero values.  All
;;; statements are executed in command continuations.

;; exec-com-cont : Com-cont -> ???
(define (exec-com-cont cont) (cont))

;;; A value continuation (Val-cont) accepts a single value.  All
;;; expressions are evaluated in value continuations.

;; assign-exp1-cont : Var x Env x Com-cont -> Val-cont
(define (assign-exp1-cont var env cont)
  (lambda (val)
    (setref! (apply-env env var) val)
    (exec-com-cont cont)))

;; print-exp1-cont : Com-cont -> Val-cont
(define (print-exp1-cont cont)
  (lambda (val)
    (display "    ")
    (display val)  ; improve output
    (newline)
    (exec-com-cont cont)))

;;;; Programs

(define (program exp1)
  (list 'program exp1))

;;;; Evaluator for expressions

;; value-of/k : Exp x Env x Val-cont -> ???
(define (value-of/k exp env cont)
  (pmatch exp
    ((const-exp ,num) (apply-val-cont cont `(num-val num)))
    ((var-exp ,var) (apply-val-cont (deref (apply-env env var))))
    ((not-exp ,exp1) (value-of/k exp1 env (not-exp1-cont cont)))
    ;; ...
    (? (error 'value-of/k "invalid expression" exp))))

;;;; Interpreter for statements

;; result-of/k : Stmt x Env x Com-cont -> ???
(define (result-of/k stmt env cont)
  (pmatch stmt
    ((assign-stmt ,var ,exp1)
     (value-of/k exp1
                 env
                 (assign-exp1-cont var env cont)))
    ((print-stmt ,exp1)
     (value-of/k exp1 env (print-exp1-cont cont)))
    ((if-stmt ,test ,con ,alt)
     (value-of/k test env (if-test-cont con alt env cont)))
    ((while-stmt ,test ,body)
     (value-of/k test env (while-test-cont test body env cont)))
    ;; ...
    (? (error 'result-of/k "invalid statement" stmt))))
