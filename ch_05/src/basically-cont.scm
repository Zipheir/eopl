;;;; CPS interpreter (Ex. 5.16) for the BASICALLY language of Ch. 4.

(import (rnrs base (6)))

(include "../../src/pmatch.scm")
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

;; apply-function/k : Func x Exp-val x Val-cont -> ()
(define (apply-function/k func val cont)
  (pmatch func
    ((func ,var ,body ,env)
     (value-of/k body (extend-env var (newref val) env) cont))))

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

;; exec-com-cont : Com-cont -> ()
(define (exec-com-cont cont) (cont))

;; end-cont : () -> Com-cont
(define (end-cont)
  (lambda ()
    (display "End of computation.\n")))

;; while-next-cont : Exp x Stmt x Env x Com-cont -> Com-cont
(define (while-next-cont test body env cont)
  (lambda ()
    (value-of/k test env (while-test-cont test body env cont))))

;; seq-rest-cont : List-of(Stmt) x Env x Com-cont -> Com-cont
(define (seq-rest-cont stmts env cont)
  (lambda ()
    (pmatch stmts
      (() (exec-com-cont cont))
      ((,s . ,ss)
       (result-of/k s env (seq-rest-cont ss env cont))))))

;;; A value continuation (Val-cont) accepts a single value.  All
;;; expressions are evaluated in value continuations.

;; apply-val-cont : Val-cont x Exp-val -> ()
(define (apply-val-cont cont val) (cont val))

;; not-exp1-cont : Val-cont -> Val-cont
(define (not-exp1-cont cont)
  (lambda (val)
    (apply-val-cont cont `(bool-val ,(not (expval->bool val))))))

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

;; if-test-cont : Stmt x Stmt x Env x Com-cont -> Val-cont
(define (if-test-cont con alt env cont)
  (lambda (val)
    (if (expval->bool val)
        (result-of/k con env cont)
        (result-of/k alt env cont))))

;; while-test-cont : Exp x Stmt x Env x Com-cont -> Val-cont
(define (while-test-cont test body env cont)
  (lambda (val)
    (if (expval->bool val)
        (result-of/k body env (while-next-cont test body env cont))
        (exec-com-cont cont))))

;; diff-exp1-cont : Exp x Env x Val-cont -> Val-cont
(define (diff-exp1-cont exp2 env cont)
  (lambda (val)
    (value-of/k exp2 env (diff-exp2-cont val cont))))

;; diff-exp2-cont : Exp-val x Val-cont -> Val-cont
(define (diff-exp2-cont val1 cont)
  (lambda (val2)
    (let ((num1 (expval->num val1)) (num2 (expval->num val2)))
      (apply-val-cont cont `(num-val ,(- num1 num2))))))

;; zero?-exp1-cont : Val-cont -> Val-cont
(define (zero?-exp1-cont cont)
  (lambda (val)
    (let ((num (expval->num val)))
      (apply-val-cont cont `(bool-val ,(zero? num))))))

;; rator-cont : Exp x Env x Val-cont -> Val-cont
(define (rator-cont rand env cont)
  (lambda (vrat)
    (value-of/k rand env (rand-cont vrat cont))))

;; rand-cont : Exp x Val-cont -> Val-cont
(define (rand-cont vrat cont)
  (lambda (vrand)
    (apply-function/k (expval->func vrat) vrand cont)))

;;;; Programs

(define (program exp1)
  (list 'program exp1))

;;;; Evaluator for expressions

;; value-of/k : Exp x Env x Val-cont -> ()
(define (value-of/k exp env cont)
  (pmatch exp
    ((const-exp ,num) (apply-val-cont cont `(num-val ,num)))
    ((var-exp ,var) (apply-val-cont cont (deref (apply-env env var))))
    ((not-exp ,exp1) (value-of/k exp1 env (not-exp1-cont cont)))
    ((diff-exp ,exp1 ,exp2)
     (value-of/k exp1 env (diff-exp1-cont exp2 env cont)))
    ((zero?-exp ,exp1)
     (value-of/k exp1 env (zero?-exp1-cont cont)))
    ((func-exp ,var ,body)
     (apply-val-cont cont (func-val (function var body env))))
    ((call-exp ,rator ,rand)
     (value-of/k rator env (rator-cont rand env cont)))
    (? (error 'value-of/k "invalid expression" exp))))

;;;; Interpreter for statements

;; result-of/k : Stmt x Env x Com-cont -> ()
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
    ((block-stmt ,var ,body)
     (result-of/k body
                  (extend-env var (newref 'uninitialized) env)
                  cont))
    ((begin-stmt ,stmts)
     (exec-com-cont (seq-rest-cont stmts env cont)))
    (? (error 'result-of/k "invalid statement" stmt))))

;; result-of-program : Prog -> ()
(define (result-of-program pgm)
  (pmatch pgm
    ((program ,stmt)
     (initialize-store!)
     (result-of/k stmt (init-env) (end-cont)))))

;;;; Basic S-exp syntax parsing

;; exp-parse : List -> Exp
;; Usage: Parse an expression.
(define (exp-parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) `(const-exp ,n))
    ((- ,s ,t) `(diff-exp ,(exp-parse s) ,(exp-parse t)))
    ((zero? ,s) `(zero?-exp ,(exp-parse s)))
    (,v (guard (symbol? v)) `(var-exp ,v))
    ((! ,e) `(not-exp ,(exp-parse e)))
    ((func (,v) ,body) (guard (symbol? v))
     `(func-exp ,v ,(exp-parse body)))
    ((,f ,a) `(call-exp ,(exp-parse f) ,(exp-parse a)))
    (? (error 'exp-parse "invalid expression syntax" sexp))))

;; parse : List -> Stmt
;; Usage: Parse a statement.
(define (parse sexp)
  (pmatch sexp
    ((,id := ,e) (guard (symbol? id))
     `(assign-stmt ,id ,(exp-parse e)))
    ((print ,e) `(print-stmt ,(exp-parse e)))
    ((if ,test ,con ,alt)
     `(if-stmt ,(exp-parse test) ,(parse con) ,(parse alt)))
    ((while ,test ,body)
     `(while-stmt ,(exp-parse test) ,(parse body)))
    ((var ,v : ,body) (guard (symbol? v))
     `(block-stmt ,v ,(parse body)))
    ((begin . ,sts) `(begin-stmt ,(map parse sts)))
    ((read ,v) (guard (symbol? v)) `(read-stmt ,v))
    ((do ,body while ,test)
     `(do-while-exp ,(parse body) ,(exp-parse test)))
    ((,s ,a) `(call-stmt ,(exp-parse s) ,(exp-parse a)))
    (? (error 'parse "invalid statement syntax" sexp))))

;; parse-program : List -> Program
(define (parse-program sexp)
  (program (parse sexp)))

;;;; Convenience driver

;; run : List -> ()
(define (run sexp)
  (result-of-program (parse-program sexp)))
