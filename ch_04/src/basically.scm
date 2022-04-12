;;;; BASICALLY language from Ex. 4.22

(import (rnrs lists (6))
        (rnrs records syntactic (6)))

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

;;;; Expressed values

(define-record-type num-val
  (fields num))

(define-record-type bool-val
  (fields bool))

(define-record-type func-val
  (fields func))

;; expval->num : Exp-val -> Int
(define (expval->num val)
  (if (num-val? val)
      (num-val-num val)
      (report-expval-extractor-error 'num val)))

;; expval->bool : Exp-val -> Bool
(define (expval->bool val)
  (if (bool-val? val)
      (bool-val-bool val)
      (report-expval-extractor-error 'bool val)))

;; expval->func : Exp-val -> Proc
(define (expval->func val)
  (if (func-val? val)
      (func-val-func val)
      (report-expval-extractor-error 'func val)))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;; the-unspecified-value : Exp-val
(define the-unspecified-value (make-num-val 27))

;; print-exp-val : Exp-val -> ()
(define (print-exp-val val)
  (let ((show
         (lambda (x)
           (display x)
           (newline))))
    (cond ((num-val? val) (show (num-val-num val)))
          ((bool-val? val) (show (bool-val-bool val)))
          (else (error 'print-exp-val "unknown value type" val)))))

;;;; Functions

(define-record-type func
  (fields var body saved-env))

;; apply-function : Func x Exp-val -> Exp-val
(define (apply-function func1 val)
  (value-of (func-body func1)
            (extend-env (func-var func1)
                        (newref val)
                        (func-saved-env func1))))

;;;; Environments

(define (empty-env) '())

(define (extend-env var val rest-env)
  (list 'extend-env var val rest-env))

;; extend-env-all : List-of(Var) x List-of(Val) x Env -> Env
(define (extend-env-all vars vals env)
  (fold-right extend-env env vars vals))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (pmatch env
    (() (report-no-binding-found search-var))
    ((extend-env ,var ,val ,rest-env)
     (if (eqv? search-var var)
         val
         (apply-env rest-env search-var)))
    (? (error 'apply-env "invalid environment" env))))

;; location : Var x List-of(Var) -> Nat + False
(define (location var vs)
  (letrec
    ((index-of
      (lambda (vs k)
        (pmatch vs
          (() #f)
          ((,v . ,vs*)
           (if (eqv? v var)
               k
               (index-of vs* (+ k 1))))))))

    (index-of vs 0)))

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
  (alist->env `((i . ,(make-num-val 1))
                (v . ,(make-num-val 5))
                (x . ,(make-num-val 10)))))

;;;; Programs

(define-record-type program
  (fields exp1))

;;;; Evaluator for expressions

;; value-of : Exp x Env -> Exp-val
(define (value-of exp env)
  (pmatch exp
    ((const-exp ,num) (make-num-val num))
    ((var-exp ,var) (deref (apply-env env var)))
    ((not-exp ,exp1)
     (let ((val (value-of exp1 env)))
       (make-bool-val (not (expval->bool val)))))
    ((diff-exp ,exp1 ,exp2)
     (let ((num1 (expval->num (value-of exp1 env)))
           (num2 (expval->num (value-of exp2 env))))
       (make-num-val (- num1 num2))))
    ((zero?-exp ,exp1)
     (let ((val (value-of exp1 env)))
       (if (zero? (expval->num val))
           (make-bool-val #t)
           (make-bool-val #f))))
    ((func-exp ,var ,body)
     (make-func-val (make-func var body env)))
    ((call-exp ,rator ,rand)
     (let ((func1 (expval->func (value-of rator env)))
           (rval (value-of rand env)))
       (apply-function func1 rval)))
    (? (error 'value-of "invalid expression" exp))))

;;;; Interpreter for statements

;; result-of : Stmt x Env -> ()
(define (result-of stmt env)
  (pmatch stmt
    ((assign-stmt ,var ,exp1)
     (setref! (apply-env env var) (value-of exp1 env)))
    ((print-stmt ,exp1)
     (print-exp-val (value-of exp1 env)))
    ((if-stmt ,test ,con ,alt)
     (let ((val (value-of test env)))
       (if (expval->bool val)
           (result-of con env)
           (result-of alt env))))
    ((while-stmt ,test ,body)
     (let loop ()
       (when (expval->bool (value-of test env))
         (begin (result-of body env) (loop)))))
    ((block-stmt ,vars ,body)
     (let ((refs (map (lambda (_) (newref 'uninitialized)) vars)))
       (result-of body (extend-env-all vars refs env))))
    ((begin-stmt ,stmts)
     (for-each (lambda (st) (result-of st env)) stmts))
    ((read-stmt ,var)
     (let ((x (read)))
       (if (integer? x)
           (setref! (apply-env env var) (make-num-val x))
           (error 'result-of "invalid input value" x))))
    ((do-while-exp ,body ,test)
     (let loop ()
       (result-of body env)
       (when (expval->bool (value-of test env))
         (loop))))
    (? (error 'result-of "invalid statement" stmt))))

;; result-of-program : Prog -> ()
(define (result-of-program pgm)
  (initialize-store!)
  (result-of (program-exp1 pgm) (init-env)))

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
    ((var ,vs : ,body) (guard (for-all symbol? vs))
     `(block-stmt ,vs ,(parse body)))
    ((begin . ,sts) `(begin-stmt ,(map parse sts)))
    ((read ,v) (guard (symbol? v)) `(read-stmt ,v))
    ((do ,body while ,test)
     `(do-while-exp ,(parse body) ,(exp-parse test)))
    (? (error 'parse "invalid statement syntax" sexp))))

;; parse-program : List -> Program
(define (parse-program sexp)
  (make-program (parse sexp)))

;;;; Convenience driver

;; run : Bool x List -> Exp-val
(define (run sexp)
  (result-of-program (parse-program sexp)))
