;;;; IMPLICIT-REFS language from Ch. 4, extended with immutable and
;;;; mutable bindings per Ex. 4.20.

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

;;;; Expressions

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

(define-record-type letmut-exp
  (fields var exp1 body))

(define-record-type proc-exp
  (fields var body))

(define-record-type call-exp
  (fields rator rand))

(define-record-type letrec-exp
  (fields p-names b-vars p-bodies letrec-body))

(define-record-type assign-exp
  (fields var exp1))

;;;; Expressed values

(define-record-type num-val
  (fields num))

(define-record-type bool-val
  (fields bool))

(define-record-type proc-val
  (fields proc))

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

;; expval->proc : Exp-val -> Proc
(define (expval->proc val)
  (if (proc-val? val)
      (proc-val-proc val)
      (report-expval-extractor-error 'proc val)))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;; the-unspecified-value : Exp-val
(define the-unspecified-value (make-num-val 27))

;;;; Procedures

(define-record-type proc
  (fields var body saved-env))

(define procedure make-proc)

;; apply-procedure : Proc x Exp-val -> Exp-val
(define (apply-procedure proc1 val)
  (value-of (proc-body proc1)
            (extend-env (proc-var proc1)
                        (newref val)
                        (proc-saved-env proc1))))

;;;; Environments

(define-record-type (empty-environment empty-env empty-env?))

(define-record-type (extended-env extend-env extended-env?)
  (fields var val rest-env))

(define-record-type (extended-env-rec extend-env-rec extended-env-rec?)
  (fields p-names b-vars p-bodies env))

(define (environment? obj)
  (or (empty-env? obj)
      (extended-env? obj)
      (extended-env-rec? obj)))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (cond ((empty-env? env) (report-no-binding-found search-var))
        ((extended-env? env)
         (if (eqv? search-var (extended-env-var env))
             (extended-env-val env)
             (apply-env (extended-env-rest-env env) search-var)))
        ((extended-env-rec? env)
         (let ((b-vars (extended-env-rec-b-vars env))
               (p-bodies (extended-env-rec-p-bodies env)))
           (cond ((location search-var
                            (extended-env-rec-p-names env)) =>
                  (lambda (n)
                    (make-proc-val (procedure (list-ref b-vars n)
                                              (list-ref p-bodies n)
                                              env))))
                 (else
                  (apply-env (extended-env-rec-env env) search-var)))))
        (else (error 'apply-env "invalid environment" env))))

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

;;;; Main interpreter

;; value-of-program : Program -> Exp-val
(define (value-of-program pgm)
  (initialize-store!)
  (value-of (program-exp1 pgm) (init-env)))

;; value-of : Exp x Env -> Exp-val
(define (value-of exp env)
  (cond ((const-exp? exp) (make-num-val (const-exp-num exp)))
        ((var-exp? exp)
         (let ((v (apply-env env (var-exp-var exp))))
           (if (reference? v) (deref v) v)))
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
        ((letmut-exp? exp)
         (let ((val (value-of (letmut-exp-exp1 exp) env)))
           (value-of (letmut-exp-body exp)
                     (extend-env (letmut-exp-var exp)
                                 (newref val)
                                 env))))
        ((proc-exp? exp)
         (make-proc-val (procedure (proc-exp-var exp)
                                   (proc-exp-body exp)
                                   env)))
        ((call-exp? exp)
         (let ((proc (expval->proc (value-of (call-exp-rator exp) env)))
               (arg (value-of (call-exp-rand exp) env)))
           (apply-procedure proc arg)))
        ((letrec-exp? exp)
         (value-of (letrec-exp-letrec-body exp)
                   (extend-env-rec (letrec-exp-p-names exp)
                                   (letrec-exp-b-vars exp)
                                   (letrec-exp-p-bodies exp)
                                   env)))
        ((assign-exp? exp)
         (let* ((var (assign-exp-var exp))
                (l (apply-env env var)))
           (if (reference? l)
               (setref! l (value-of (assign-exp-exp1 exp) env))
               (report-assignment-to-immutable-var var))
           the-unspecified-value))
        (else (error 'value-of "invalid expression" exp))))

;; report-assignment-to-immutable-var : Var -> ()
(define (report-assignment-to-immutable-var var)
  (error 'value-of
         "assignment to immutable variable"
         var))

;; Parser for a simple S-exp representation.
;; parse : List -> Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) (make-const-exp n))
    ((- ,s ,t) (make-diff-exp (parse s) (parse t)))
    ((zero? ,s) (make-zero?-exp (parse s)))
    ((if ,t ,c ,a) (make-if-exp (parse t) (parse c) (parse a)))
    (,v (guard (symbol? v)) (make-var-exp v))
    ((let ,v = ,s in ,b) (guard (symbol? v))
     (make-let-exp v (parse s) (parse b)))
    ((letmutable ,v = ,s in ,b) (guard (symbol? v))
     (make-letmut-exp v (parse s) (parse b)))
    ((proc (,v) ,body) (guard (symbol? v))
     (make-proc-exp v (parse body)))
    ((letrec ,bs in ,body) (parse-letrec bs body))
    ((set ,v ,ve) (guard (symbol? v))
     (make-assign-exp v (parse ve)))
    ((,e1 ,e2) (make-call-exp (parse e1) (parse e2)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-letrec : List x List -> Exp
(define (parse-letrec binds body)
  (letrec
    ((collect
      (lambda (bs names vars bodies)
        (pmatch bs
          (() (values names vars bodies))
          (((,name (,var) = ,body) . ,bs*)
           (guard (symbol? name) (symbol? var))
           (collect bs*
                    (cons name names)
                    (cons var vars)
                    (cons (parse body) bodies)))))))

    (let-values (((names vars bodies) (collect binds '() '() '())))
      (make-letrec-exp names vars bodies (parse body)))))

;; parse-program : List -> Program
(define (parse-program sexp)
  (make-program (parse sexp)))

;;;; Convenience drivers

;; run : Bool x List -> Exp-val
(define (run sexp)
  (value-of-program (parse-program sexp)))

;;;; Tests

(define (eval-to-num sexp)
  (expval->num (run sexp)))

(define (run-tests)
  (test 5 (eval-to-num '5))
  (test 5 (eval-to-num 'v))
  (test 0 (eval-to-num '(if (zero? 2) 1 0)))
  (test 1 (eval-to-num '(if (zero? 0) 1 0)))
  (test 1 (eval-to-num '(- 3 2)))
  (test 4 (eval-to-num '(let a = (- v i) in a)))
  (test 6 (eval-to-num
           '(let add1 = (proc (a) (- a (- 0 1))) in (add1 v))))
  (test 5 (eval-to-num
           '(let add1 = (proc (b) (- b (- 0 1))) in
              (letrec ((f (a) = (if (zero? a) 0 (add1 (f (- a 1))))))
               in (f 5)))))
  (test 0 (eval-to-num
           '(letrec ((even (k) = (if (zero? k) 1 (odd (- k 1))))
                     (odd  (k) = (if (zero? k) 0 (even (- k 1)))))
             in (- (even 4) (odd 3)))))

  (test 5 (eval-to-num '(letmutable y = 0 in
                          (let dum = (set y 5) in y))))
  (test 0 (eval-to-num
           '(letmutable x = 0 in
              (letrec ((even (dum) = (if (zero? x)
                                         1
                                         (let dum = (set x (- x 1)) in
                                           (odd 4))))
                       (odd (dum) = (if (zero? x)
                                        0
                                        (let dum = (set x (- x 1)) in
                                          (even 4)))))
               in (let dum = (set x 5) in
                    (even 888))))))
  )
