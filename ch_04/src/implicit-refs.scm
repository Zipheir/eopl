;;;; IMPLICIT-REFS language from Ch. 4, with multi-parameter
;;;; extensions from Ex. 4.17, etc.

(import (rnrs lists (6))
        (rnrs records syntactic (6)))

(include "pmatch.scm")
(include "../../src/test.scm")

;; zip : List x List -> List
(define (zip xs ys)
  (cond ((null? xs) '())
        ((null? ys) '())
        (else
         (cons (cons (car xs) (car ys))
               (zip (cdr xs) (cdr ys))))))

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
  (fields vars exps body))

(define-record-type proc-exp
  (fields vars body))

(define-record-type call-exp
  (fields rator rands))

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
  (fields vars body saved-env))

(define procedure make-proc)

;; apply-procedure : Proc x List-of(Exp-val) -> Exp-val
(define (apply-procedure proc1 vals)
  (value-of (proc-body proc1)
            (extend-env (zip (proc-vars proc1) (map newref vals))
                        (proc-saved-env proc1))))

;;;; Environments

(define-record-type (empty-environment empty-env empty-env?))

(define-record-type (extended-env extend-env extended-env?)
  (fields binds rest-env))

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
         (cond ((assv search-var (extended-env-binds env)) => cdr)
               (else (apply-env (extended-env-rest-env env)
                                search-var))))
        ((extended-env-rec? env)
         (let ((b-vars (extended-env-rec-b-vars env))
               (p-bodies (extended-env-rec-p-bodies env)))
           (cond ((location search-var
                            (extended-env-rec-p-names env)) =>
                  (lambda (n)
                    (newref
                      (make-proc-val (procedure b-vars
                                                (list-ref p-bodies n)
                                                env)))))
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
  (extend-env as (empty-env)))

;;; Initial environment

;; init-env : () -> Env
;; This is side-effecting, due to the newrefs.
(define (init-env)
  (alist->env `((i . ,(newref (make-num-val 1)))
                (v . ,(newref (make-num-val 5)))
                (x . ,(newref (make-num-val 10))))))

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
        ((var-exp? exp) (deref (apply-env env (var-exp-var exp))))
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
         (let ((vals (eval-in-order (let-exp-exps exp) env)))
           (value-of (let-exp-body exp)
                     (extend-env (zip (let-exp-vars exp)
                                      (map newref vals))
                                 env))))
        ((proc-exp? exp)
         (make-proc-val (procedure (proc-exp-vars exp)
                                   (proc-exp-body exp)
                                   env)))
        ((call-exp? exp)
         (let ((proc (expval->proc (value-of (call-exp-rator exp) env)))
               (args (eval-in-order (call-exp-rands exp) env)))
           (apply-procedure proc args)))
        ((letrec-exp? exp)
         (value-of (letrec-exp-letrec-body exp)
                   (extend-env-rec (letrec-exp-p-names exp)
                                   (letrec-exp-b-vars exp)
                                   (letrec-exp-p-bodies exp)
                                   env)))
        ((assign-exp? exp)
         (setref! (apply-env env (assign-exp-var exp))
                  (value-of (assign-exp-exp1 exp) env))
         the-unspecified-value)
        (else (error 'value-of "invalid expression" exp))))

;; eval-in-order : List-of(Exp) x Env -> List-of(Exp-val)
;; This is very much like map, but with a specified order of
;; evaluation.
(define (eval-in-order exps env)
  (letrec
    ((eval-all
      (lambda (es)
        (pmatch es
          (() '())
          ((,e . ,es*) `(,(value-of e env) . ,(eval-all es*)))))))

    (eval-all exps)))

;; Parser for a simple S-exp representation.
;; parse : List -> Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) (make-const-exp n))
    ((- ,s ,t) (make-diff-exp (parse s) (parse t)))
    ((zero? ,s) (make-zero?-exp (parse s)))
    ((if ,t ,c ,a) (make-if-exp (parse t) (parse c) (parse a)))
    (,v (guard (symbol? v)) (make-var-exp v))
    ((let ,bs in ,body)
     (let-values (((vars exps) (parse-bindings bs)))
       (make-let-exp vars exps (parse body))))
    ((proc ,vs ,body) (guard (for-all symbol? vs))
     (make-proc-exp vs (parse body)))
    ((letrec ,bs in ,body) (parse-letrec bs body))
    ((set ,v ,ve) (guard (symbol? v))
     (make-assign-exp v (parse ve)))
    ((,e . ,ers) (make-call-exp (parse e) (map parse ers)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-bindings : List -> List-of(Var) x List-of(Exp)
(define (parse-bindings bs)
  (pmatch bs
    (() (values '() '()))
    (((,var = ,exp) . ,bs*) (guard (symbol? var))
     (let-values (((vars exps) (parse-bindings bs*)))
       (values (cons var vars) (cons (parse exp) exps))))))

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
  (test 4 (eval-to-num '(let ((a = (- v i))) in a)))
  (test 6 (eval-to-num
           '(let ((add1 = (proc (a) (- a (- 0 1))))) in (add1 v))))
  (test 5 (eval-to-num
           '(let ((add1 = (proc (b) (- b (- 0 1))))) in
              (letrec ((f (a) = (if (zero? a) 0 (add1 (f (- a 1))))))
               in (f 5)))))
  (test 0 (eval-to-num
           '(letrec ((even (k) = (if (zero? k) 1 (odd (- k 1))))
                     (odd  (k) = (if (zero? k) 0 (even (- k 1)))))
             in (- (even 4) (odd 3)))))

  (test 5 (eval-to-num '(let ((y = 0)) in
                          (let ((dum = (set y 5))) in y))))
  (test 0 (eval-to-num
           '(let ((x = 0)) in
              (letrec ((even (dum) = (if (zero? x)
                                         1
                                         (let ((dum = (set x (- x 1))))
                                          in (odd 4))))
                       (odd (dum) = (if (zero? x)
                                        0
                                        (let ((dum = (set x (- x 1))))
                                         in (even 4)))))
               in (let ((dum = (set x 5))) in
                    (even 888))))))
  )
