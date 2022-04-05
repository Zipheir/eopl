;;;; EXPLICIT-REFS language from Ch. 4.

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

(define-record-type proc-exp
  (fields var body))

(define-record-type call-exp
  (fields rator rand))

(define-record-type letrec-exp
  (fields p-name b-var p-body letrec-body))

(define-record-type newref-exp
  (fields exp1))

(define-record-type deref-exp
  (fields exp1))

(define-record-type setref-exp
  (fields exp1 exp2))

(define-record-type begin-exp
  (fields exps))

;;;; Expressed values

(define-record-type ref-val
  (fields loc))

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

;; expval->loc : Exp-val -> Ref
(define (expval->ref val)
  (if (ref-val? val)
      (ref-val-loc val)
      (report-expval-extractor-error 'ref val)))

;; expval->proc : Exp-val → Proc
(define (expval->proc val)
  (if (proc-val? val)
      (proc-val-proc val)
      (report-expval-extractor-error 'proc val)))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;;;; Procedures

(define-record-type proc
  (fields var body saved-env))

(define procedure make-proc)

;; apply-procedure : Proc x Exp-val -> Exp-val
(define (apply-procedure proc1 val)
  (value-of (proc-body proc1)
            (extend-env (proc-var proc1) val (proc-saved-env proc1))))

;;;; Environments

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
             (make-proc-val (procedure (extended-env-rec-b-var env)
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
         (value-of (letrec-exp-letrec-body exp)
                   (extend-env-rec (letrec-exp-p-name exp)
                                   (letrec-exp-b-var exp)
                                   (letrec-exp-p-body exp)
                                   env)))
        ((newref-exp? exp)
         (let ((v1 (value-of (newref-exp-exp1 exp) env)))
           (make-ref-val (newref v1))))
        ((deref-exp? exp)
         (let ((ref1 (expval->ref (value-of (deref-exp-exp1 exp) env))))
           (deref ref1)))
        ((setref-exp? exp)
         ;; Using let* ensures the proper evaluation order.
         (let* ((ref (expval->ref (value-of (setref-exp-exp1 exp) env)))
                (val2 (value-of (setref-exp-exp2 exp) env)))
           (begin
            (setref! ref val2)
            (make-num-val 23))))  ; arbitrary value
        ((begin-exp? exp) (eval-sequence (begin-exp-exps exp) env))
        (else (error 'value-of "invalid expression" exp))))

;; eval-sequence : List-of(Exp) x Env -> Exp-val
(define (eval-sequence exps env)
  (pmatch exps
    (() (make-num-val 23))  ; arbitrary
    ((,e) (value-of e env))
    ((,e . ,es)
     (value-of e env)       ; implicit begin!
     (eval-sequence es env))))

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
    ((proc (,v) ,body) (guard (symbol? v))
     (make-proc-exp v (parse body)))
    ((letrec ,name (,v) = ,p-body in ,body)
     (guard (symbol? name) (symbol? v))
     (make-letrec-exp name v (parse p-body) (parse body)))
    ((newref ,e) (make-newref-exp (parse e)))
    ((deref ,e) (make-deref-exp (parse e)))
    ((setref ,re ,ve) (make-setref-exp (parse re) (parse ve)))
    ((begin . ,es) (make-begin-exp (map parse es)))
    ((,e1 ,e2) (make-call-exp (parse e1) (parse e2)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-program : List -> Program
(define (parse-program sexp)
  (make-program (parse sexp)))

;; Unparser for the syntax above.
;; unparse : Exp -> List
(define (unparse exp)
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
        ((proc-exp? exp)
         `(proc ,(list (proc-exp-var exp))
                ,(unparse (proc-exp-body exp))))
        ((letrec-exp? exp)
         `(letrec ,(letrec-exp-p-name exp)
                  ,(list (letrec-exp-b-var exp)) =
                    ,(unparse (letrec-exp-p-body exp))
           in ,(unparse (letrec-exp-letrec-body exp))))
        ((newref-exp? exp) `(newref ,(unparse (newref-exp-exp1 exp))))
        ((deref-exp? exp) `(deref ,(unparse (deref-exp-exp1 exp))))
        ((setref-exp? exp)
         `(setref ,(unparse (setref-exp-exp1 exp))
                  ,(unparse (setref-exp-exp2 exp))))
        ((begin-exp? exp)
         (cons 'begin (map unparse (begin-exp-exps exp))))
        ((call-exp? exp)
         (list (unparse (call-exp-rator exp))
               (unparse (call-exp-rand exp))))
        (else (error 'unparse "unknown expression type" exp))))

;; unparse-program : Program -> List
(define (unparse-program pgm)
  (assert (program? pgm))
  (unparse (program-exp1 pgm)))

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
              (letrec f (a) = (if (zero? a) 0 (add1 (f (- a 1)))) in
                (f 5)))))

  (test 1 (eval-to-num '(let pn = (newref 1) in (deref pn))))
  (test 1 (eval-to-num 
           '(let pn = (newref (newref 1)) in (deref (deref pn)))))
  (test 3 (eval-to-num
           '(let pn = (newref 0) in
              (let dummy = (setref pn 3) in
                (deref pn)))))
  (test 4 (eval-to-num
           '(let pn = (newref 3) in
              (let dummy = (setref pn (- (deref pn) (- 0 1))) in
                (deref pn)))))

  ;; begin (ex. 4.4)
  (test 3 (eval-to-num '(begin 1 2 3)))
  (test 3 (eval-to-num
           '(let a = (newref 0) in (begin (setref a 3) (deref a)))))
  (test 5 (eval-to-num '(begin (let v = 7 in (begin)) v)))
  (test 4 (eval-to-num
           '(let g = (let c = (newref 0)
                      in (proc (dum)
                           (begin
                            (setref c (- (deref c) (- 0 1)))
                            (deref c))))
             in (begin (g 0) (g 0) (g 0) (g 0)))))
  )
