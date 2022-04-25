;;;; CPS LETREC interpreter from Ch. 5.

(import (rnrs base (6))
        (rnrs lists (6)))

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

;; expval->proc : Exp-val -> Proc
(define (expval->proc val)
  (pmatch val
    ((proc-val ,p) p)
    (? (report-expval-extractor-error 'proc val))))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

(define the-unspecified-value '(num-val 27))

;;;; Procedures

(define (procedure b-var body saved-env)
  (list 'proc b-var body saved-env))

;; apply-procedure/k : Proc x Ref x Cont -> Final-answer
(define (apply-procedure/k proc1 val cont)
  (pmatch proc1
    ((proc ,var ,body ,env)
     (value-of/k body (extend-env var (newref val) env) cont))))

;;;; Environments

;; empty-env : () -> Env
(define (empty-env) '())

;; extend-env : Var x Exp-val x Env -> Env
(define (extend-env var val env)
  (cons (list 'ext var val) env))

;; extend-env-rec : Var x Var x Exp-val x Env -> Env
(define (extend-env-rec p-name b-var p-body env)
  (cons (list 'ext-rec p-name b-var p-body) env))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (pmatch env
    (() (report-no-binding-found search-var))
    (((ext ,var ,val) . ,env*)
     (if (eqv? search-var var) val (apply-env env* search-var)))
    (((ext-rec ,p-name ,b-var ,p-body) . ,env*)
     (if (eqv? search-var p-name)
         (newref (list 'proc-val (procedure b-var p-body env)))
         (apply-env env* search-var)))
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

;; apply-cont : Cont x Val -> Final-answer
(define (apply-cont cont val)
  (pmatch cont
    ((end-cont ,print-msg)
     (when print-msg (display "End of computation.\n"))
     val)
    ((zero1-cont ,k)
     (apply-cont k `(bool-val ,(zero? (expval->num val)))))
    ((if-test-cont ,exp2 ,exp3 ,env ,k)
     (if (expval->bool val)
         (value-of/k exp2 env k)
         (value-of/k exp3 env k)))
    ((let-exp-cont ,var ,body ,env ,k)
     (value-of/k body (extend-env var (newref val) env) k))
    ((diff1-cont ,exp2 ,env ,k)
     (value-of/k exp2 env `(diff2-cont ,val ,env ,k)))
    ((diff2-cont ,val1 ,env ,k)
     (let ((num1 (expval->num val1))
           (num2 (expval->num val)))
       (apply-cont k `(num-val ,(- num1 num2)))))
    ((rator-cont ,rand ,env ,k)
     (value-of/k rand env `(rand-cont ,val ,env ,k)))
    ((rand-cont ,vrat ,env ,k)
     (apply-procedure/k (expval->proc vrat) val k))
    ((assign-rhs-cont ,ref ,k)
     (apply-cont k (begin (setref! ref val)
                          the-unspecified-value)))
    (? (error 'apply-cont "invalid continuation" cont))))

;;;; Interpreter

;; value-of-program : Program x Bool -> Final-answer
(define (value-of-program pgm print-msg)
  (pmatch pgm
    ((program ,exp1)
     (initialize-store!)
     (value-of/k exp1 (init-env) `(end-cont ,print-msg)))))

;; value-of/k : Exp x Env x Cont -> Final-answer
(define (value-of/k exp env cont)
  (pmatch exp
    ((const-exp ,n) (apply-cont cont `(num-val ,n)))
    ((var-exp ,var) (apply-cont cont (deref (apply-env env var))))
    ((proc-exp ,var ,body)
     (apply-cont cont `(proc-val ,(procedure var body env))))
    ((zero?-exp ,exp1) (value-of/k exp1 env `(zero1-cont ,cont)))
    ((diff-exp ,exp1 ,exp2)
     (value-of/k exp1 env `(diff1-cont ,exp2 ,env ,cont)))
    ((if-exp ,exp1 ,exp2 ,exp3)
     (value-of/k exp1 env `(if-test-cont ,exp2 ,exp3 ,env ,cont)))
    ((let-exp ,var ,exp1 ,body)
     (value-of/k exp1 env `(let-exp-cont ,var ,body ,env ,cont)))
    ((letrec-exp ,p-name ,b-var ,p-body ,lr-body)
     (value-of/k lr-body
                 (extend-env-rec p-name b-var p-body env)
                 cont))
    ((call-exp ,rator ,rand)
     (value-of/k rator env `(rator-cont ,rand ,env ,cont)))
    ((assign-exp ,var ,exp1)
     (value-of/k exp1
                 env
                 `(assign-rhs-cont ,(apply-env env var) ,cont)))
    (? (error 'value-of/k "invalid expression" exp))))

;; Parser for a simple S-exp representation.
;; parse : List -> Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) `(const-exp ,n))
    ((- ,s ,t) `(diff-exp ,(parse s) ,(parse t)))
    ((zero? ,s) `(zero?-exp ,(parse s)))
    ((if ,t ,c ,a) `(if-exp ,(parse t) ,(parse c) ,(parse a)))
    (,v (guard (symbol? v)) `(var-exp ,v))
    ((let ,v = ,s in ,b) (guard (symbol? v))
     `(let-exp ,v ,(parse s) ,(parse b)))
    ((proc (,v) ,body) (guard (symbol? v))
     `(proc-exp ,v ,(parse body)))
    ((letrec ,f (,v) = ,e in ,body)
     (guard (symbol? f) (symbol? v))
     `(letrec-exp ,f ,v ,(parse e) ,(parse body)))
    ((set ,v ,e) (guard (symbol? v))
     `(assign-exp ,v ,(parse e)))
    ((,e1 ,e2) `(call-exp ,(parse e1) ,(parse e2)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-program : List -> Program
(define (parse-program sexp)
  (list 'program (parse sexp)))

;; run : List x Bool -> Final-answer
(define (run sexp print-msg)
  (value-of-program (parse-program sexp) print-msg))

;;;; Tests

(define (run-tests)
  (define (eval-to-num exp)
    (expval->num (run exp #f)))

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
              (letrec f (a) = (if (zero? a) 0 (add1 (f (- a 1))))
               in (f 5)))))

  ;;; Assignment

  (test 5 (eval-to-num
           '(let x = 0
             in (let dum = (set x 5)
                 in x))))
  (test 8 (eval-to-num
           '(let acc = 0
             in (let add2 = (proc (a) (- a (- 0 2)))
                 in (letrec double (x) =
                              (if (zero? x)
                                  acc
                                  (let dum = (set acc (add2 acc))
                                    in (double (- x 1))))
                     in (double 4))))))
  )
