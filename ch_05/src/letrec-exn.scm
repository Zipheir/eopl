;;;; CPS LETREC interpreter from Ch. 5, with exception (S 5.4).

(import (rnrs base (6))
        (rnrs lists (6)))

(include "../../src/pmatch.scm")
(include "../../src/test.scm")

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

;;;; Procedures

(define (procedure b-var body saved-env)
  (list 'proc b-var body saved-env))

;; apply-procedure/k : Proc x Ref x Cont x Cont -> Final-answer
(define (apply-procedure/k proc1 val success failure)
  (pmatch proc1
    ((proc ,var ,body ,env)
     (value-of/k body (extend-env var val env) success failure))))

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
         (list 'proc-val (procedure b-var p-body env))
         (apply-env env* search-var)))
    (? (error 'apply-env "invalid environment" env))))

(define (report-no-binding-found var)
  (error 'apply-env "no binding found" var))

;; alist->env : List-of(Var x Scheme-val) -> Env
;; No recursive bindings.
(define (alist->env as)
  (fold-right (lambda (p env)
                (extend-env (car p) (cdr p) env))
              (empty-env)
              as))

;;; Initial environment

;; init-env : () -> Env
(define (init-env)
  (alist->env `((i . (num-val 1))
                (v . (num-val 5))
                (x . (num-val 10)))))

;;;; Exception handling

;; apply-handler : Exp-val x Cont -> Final-answer
(define (apply-handler val failure)
  (pmatch failure
    (() (report-uncaught-exception))
    (((try-cont ,var ,hexp ,senv ,scont) . ,fail-rest)
     (value-of/k hexp (extend-env var val senv) scont fail-rest))
    (? (error 'apply-handler
    	      "invalid failure continuation"
    	      cont))))

;; report-uncaught-exception : () -> [Bottom]
(define (report-uncaught-exception)
  (error 'report-uncaught-exception "uncaught exception"))

;;;; Continuations

;; apply-cont : Cont x Val x Cont -> Final-answer
(define (apply-cont cont val failure)
  (pmatch cont
    (() val)
    ((zero1-cont . ,k)
     (apply-cont k
                 `(bool-val ,(zero? (expval->num val)))
                 failure))
    (((if-test-cont ,exp2 ,exp3 ,env) . ,k)
     (if (expval->bool val)
         (value-of/k exp2 env k failure)
         (value-of/k exp3 env k failure)))
    (((let-exp-cont ,var ,body ,env) . ,k)
     (value-of/k body (extend-env var val env) k failure))
    (((diff1-cont ,exp2 ,env) . ,k)
     (value-of/k exp2 env `((diff2-cont ,val ,env) . ,k) failure))
    (((diff2-cont ,val1 ,env) . ,k)
     (let ((num1 (expval->num val1))
           (num2 (expval->num val)))
       (apply-cont k `(num-val ,(- num1 num2)) failure)))
    (((rator-cont ,rand ,env) . ,k)
     (value-of/k rand env `((rand-cont ,val ,env) . ,k) failure))
    (((rand-cont ,vrat ,env) . ,k)
     (apply-procedure/k (expval->proc vrat) val k failure))
    (((try-cont ? ? ? ?) . ,k)
     (error 'apply-cont "found try-cont (can't happen!)" cont))
    ((raise1-cont . ,k) (apply-handler val k))
    (? (error 'apply-cont "invalid continuation" cont))))

;;;; Interpreter

;; value-of-program : Program -> Final-answer
(define (value-of-program pgm)
  (pmatch pgm
    ((program ,exp1)
     (value-of/k exp1 (init-env) '() '()))))

;; value-of/k : Exp x Env x Cont x Cont -> Final-answer
(define (value-of/k exp env success failure)
  (pmatch exp
    ((const-exp ,n) (apply-cont success `(num-val ,n) failure))
    ((var-exp ,var) (apply-cont success (apply-env env var) failure))
    ((proc-exp ,var ,body)
     (apply-cont success
                 `(proc-val ,(procedure var body env))
                 failure))
    ((zero?-exp ,exp1)
     (value-of/k exp1 env `(zero1-cont . ,success) failure))
    ((diff-exp ,exp1 ,exp2)
     (value-of/k exp1
                 env
                 `((diff1-cont ,exp2 ,env) . ,success)
                 failure))
    ((if-exp ,exp1 ,exp2 ,exp3)
     (value-of/k exp1
                 env
                 `((if-test-cont ,exp2 ,exp3 ,env) . ,success)
                 failure))
    ((let-exp ,var ,exp1 ,body)
     (value-of/k exp1
                 env
                 `((let-exp-cont ,var ,body ,env) . ,success)
                 failure))
    ((letrec-exp ,p-name ,b-var ,p-body ,lr-body)
     (value-of/k lr-body
                 (extend-env-rec p-name b-var p-body env)
                 success
                 failure))
    ((call-exp ,rator ,rand)
     (value-of/k rator
                 env
                 `((rator-cont ,rand ,env) . ,success)
                 failure))
    ((try-exp ,exp1 ,var ,hexp)
     (value-of/k exp1
                 env
                 success
                 `((try-cont ,var ,hexp ,env ,success) . ,failure)))
    ((raise-exp ,exp1)
     (value-of/k exp1
                 env
                 `(raise1-cont . ,failure)
                 #f))  ; discarded
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
    ((try ,e catch (,v) ,h) (guard (symbol? v))
     `(try-exp ,(parse e) ,v ,(parse h)))
    ((raise ,e) `(raise-exp ,(parse e)))
    ((,e1 ,e2) `(call-exp ,(parse e1) ,(parse e2)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-program : List -> Program
(define (parse-program sexp)
  (list 'program (parse sexp)))

;; run : List -> Final-answer
(define (run sexp)
  (value-of-program (parse-program sexp)))

;;;; Tests

(define (run-tests)
  (define (eval-to-num exp)
    (expval->num (run exp)))

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

  (test 5 (eval-to-num '(try 5 catch (x) 2)))
  (test 2 (eval-to-num '(try (raise 10) catch (x) 2)))
  (test 10 (eval-to-num '(try (raise 10) catch (x) x)))
  (test 2 (eval-to-num
           '(try (try (raise 6) catch (x) (raise (- x 1)))
                 catch (y) (- y 3))))
  )
