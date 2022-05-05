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

;; apply-procedure/k : Proc x Ref x Cont -> Final-answer
(define (apply-procedure/k proc1 val cont)
  (pmatch proc1
    ((proc ,var ,body ,env)
     (value-of/k body (extend-env var val env) cont))))

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
;;
;; Backtracks through the continuation stack until a try-cont
;; is found, then runs the included handler.
;;
;; This would be more compact if continuations used the stack
;; representation of Ex. 5.15.  As it is, every continuation
;; variety has to be considered.
(define (apply-handler val cont)
  (pmatch cont
    ((try-cont ,var ,hexp ,senv ,k)
     (value-of/k hexp (extend-env var val senv) k))
    ((end-cont ?) (report-uncaught-exception))
    ((zero1-cont ,k) (apply-handler val k))
    ((if-test-cont ? ? ? ,k) (apply-handler val k))
    ((let-exp-cont ? ? ? ,k) (apply-handler val k))
    ((diff1-cont ? ? ,k) (apply-handler val k))
    ((diff2-cont ? ? ,k) (apply-handler val k))
    ((div1-cont ? ? ,k) (apply-handler val k))
    ((div2-cont ? ,k) (apply-handler val k))
    ((rator-cont ? ? ,k) (apply-handler val k))
    ((rand-cont ? ? ,k) (apply-handler val k))
    ((raise1-cont ,k) (apply-handler val k))
    (? (error 'apply-handler "invalid continuation" cont))))

;; report-uncaught-exception : () -> [Bottom]
(define (report-uncaught-exception)
  (error 'report-uncaught-exception "uncaught exception"))

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
     (value-of/k body (extend-env var val env) k))
    ((diff1-cont ,exp2 ,env ,k)
     (value-of/k exp2 env `(diff2-cont ,val ,env ,k)))
    ((diff2-cont ,val1 ,env ,k)
     (let ((num1 (expval->num val1))
           (num2 (expval->num val)))
       (apply-cont k `(num-val ,(- num1 num2)))))
    ((div1-cont ,exp2 ,env ,k)
     (value-of/k exp2 env `(div2-cont ,val ,k)))
    ((div2-cont ,val1 ,k)
     (let ((num1 (expval->num val1))
           (num2 (expval->num val)))
       (if (zero? num2)
           (apply-handler `(condition "divide by zero" num1) cont)
           (apply-cont k `(num-val ,(/ num1 num2))))))
    ((rator-cont ,rand ,env ,k)
     (value-of/k rand env `(rand-cont ,val ,env ,k)))
    ((rand-cont ,vrat ,env ,k)
     (apply-procedure/k (expval->proc vrat) val k))
    ((try-cont ? ? ? ,k) (apply-cont k val))
    ((raise1-cont ,k) (apply-handler val k))
    (? (error 'apply-cont "invalid continuation" cont))))

;;;; Interpreter

;; value-of-program : Program x Bool -> Final-answer
(define (value-of-program pgm print-msg)
  (pmatch pgm
    ((program ,exp1)
     (value-of/k exp1 (init-env) `(end-cont ,print-msg)))))

;; value-of/k : Exp x Env x Cont -> Final-answer
(define (value-of/k exp env cont)
  (pmatch exp
    ((const-exp ,n) (apply-cont cont `(num-val ,n)))
    ((var-exp ,var) (apply-cont cont (apply-env env var)))
    ((proc-exp ,var ,body)
     (apply-cont cont `(proc-val ,(procedure var body env))))
    ((zero?-exp ,exp1) (value-of/k exp1 env `(zero1-cont ,cont)))
    ((diff-exp ,exp1 ,exp2)
     (value-of/k exp1 env `(diff1-cont ,exp2 ,env ,cont)))
    ((div-exp ,exp1 ,exp2)
     (value-of/k exp1 env `(div1-cont ,exp2 ,env ,cont)))
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
    ((try-exp ,exp1 ,var ,hexp)
     (value-of/k exp1 env `(try-cont ,var ,hexp ,env ,cont)))
    ((raise-exp ,exp1)
     (value-of/k exp1 env `(raise1-cont ,cont)))
    (? (error 'value-of/k "invalid expression" exp))))

;; Parser for a simple S-exp representation.
;; parse : List -> Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) `(const-exp ,n))
    ((- ,s ,t) `(diff-exp ,(parse s) ,(parse t)))
    ((/ ,a ,b) `(div-exp ,(parse a) ,(parse b)))
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

  (test 5 (eval-to-num '(try 5 catch (x) 2)))
  (test 2 (eval-to-num '(try (raise 10) catch (x) 2)))
  (test 10 (eval-to-num '(try (raise 10) catch (x) x)))
  (test 2 (eval-to-num
           '(try (try (raise 6) catch (x) (raise (- x 1)))
                 catch (y) (- y 3))))

  (test 2 (eval-to-num '(/ 8 4)))
  (test 3 (eval-to-num '(try (/ 8 0) catch (junk) 3)))
  )