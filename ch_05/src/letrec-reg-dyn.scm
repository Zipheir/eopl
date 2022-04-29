;;;; Registerized CPS LETREC interpreter from Sec. 5.3,
;;;; with dynamic binding.

(import (rnrs base (6))
        (rnrs lists (6)))

(include "../../src/pmatch.scm")
(include "../../src/test.scm")

;;;; Registers

(define *exp-reg* 'uninitialized)
(define *env-reg* 'uninitialized)
(define *cont-reg* 'uninitialized)
(define *val-reg* 'uninitialized)
(define *proc1-reg* 'uninitialized)

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

;; expval->list : Exp-val -> List
(define (expval->list val)
  (pmatch val
    ((list-val ,l) l)
    (? (report-expval-extractor-error 'list val))))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;;;; Procedures

(define (procedure b-var body)
  (list 'proc b-var body))

;; apply-procedure/k : () -> Final-answer
;;
;; Relies on regs
;;   *proc1-reg* : Proc
;;   *cont-reg*  : Cont
(define (apply-procedure/k)
  (pmatch *proc1-reg*
    ((proc ,var ,body)
     (set! *exp-reg* body)
     (set! *env-reg* (extend-env var *val-reg* *env-reg*))
     (value-of/k))))

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
     (if (eqv? search-var var)
         val
         (apply-env env* search-var)))
    (((ext-rec ,p-name ,b-vars ,p-body) . ,env*)
     (if (eqv? p-name search-var)
         (list 'proc-val (procedure b-vars p-body))
         (apply-env env* search-var)))
    (? (error 'apply-env "invalid environment" env))))

(define (report-no-binding-found var)
  (error 'apply-env "no binding found" var))

;; alist->env : List-of(Var x Scheme-val) -> Env
;; No recursive bindings.
(define (alist->env as)
  (fold-right (lambda (p e) (extend-env (car p) (cdr p) e))
              (empty-env)
              as))

;;; Initial environment

;; init-env : () -> Env
(define (init-env)
  (alist->env `((i . (num-val 1))
                (v . (num-val 5))
                (x . (num-val 10)))))

;;;; Continuations

;; apply-cont : () -> Final-answer
;;
;; Relies on registers
;;   *cont-reg* : Cont
;;   *val-reg*  : Exp-val
;;
;; The continuation register is always updated first.
(define (apply-cont)
  (pmatch *cont-reg*
    ((end-cont ,print-msg)
     (when print-msg (display "End of computation.\n"))
     *val-reg*)
    ((zero1-cont ,k)
     (set! *cont-reg* k)
     (set! *val-reg* `(bool-val ,(zero? (expval->num *val-reg*))))
     (apply-cont))
    ((if-test-cont ,exp2 ,exp3 ,env ,k)
     (set! *cont-reg* k)
     (if (expval->bool *val-reg*)
         (set! *exp-reg* exp2)
         (set! *exp-reg* exp3))
     (set! *env-reg* env)
     (value-of/k))
    ((let-exp-cont ,var ,body ,env ,k)
     (set! *cont-reg* k)
     (set! *exp-reg* body)
     (set! *env-reg* (extend-env var *val-reg* env))
     (value-of/k))
    ((diff1-cont ,exp2 ,env ,k)
     (set! *cont-reg* `(diff2-cont ,*val-reg* ,k))
     (set! *exp-reg* exp2)
     (set! *env-reg* env)
     (value-of/k))
    ((diff2-cont ,val1 ,k)
     (set! *cont-reg* k)
     (let ((num1 (expval->num val1))
           (num2 (expval->num *val-reg*)))
       (set! *val-reg* `(num-val ,(- num1 num2))))
     (apply-cont))
    ((rator-cont ,rand ,env ,k)
     (set! *cont-reg* `(rand-cont ,*val-reg* ,env ,k))
     (set! *env-reg* env)
     (set! *exp-reg* rand)
     (value-of/k))
    ((rand-cont ,vrat ,env ,k)
     (set! *cont-reg* k)
     (set! *proc1-reg* (expval->proc vrat))
     (apply-procedure/k))
    (? (error 'apply-cont "invalid continuation" *cont-reg*))))

;;;; Interpreter

;; value-of-program : Program x Bool -> Final-answer
(define (value-of-program pgm print-msg)
  (pmatch pgm
    ((program ,exp1)
     (set! *cont-reg* `(end-cont ,print-msg))
     (set! *exp-reg* exp1)
     (set! *env-reg* (init-env))
     (value-of/k))))

;; value-of/k : () -> Final-answer
;; Notice that there's still a lot of information being stored in
;; the continuation values.  More registerization is possible.
(define (value-of/k)
  (pmatch *exp-reg*
    ((const-exp ,n)
     (set! *val-reg* `(num-val ,n))
     (apply-cont))
    ((var-exp ,var)
     (set! *val-reg* (apply-env *env-reg* var))
     (apply-cont))
    ((proc-exp ,var ,body)
     (set! *val-reg* `(proc-val ,(procedure var body)))
     (apply-cont))
    ((zero?-exp ,exp1)
     (set! *cont-reg* `(zero1-cont ,*cont-reg*))
     (set! *exp-reg* exp1)
     (value-of/k))
    ((diff-exp ,exp1 ,exp2)
     (set! *cont-reg* `(diff1-cont ,exp2 ,*env-reg* ,*cont-reg*))
     (set! *exp-reg* exp1)
     (value-of/k))
    ((if-exp ,exp1 ,exp2 ,exp3)
     (set! *cont-reg*
           `(if-test-cont ,exp2 ,exp3 ,*env-reg* ,*cont-reg*))
     (set! *exp-reg* exp1)
     (value-of/k))
    ((let-exp ,var ,exp1 ,body)
     (set! *cont-reg*
           `(let-exp-cont ,var ,body ,*env-reg* ,*cont-reg*))
     (set! *exp-reg* exp1)
     (value-of/k))
    ((letrec-exp ,p-name ,b-vars ,p-body ,lr-body)
     (set! *exp-reg* lr-body)
     (set! *env-reg* (extend-env-rec p-name b-vars p-body *env-reg*))
     (value-of/k))
    ((call-exp ,rator ,rand)
     (set! *cont-reg* `(rator-cont ,rand ,*env-reg* ,*cont-reg*))
     (set! *exp-reg* rator)
     (value-of/k))
    (? (error 'value-of/k "invalid expression" exp))))

;; Parser for a simple S-exp representation.
;; parse : List -> Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) `(const-exp ,n))
    (emptylist '(emptylist-exp))
    ((- ,s ,t) `(diff-exp ,(parse s) ,(parse t)))
    ((zero? ,s) `(zero?-exp ,(parse s)))
    ((if ,t ,c ,a) `(if-exp ,(parse t) ,(parse c) ,(parse a)))
    (,v (guard (symbol? v)) `(var-exp ,v))
    ((let ,v = ,exp1 in ,body) (guard (symbol? v))
     `(let-exp ,v ,(parse exp1) ,(parse body)))
    ((proc (,v) ,body) (guard (symbol? v))
     `(proc-exp ,v ,(parse body)))
    ((letrec ,nm (,v) = ,pbody in ,lrbody)
     (guard (symbol? nm) (symbol? v))
     `(letrec-exp ,nm ,v ,(parse pbody) ,(parse lrbody)))
    ((,e1 ,e2) `(call-exp ,(parse e1) ,(parse e2)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-program : List -> Program
(define (parse-program sexp)
  (list 'program (parse sexp)))

;; run : List ... -> Final-answer
(define (run sexp . opt)
  (let ((print-msg (and (pair? opt) (car opt))))
    (value-of-program (parse-program sexp) print-msg)))

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

  ;; Dynamic binding
  
  (test 5 (eval-to-num
           '(let x = 7
             in (let f = (proc (y) x)
                 in (let x = 5
                     in (f 0))))))
  )
