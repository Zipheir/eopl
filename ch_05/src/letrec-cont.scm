;;;; CPS LETREC interpreter from Ch. 5.

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

(define (procedure b-var body saved-env)
  (list 'proc b-var body saved-env))

;; apply-procedure/k : Proc x Ref x Cont -> Final-answer
(define (apply-procedure/k proc1 val cont)
  (pmatch proc1
    ((proc ,var ,body ,env)
     (value-of/k body (extend-env1 var val env) cont))))

;;;; Environments

;; empty-env : () -> Env
(define (empty-env) '())

;; extend-env : List-of(Var) x List-of(Exp-val) x Env -> Env
(define (extend-env vars vals env)
  (cons (list 'ext vars vals) env))

(define (extend-env1 var val env)
  (extend-env (list var) (list val) env))

;; extend-env-rec : List-of(Var) x List-of(Var) x List-of(Exp-val)
;;                  x Env -> Env
(define (extend-env-rec p-names b-vars p-bodies env)
  (cons (list 'ext-rec p-names b-vars p-bodies) env))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (pmatch env
    (() (report-no-binding-found search-var))
    (((ext ,vars ,vals) . ,env*)
     (cond ((location search-var vars) => (lambda (n)
                                            (list-ref vals n)))
           (else (apply-env env* search-var))))
    (((ext-rec ,p-names ,b-vars ,p-bodies) . ,env*)
     (cond ((location search-var p-names) =>
            (lambda (n)
              (list 'proc-val
                    (procedure (list-ref b-vars n)
                               (list-ref p-bodies n)
                               env))))
           (else (apply-env env* search-var))))
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
  (extend-env (map car as) (map cdr as) (empty-env)))

;;; Initial environment

;; init-env : () -> Env
(define (init-env)
  (alist->env `((i . (num-val 1))
                (v . (num-val 5))
                (x . (num-val 10)))))

;;;; Continuations

;; apply-cont : Cont x (Val + List-of(Val)) -> Final-answer
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
    ((let-exps-cont ,vars ,body ,env ,k)
     (value-of/k body (extend-env vars val env) k))
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
    ((cons-car-cont ,dexp ,env ,k)
     (value-of/k dexp env `(cons-cdr-cont ,val ,k)))
    ((cons-cdr-cont ,car-val ,k)
     (apply-cont k `(list-val ,(cons car-val (expval->list val)))))
    ((car1-cont ,k) (apply-cont k (car (expval->list val))))
    ((cdr1-cont ,k)
     (apply-cont k `(list-val ,(cdr (expval->list val)))))
    ((null1-cont ,k)
     (apply-cont k `(bool-val ,(null? (expval->list val)))))
    ((evlis-continue-cont ,exps ,env ,k)
     (eval-list/k exps env `(evlis-collect-cont ,val ,k)))
    ((evlis-collect-cont ,car-val ,k)
     (apply-cont k (cons car-val val)))
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
    ((if-exp ,exp1 ,exp2 ,exp3)
     (value-of/k exp1 env `(if-test-cont ,exp2 ,exp3 ,env ,cont)))
    ((let-exp ,vars ,exps ,body)
     (eval-list/k exps env `(let-exps-cont ,vars ,body ,env ,cont)))
    ((letrec-exp ,p-names ,b-vars ,p-bodies ,lr-body)
     (value-of/k lr-body
                 (extend-env-rec p-names b-vars p-bodies env)
                 cont))
    ((call-exp ,rator ,rand)
     (value-of/k rator env `(rator-cont ,rand ,env ,cont)))
    ((emptylist-exp) (apply-cont cont '(list-val ())))
    ((cons-exp ,aexp ,dexp)
     (value-of/k aexp env `(cons-car-cont ,dexp ,env ,cont)))
    ((car-exp ,lexp) (value-of/k lexp env `(car1-cont ,cont)))
    ((cdr-exp ,lexp) (value-of/k lexp env `(cdr1-cont ,cont)))
    ((null?-exp ,exp1) (value-of/k exp1 env `(null1-cont ,cont)))
    ((list-exp ,exps) `(list-val ,(eval-list/k exps env cont)))
    (? (error 'value-of/k "invalid expression" exp))))

;; eval-list/k : List-of(Exp) x Env x Cont -> Final-answer
;;
;; Usage: Evaluates a list of expressions in env and delivers
;; the list of results to cont.
(define (eval-list/k exps env cont)
  (pmatch exps
    (() (apply-cont cont '()))
    ((,e . ,es)
     (value-of/k e env `(evlis-continue-cont ,es ,env ,cont)))))

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
    ((let ,bs in ,b) (parse-let-exp bs b))
    ((proc (,v) ,body) (guard (symbol? v))
     `(proc-exp ,v ,(parse body)))
    ((letrec ,bs in ,body) (parse-letrec-exp bs body))
    ((cons ,a ,d) `(cons-exp ,(parse a) ,(parse d)))
    ((car ,l) `(car-exp ,(parse l)))
    ((cdr ,l) `(cdr-exp ,(parse l)))
    ((null? ,e) `(null?-exp ,(parse e)))
    ((list . ,es) `(list-exp ,(map parse es)))
    ((,e1 ,e2) `(call-exp ,(parse e1) ,(parse e2)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-let-exp : List x List -> Exp
(define (parse-let-exp binds body)
  (letrec
    ((collect
      (lambda (bs vars vals)
        (pmatch bs
          (() (values vars vals))
          (((,v = ,e) . ,bs*) (guard (symbol? v))
           (collect bs* (cons v vars) (cons (parse e) vals)))))))

    (let-values (((vars vals) (collect binds '() '())))
      `(let-exp ,vars ,vals ,(parse body)))))

(define (parse-letrec-exp binds body)
  (let* ((f (lambda args
              (pmatch args
                (((,g (,v) = ,e) (,names ,b-vars ,bodies))
                 (guard (symbol? g) (symbol? v))
                 `((,g . ,names)
                   (,v . ,b-vars)
                   (,(parse e) . ,bodies))))))
         (ts (fold-right f '(() () ()) binds)))
    (pmatch ts
      ((,names ,vars ,bodies)
       `(letrec-exp ,names ,vars ,bodies ,(parse body))))))

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

  (define (eval-to-num-list exp)
    (map expval->num (expval->list (run exp #f))))

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
  (test 5 (eval-to-num
           '(let ((a = 8) (b = 1) (c = 2)) in (- (- a b) c))))
  (test 1 (eval-to-num
           '(letrec ((even (x) = (if (zero? x) 1 (odd (- x 1))))
                     (odd (x) = (if (zero? x) 0 (even (- x 1)))))
             in (even 4))))
  (test 0 (eval-to-num
           '(letrec ((even (x) = (if (zero? x) 1 (odd (- x 1))))
                     (odd (x) = (if (zero? x) 0 (even (- x 1)))))
             in (even 5))))

  ;;; Lists

  (test '() (eval-to-num-list 'emptylist))
  (test '(1) (eval-to-num-list '(cons 1 emptylist)))
  (test '(1 2 3) (eval-to-num-list '(cons 1 (cons 2 (cons 3 emptylist)))))
  (test 1 (eval-to-num '(car (cons 1 emptylist))))
  (test '(2 3) (eval-to-num-list
                '(cdr (cons 1 (cons 2 (cons 3 emptylist))))))
  (test 1 (eval-to-num '(if (null? emptylist) 1 0)))
  (test 0 (eval-to-num '(if (null? (cons 1 emptylist)) 1 0)))
  (test '() (eval-to-num-list '(list)))
  (test '(1 2 3) (eval-to-num-list '(list 1 2 3)))
  (test '(1 5 10) (eval-to-num-list '(list i v x)))
  )
