;;;; CPS-OUT interpreter from Ch. 6

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

;;;; Environments

;; empty-env : () -> Env
(define (empty-env) '())

;; extend-env* : List-of(Var) x List-of(Exp-val) x Env -> Env
(define (extend-env* vars vals env)
  (cons (list 'ext-env vars vals) env))

;; extend-env-rec** : List-of(Var) x List-of(List-of(Var)) x
;;                      List-of(Exp-val) x Env -> Env
(define (extend-env-rec** p-names b-varss p-bodies env)
  (cons (list 'ext-env-rec p-names b-varss p-bodies) env))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (pmatch env
    (() (report-no-binding-found search-var))
    (((ext-env ,vars ,vals) . ,env*)
     (cond ((location search-var vars) => (lambda (n)
                                            (list-ref vals n)))
           (else (apply-env env* search-var))))
    (((ext-env-rec ,p-names ,b-varss ,p-bodies) . ,env*)
     (cond ((location search-var p-names) =>
            (lambda (n)
              `(proc-val
                (proc ,(list-ref b-varss n)
                      ,(list-ref p-bodies n)
                      ,env))))
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
  (extend-env* (map car as) (map cdr as) (empty-env)))

;;; Initial environment

;; init-env : () -> Env
(define (init-env)
  (alist->env `((i . (num-val 1))
                (v . (num-val 5))
                (x . (num-val 10)))))

;;; Interpreter

;; value-of/k : Tf-exp x Env x Cont -> Final-answer
(define (value-of/k exp env cont)
  (pmatch exp
    ((simple-exp->exp ,simple)
     (apply-cont cont (value-of-simple-exp simple env)))
    ((cps-let-exp ,var ,rhs ,body)
     (let ((val (value-of-simple-exp rhs env)))
       (value-of/k body
                   (extend-env* (list var) (list val) env)
                   cont)))
    ((cps-letrec-exp ,p-names ,b-varss ,p-bodies ,letrec-body)
     (value-of/k letrec-body
                 (extend-env-rec** p-names b-varss p-bodies env)
                 cont))
    ((cps-if-exp ,simple1 ,body1 ,body2)
     (if (expval->bool (value-of-simple-exp simple1 env))
         (value-of/k body1 env cont)
         (value-of/k body2 env cont)))
    ((cps-call-exp ,rator ,rands)
     (let ((proc (expval->proc (value-of-simple-exp rator env)))
           (vals (map (lambda (s) (value-of-simple-exp s env))
                      rands)))
       (apply-procedure/k proc vals cont)))))

;; apply-procedure/k : Proc x Exp-vals x Cont -> Final-answer
(define (apply-procedure/k proc args cont)
  (pmatch proc
    ((proc ,vars ,body ,saved-env)
     (value-of/k body
                 (extend-env* vars args saved-env)
                 cont))))

;; apply-cont : Cont x Exp-val -> Final-answer
(define (apply-cont cont val)
  (pmatch cont
    (end-cont val)
    (? (error 'apply-cont "invalid continuation" cont))))

;; value-of-simple-exp : Simple-exp x Env -> Exp-val
(define (value-of-simple-exp simple env)
  (pmatch simple
    ((cps-const-exp ,num) `(num-val ,num))
    ((cps-var-exp ,var) (apply-env env var))
    ((cps-diff-exp ,simple1 ,simple2)
     `(num-val
       ,(- (expval->num (value-of-simple-exp simple1 env))
           (expval->num (value-of-simple-exp simple2 env)))))
    ((cps-sum-exp ,simples)
     `(num-val
       ,(apply + (map (lambda (s)
                        (expval->num (value-of-simple-exp s env)))
                      simples))))
    ((cps-zero?-exp ,simple1)
     `(bool-val
       ,(zero? (expval->num (value-of-simple-exp simple1 env)))))
    ((cps-proc-exp ,vars ,body)
     `(proc-val (proc ,vars ,body ,env)))
    (? (error 'value-of-simple-exp
              "invalid simple expression"
              simple))))

;;; Programs

;; value-of-program : Program -> Final-answer
(define (value-of-program pgm)
  (pmatch pgm
    ((cps-program ,tf-exp)
     (value-of/k tf-exp (init-env) 'end-cont))))
