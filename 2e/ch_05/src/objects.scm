;;;; Object-oriented language from Ch. 5 (2e)

(import (rnrs base (6))
        )

(include "../../../src/pmatch.scm")

;;;; References

(define (deref ref)
  (pmatch ref
    ((a-ref ,k ,vec) (vector-ref vec k))
    (? (error 'deref "not a reference" ref))))

(define (setref! ref val)
  (pmatch ref
    ((a-ref ,k ,vec) (vector-set! vec k val))
    (? (error 'setref! "not a reference" ref))))

;;;; Expressed values

;; expval->num : Exp-val -> Int
(define (expval->num val)
  (pmatch val
    ((num-val ,n) n)
    (? (report-expval-extractor-error 'num val))))

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

;;;; Environments

;; empty-env : () -> Env
(define (empty-env) '())

;; extend-env : List-of(Var) x List-of(Exp-val) x Env -> Env
(define (extend-env vars vals env)
  (cons (list 'ext vars (list->vector vals)) env))

;; extend-env-rec : List-of(Var) x List-of(List-of(Var)) x
;;                    List-of(Exp-val) x Env -> Env
(define (extend-env-rec p-names b-varss p-bodies old-env)
  (cons (list 'ext-rec p-names b-varss p-bodies) old-env))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (deref (apply-env-ref env search-var)))

;; apply-env-ref : Env x Var -> Ref
(define (apply-env-ref env search-var)
  (pmatch env
    (() (report-no-binding-found search-var))
    (((ext ,vars ,vals) . ,env*)
     (cond ((rib-find-position search-var vars) =>
            (lambda (pos) `(a-ref ,pos ,vals)))
           (else (apply-env-ref env* search-var))))
    (? (error 'apply-env-ref "invalid environment" env))))

(define (report-no-binding-found var)
  (error 'apply-env "no binding found" var))

;; rib-find-position : Var x List-of(Var) -> Int-or-false
(define (rib-find-position var lis)
  (letrec
   ((find
     (lambda (lis i)
       (cond ((null? lis) #f)
             ((eqv? (car lis) var) i)
             (else (find (cdr lis) (+ i 1)))))))
    (find lis 0)))

;; alist->env : List-of(Var x Scheme-val) -> Env
;; No recursive bindings.
(define (alist->env as)
  (fold-right (lambda (p env)
                (extend-env (car p) (cdr p) env))
              (empty-env)
              as))
