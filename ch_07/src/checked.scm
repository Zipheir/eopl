;;;; CHECKED language from Ch. 7.

(import (rnrs base (6))
        (rename (rnrs lists (6)) (for-all every)))

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

;; apply-procedure : Proc x Val -> Final-answer
(define (apply-procedure proc1 val)
  (pmatch proc1
    ((proc ,var ,body ,env)
     (value-of body (extend-env var val env)))))

;;;; Environments

;; empty-env : () -> Env
(define (empty-env) '())

;; extend-env : Var x Exp-val x Env -> Env
(define (extend-env var val env)
  (cons (list 'ext var val) env))

;; extend-env-rec : Var x Var x Exp-val	x Env -> Env
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
    (((ext-rec ,p-name ,b-var ,p-body) . ,env*)
     (if (eqv? search-var var)
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

;;; Type environments

;; tenv = List-of(Sym x Type)

(define (init-tenv) '())

(define (extend-tenv var type tenv)
  (cons (cons var type) tenv))

(define (extend-tenv* alist tenv)
  (append alist tenv))

(define (apply-tenv tenv var)
  (cond ((assv var tenv) => cdr)
        (else
         (error 'apply-tenv "untyped variable" var))))

;;; Types

;; check-equal-type : Type x Type x Exp -> ()
(define (check-equal-type ty1 ty2 exp)
  (unless (equal? ty1 ty2)
    (report-unequal-types ty1 ty2 exp)))

;; report-unequal-types : Type x Type x Exp -> ()
(define (report-unequal-types ty1 ty2 exp)
  (error 'check-equal-type
         "types didn't match"
         (type-to-external-form ty1)
         (type-to-external-form ty2)
         exp))

;; type-to-external-form : Type -> List
(define (type-to-external-form ty)
  (pmatch ty
    (int-type 'int)
    (bool-type 'bool)
    ((proc-type ,arg-type ,res-type)
     `(,(type-to-external-form arg-type)
       ->
       ,(type-to-external-form res-type)))))

;; type-of-program : Program -> Type
(define (type-of-program pgm)
  (pmatch pgm
    ((program ,exp1)
     (type-of exp1 (init-tenv)))))

;; type-of : Exp x Tenv -> Type
(define (type-of exp tenv)
  (pmatch exp
    ((const-exp ?) 'int-type)
    ((var-exp ,v) (apply-tenv tenv v))
    ((diff-exp ,exp1 ,exp2)
     (check-equal-type (type-of exp1 tenv) 'int-type exp1)
     (check-equal-type (type-of exp2 tenv) 'int-type exp2)
     'int-type)
    ((zero?-exp ,exp1)
     (check-equal-type (type-of exp1 tenv) 'int-type exp1)
     'bool-type)
    ((if-exp ,exp1 ,exp2 ,exp3)
     (check-equal-type (type-of exp1 tenv) 'bool-type exp1)
     (let ((ty1 (type-of exp2 tenv))
           (ty2 (type-of exp3 tenv)))
       (check-equal-type ty1 ty2 exp)
       ty2))
    ((let-exp ,var ,exp1 ,body)
     (let ((ty1 (type-of exp1 tenv)))
       (type-of body (extend-tenv var ty1 tenv))))
    ((proc-exp ,var ,var-type ,body)
     (let ((res-type (type-of body (extend-tenv var var-type tenv))))
       `(proc-type ,var-type ,res-type)))
    ((call-exp ,rator ,rand) (type-of-call-exp rator rand tenv))
    ((letrec-exp . ,rest)
     (apply type-of-letrec-exp (append rest (list tenv))))
    (? (error 'type-of "invalid expression" exp))))

;; type-of-call-exp : Exp x Exp x Tenv -> Type
(define (type-of-call-exp rator rand tenv)
  (let ((rator-type (type-of rator tenv)))
    (pmatch rator-type
      ((proc-type ,t-op ,t-res)
       (check-equal-type t-op (type-of rand tenv) rand)
       t-res)
      (? (error 'type-of "not a procedure type" rator-type rator)))))

;; type-of-letrec-exp : Type x Var x Var x Type x Exp x Exp x
;;                        Tenv -> Type
(define (type-of-letrec-exp p-res-type p-name b-var b-var-type p-body
                            lr-body tenv)
  (let* ((p-type `(proc-type ,b-var-type ,p-res-type))
         (lr-body-tenv (extend-tenv p-name p-type tenv))
         (p-body-type
          (type-of p-body
                   (extend-tenv b-var b-var-type lr-body-tenv))))
    (check-equal-type p-body-type p-res-type p-body)
    (type-of lr-body lr-body-tenv)))

;;; Interpreter

;; The usual, just like LETREC.  TODO.

;;; Parser

(define (parse-program sexp)
  (list 'program (parse sexp)))

(define (natural? x)
  (and (integer? x) (not (negative? x))))

;; parse : S-exp -> Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (natural? n)) `(const-exp ,n))
    (,v (guard (symbol? v)) `(var-exp ,v))
    ((- ,e1 ,e2)
     `(diff-exp ,(parse e1) ,(parse e2)))
    ((zero? ,e) `(zero?-exp ,(parse e)))
    ((if ,e1 ,e2 ,e3)
     `(if-exp ,(parse e1) ,(parse e2) ,(parse e3)))
    ((let ,v = ,e in ,b) (guard (symbol? v))
     `(let-exp ,v ,(parse e) ,(parse b)))
    ((proc (,v : ,t) ,e) (guard (symbol? v))
     `(proc-exp ,v ,(parse-type t) ,(parse e)))
    ((letrec ,rt ,nm (,v : ,vt) = ,e in ,b)
     (guard (symbol? nm) (symbol? v))
     `(letrec-exp ,(parse-type rt) ,nm ,v ,(parse-type vt) ,(parse e)
                  ,(parse b)))
    ((,e1 ,e2) `(call-exp ,(parse e1) ,(parse e2)))
    (? (error 'parse "syntax error" sexp))))

;; parse-type : S-exp -> Type
(define (parse-type sexp)
  (pmatch sexp
    (int 'int-type)
    (bool 'bool-type)
    ((,t1 -> ,t2) `(proc-type ,(parse-type t1) ,(parse-type t2)))
    (? (error 'parse-type "invalid type syntax" sexp))))
