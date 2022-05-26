;;;; CHECKED language from Ch. 7.

(import (rnrs base (6))
        (rnrs exceptions (6))
        (rnrs records syntactic (6))
        (rename (rnrs lists (6)) (for-all every)))

(include "../../../src/pmatch.scm")
(include "../../../src/test.scm")

;;;; Utility

(define (unzip ps)
  (if (null? ps)
      (list '() '())
      (pmatch (unzip (cdr ps))
        ((,as ,bs)
	 (list (cons (caar ps) as)
	       (cons (cadar ps) bs))))))

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

;;; Type environments

;; tenv = List-of(Sym x Type)

(define (init-tenv) '())

(define (extend-tenv var type tenv)
  (cons (cons var type) tenv))

(define (extend-tenv* vars types tenv)
  (append (map cons vars types) tenv))

(define (apply-tenv tenv var)
  (cond ((assv var tenv) => cdr)
        (else
         (error 'apply-tenv "untyped variable" var))))

;;; Types

(define-record-type (&type-cond make-type-cond type-cond?)
  (parent &condition)
  (fields
   (immutable type1 type-cond-type1)
   (immutable type2 type-cond-type2)
   (immutable expression type-cond-expression)))

;; check-equal-type : Type x Type x Exp -> ()
(define (check-equal-type ty1 ty2 exp)
  (unless (equal? ty1 ty2)
    (raise (make-type-cond ty1 ty2 exp))))

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
    (true-exp 'bool-type)
    (false-exp 'bool-type)
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
    ((let-exp ,vars ,exps ,body)
     (let ((types (map (lambda (e) (type-of e tenv)) exps)))
       (type-of body (extend-tenv* vars types tenv))))
    ((proc-exp ,var-types ,vars ,body)
     `(proc-type ,var-types
                 ,(type-of body
                           (extend-tenv* vars var-types tenv))))
    ((call-exp ,rator ,rands)
     (type-of-call-exp rator rands exp tenv))
    ((letrec-exp . ,rest)
     (apply type-of-letrec-exp (append rest (list tenv))))
    (? (error 'type-of "invalid expression" exp))))

;; type-of-call-exp : Exp x List-of(Exp) x Exp x Tenv -> Type
(define (type-of-call-exp rator rands orig-exp tenv)
  (let ((rator-type (type-of rator tenv))
        (rand-types (map (lambda (e) (type-of e tenv)) rands)))
    (pmatch rator-type
      ((proc-type ,t-ids ,t-res)
       (unless (= (length t-ids) (length rands))
         (error 'type-of "too many/few arguments" orig-exp))
       (for-each (lambda (t1 t2)
                   (check-equal-type t1 t2 orig-exp))
                 t-ids
                 rand-types)
       t-res)
      (? (raise (make-type-cond rator-type 'proc-type orig-exp))))))

;; type-of-letrec-exp : List-of(Type) x List-of(Var) x
;;                        List-of(List-of(Var)) x
;;			  List-of(List-of(Type)) x List-of(Exp) x
;;			  Exp x Tenv -> Type
(define (type-of-letrec-exp p-res-types p-names b-varss b-var-typess
                            p-bodies lr-body tenv)
  (let* ((p-types (map (lambda (bvts rt) `(proc-type ,bvts ,rt))
                       b-var-typess
                       p-res-types))
         (lr-body-tenv (extend-tenv* p-names p-types tenv)))
    (for-each (lambda (vars var-types body res-type)
                (let ((ext (extend-tenv* vars var-types lr-body-tenv)))
                  (check-equal-type (type-of body ext) res-type body)))
              b-varss
              b-var-typess
              p-bodies
              p-res-types)
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
    (true 'true-exp)
    (false 'false-exp)
    (,v (guard (symbol? v)) `(var-exp ,v))
    ((- ,e1 ,e2)
     `(diff-exp ,(parse e1) ,(parse e2)))
    ((zero? ,e) `(zero?-exp ,(parse e)))
    ((if ,e1 ,e2 ,e3)
     `(if-exp ,(parse e1) ,(parse e2) ,(parse e3)))
    ((let ,binds in ,b) (parse-let-exp binds b))
    ((proc ,args ,e) (parse-proc-exp args e))
    ((letrec ,binds in ,b) (parse-letrec-exp binds b))
    ((,e1 . ,es) `(call-exp ,(parse e1) ,(map parse es)))
    (? (error 'parse "syntax error" sexp))))

;; parse-type : S-exp -> Type
(define (parse-type sexp)
  (pmatch sexp
    (int 'int-type)
    (bool 'bool-type)
    ((-> ,arg-ts ,res-t) (guard (pair? arg-ts))
     `(proc-type ,(map parse-type arg-ts) ,(parse-type res-t)))
    (? (error 'parse-type "invalid type syntax" sexp))))

;; parse-let-exp : List-of(S-exp x Sym) x S-exp -> Exp
(define (parse-let-exp binds body)
  (letrec
   ((collect
     (lambda (bs ids exps)
       (pmatch bs
         (() (values ids exps))
         (((,v = ,e) . ,bs*) (guard (symbol? v))
          (collect bs* (cons v ids) (cons (parse e) exps)))
         (? (error 'parse "syntax error" bs))))))

    (let-values (((ids exps) (collect binds '() '())))
      `(let-exp ,ids ,exps ,(parse body)))))

;; parse-letrec-exp : List x S-exp -> Exp
(define (parse-letrec-exp binds lr-body)
  (letrec
   ((collect
     (lambda (bs res-ts p-names texpss idss bodies)
       (pmatch bs
         (() (values res-ts p-names texpss idss bodies))
         (((,rt ,nm ,vs = ,body) . ,bs*)
          (let-values (((ids ts) (parse-args vs)))
            (collect bs*
                     (cons (parse-type rt) res-ts)
                     (cons nm p-names)
                     (cons ts texpss)
                     (cons ids idss)
                     (cons (parse body) bodies))))))))

    (let-values (((res-ts p-names texpss idss bodies)
                  (collect binds '() '() '() '() '())))
      (list 'letrec-exp res-ts p-names idss texpss bodies
            (parse lr-body)))))

;; parse-args : List -> (List-of(Sym) x List-of(Type))
(define (parse-args args+types)
  (pmatch (unzip args+types)
    ((,ids ,ts) (guard (every symbol? ids))
     (values ids (map parse-type ts)))))

;; parse-proc-exp : List x List -> Exp
(define (parse-proc-exp args body)
  (let-values (((ids ts) (parse-args args)))
    `(proc-exp ,ts ,ids ,(parse body))))

;; Convenience driver
(define (check sexp)
  (type-of-program (parse-program sexp)))

;;; Tests

(define (run-tests)
  (define (rejected? sexp)
    (guard (con
             ((type-cond? con) #t)
             (else (raise con)))
      (check sexp)))

  (test 'bool-type (check 'true))
  (test 'bool-type (check 'false))
  (test 'int-type (check 4))
  (test 'bool-type (check '(zero? 4)))
  (test 'int-type (check '(- 4 1)))
  (test 'int-type (check '(if (zero? 3) 1 0)))
  (test 'int-type (check '(let ((x = 4)) in x)))
  (test 'bool-type (check '(let ((z = (zero? 3))) in z)))
  (test '(proc-type (int-type) int-type)
        (check '(proc ((x int)) 0)))
  (test '(proc-type (int-type) int-type)
         (check '(let ((f = (proc ((x int)) (- x (- 0 1)))))
                  in (proc ((y int)) (- (f y) 4)))))
  (test '(proc-type (int-type) bool-type)
        (check '(proc ((x int)) (zero? x))))
  (test '(proc-type ((proc-type (int-type) int-type))
                    (proc-type (int-type) bool-type))
        (check '(proc ((f (-> (int) int)))
                  (proc ((x int))
                    (zero? (f x))))))
  (test '(proc-type (int-type) int-type)
        (check '(letrec ((int f ((x int)) = x)) in f)))
  (test 'bool-type
        (check '(letrec ((bool g ((x int)) = (zero? (- x 1))))
                 in (g 10))))
  (test 'int-type
        (check '((proc ((x int))
                   ((proc ((y int)) (- x y)) (- x 2)))
                 4)))
  (test 'int-type
        (check '(let ((x = 10) (y = 11)) in (- y x))))
  (test 'int-type
        (check '(let ((b = true) (x = 4)) in (if b x 0))))

  (test #t (rejected? '(- (zero? 3) 2)))
  (test #t (rejected? '(- 3 (proc ((x int)) x))))
  (test #t (rejected? '(zero? (zero? 0))))
  (test #t (rejected? '(if 3 1 0)))
  (test #t (rejected? '(if (zero? 3) (zero? 1) 4)))
  (test #t (rejected? '(if (zero? 0) 3 ((proc ((x int)) (zero? x)) 4))))
  (test #t (rejected? '(let ((x = 4)) in (if x 0 1))))
  (test #t (rejected? '((proc ((f (-> (int) int))) (f 10))
                        (proc ((x int)) (zero? x)))))
  (test #t (rejected? '(letrec ((int f ((x bool)) = (f (f x)))) in 4)))
  (test #t (rejected? '(4 4)))
  (test #t (rejected? '(((proc ((x int)) x) 10) 3)))
  (test #t (rejected? '(let ((b = false) (x = 5)) in (if x b true))))
  )
