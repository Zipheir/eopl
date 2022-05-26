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

;; check-all-same : Non-empty-list-of(Type) x Exp -> ()
(define (check-all-same types orig-exp)
  (pmatch types
    ((,ty1 . ,tys)
     (for-each (lambda (t) (check-equal-type ty1 t orig-exp))
               tys))))

;; type-to-external-form : Type -> List
(define (type-to-external-form ty)
  (pmatch ty
    (int-type 'int)
    (bool-type 'bool)
    (void-type 'void)
    ((pair-type ,type1 ,type2)
     `(pair-of ,(type-to-external-form type1)
               ,(type-to-external-form type2)))
    ((proc-type ,arg-types ,res-type)
     `(,(map type-to-external-form arg-types)
       ->
       ,(type-to-external-form res-type)))
    ((list-type ,type)
     `(list-of ,(type-to-external-form type)))))

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
    ((emptylist-exp ,type) (list 'list-type type))
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
    ((set-exp ,var ,exp1)
     (let ((ty (type-of exp1 tenv)))
       (check-equal-type ty (apply-tenv tenv var) exp)
       'void-type))
    ((begin-exp ,exps) (type-of-begin-exp exps tenv))
    ((pair-exp ,exp1 ,exp2)
     (let ((ty1 (type-of exp1 tenv))
           (ty2 (type-of exp2 tenv)))
       (list 'pair-type ty1 ty2)))
    ((unpack-exp ,var1 ,var2 ,exp1 ,body)
     (pmatch (type-of exp1 tenv)
       ((pair-type ,ty1 ,ty2)
        (type-of body
                 (extend-tenv* (list var1 var2)
                               (list ty1 ty2)
                               tenv)))
       (,type (raise (make-type-cond '(pair * *) type exp1)))))
    ((list-exp ,exps)  ; exps is guaranteed non-empty
     (let* ((types (map (lambda (e) (type-of e tenv)) exps)))
       (check-all-same types exp)
       (list 'list-type (car types))))
    ((cons-exp ,exp1 ,exp2)
     (let ((ty1 (type-of exp1 tenv))
           (ty2 (type-of exp2 tenv)))
       (check-equal-type `(list-type ,ty1) ty2 exp)
       ty2))
    ((null?-exp ,exp1)
     (pmatch (type-of exp1 tenv)
       ((list-type ?) 'bool-type)
       (,type (raise (make-type-cond '(list-type *) type exp1)))))
    ((car-exp ,exp1)
     (pmatch (type-of exp1 tenv)
       ((list-type ,t) t)
       (,type (raise (make-type-cond '(list-type *) type exp1)))))
    ((cdr-exp ,exp1)
     (pmatch (type-of exp1 tenv)
       ((list-type ,t) `(list-type ,t))
       (,type (raise (make-type-cond '(list-type *) type exp1)))))
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

;; type-of-begin-exp : List-of(Exp) x Tenv -> Type
(define (type-of-begin-exp exps tenv)
  (let loop ((es exps))
    (pmatch es
      ((,e) (type-of e tenv))  ; tail call
      ((,e . ,es*)
       (type-of e tenv)        ; check type, but discard the result
       (loop es*)))))

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
    ((set ,v ,e) (guard (symbol? v))
     `(set-exp ,v ,(parse e)))
    ((begin . ,es) (guard (pair? es))
     `(begin-exp ,(map parse es)))
    ((pair ,e1 ,e2) `(pair-exp ,(parse e1) ,(parse e2)))
    ((unpack ,v1 ,v2 = ,e in ,b)
     (guard (symbol? v1) (symbol? v2))
     (list 'unpack-exp v1 v2 (parse e) (parse b)))
    ((emptylist of ,t) `(emptylist-exp ,(parse-type t)))
    ((cons ,a ,d) `(cons-exp ,(parse a) ,(parse d)))
    ((car ,e) `(car-exp ,(parse e)))
    ((cdr ,e) `(cdr-exp ,(parse e)))
    ((null? ,e) `(null?-exp ,(parse e)))
    ((list . ,es) (guard (pair? es))  ; need a type, so no empties
     `(list-exp ,(map parse es)))
    ((,e1 . ,es) `(call-exp ,(parse e1) ,(map parse es)))
    (? (error 'parse "syntax error" sexp))))

;; parse-type : S-exp -> Type
(define (parse-type sexp)
  (pmatch sexp
    (int 'int-type)
    (bool 'bool-type)
    (void 'void-type)
    ((-> ,arg-ts ,res-t) (guard (pair? arg-ts))
     `(proc-type ,(map parse-type arg-ts) ,(parse-type res-t)))
    ((pair-of ,t1 ,t2)
     `(pair-type ,(parse-type t1) ,(parse-type t2)))
    ((list-of ,texp) `(list-type ,(parse-type texp)))
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
  (test 'int-type (check '(begin 1 2 3)))
  (test 'bool-type (check '(begin true 2 false)))
  (test 'void-type
        (check '(let ((x = 10)) in (set x 11))))
  (test 'bool-type
        (check '(let ((b = false)) in (begin (set b true) b))))

  ;; Pairs
  (test '(pair-type int-type int-type) (check '(pair 1 2)))
  (test '(pair-type int-type bool-type) (check '(pair 1 (zero? 2))))
  (test '(pair-type bool-type int-type)
        (check '(let ((x = 5))
                 in (if (zero? x) (pair true x) (pair false x)))))
  (test '(pair-type (pair-type bool-type bool-type)
                    (pair-type int-type int-type))
        (check '(pair (pair true false) (pair 2 3))))

  ;; Unpack
  (test 'int-type (check '(unpack x y = (pair 1 2) in (- x y))))
  (test 'bool-type
        (check '(unpack p q = (pair (pair 1 true) (pair false 2))
                 in (unpack x b = p in (zero? x)))))

  ;; Lists
  (test '(list-type int-type) (check '(emptylist of int)))
  (test '(list-type (list-type int-type))
        (check '(emptylist of (list-of int))))
  (test '(list-type bool-type) (check '(list true)))
  (test '(list-type bool-type) (check '(cons true (emptylist of bool))))
  (test '(list-type int-type)
        (check '(cons 1 (cons 2 (cons (if (zero? 1) 0 3)
                                      (emptylist of int))))))
  (test '(list-type int-type) (check '(list 1 2 3)))
  (test 'bool-type (check '(null? (emptylist of bool))))
  (test '(list-type int-type)
        (check '(list (- 4 2) (- 8 3) ((proc ((x int)) x) 10))))
  (test 'int-type (check '(car (emptylist of int))))
  (test '(list-type int-type) (check '(cdr (list 1 2))))
  (test 'bool-type
        (check '(null? (cdr (cons (car (list 4 3))
                                  (cdr (list 5 6)))))))
  (test 'int-type
        (check
         '(letrec ((int add ((x int) (y int)) =
                     (- x (- 0 y)))
                  (int sum ((ns (list-of int))) =
                     (if (null? ns)
                         0
                         (add (car ns) (sum (cdr ns))))))
           in (sum (list 1 2 3 4 5)))))
  (test #t (rejected? '(cons 2 (emptylist of bool))))
  (test #t (rejected? '(cons true (cons false (emptylist of int)))))
  (test #t (rejected? '(list 1 true 3)))
  (test #t (rejected? '(list (if (zero? 1) (- 4 2) 0) true false)))
  (test #t (rejected? '(null? 4)))
  (test #t (rejected? '(null? (cons true (emptylist of int)))))
  (test #t (rejected? '(car 4)))
  (test #t (rejected? '(cdr 4)))
  (test #t (rejected? '(cons (car (list 2 3)) (cdr (list true)))))

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
  (test #t (rejected? '(let ((b = false)) in (set b 10))))
  (test #t (rejected? '(let ((b = false))
                        in (let ((v = (set b true)))
                            in (- v 4)))))
  (test #t (rejected? '(if true (pair 1 true) (pair true 1))))
  (test #t (rejected? '(unpack a b = 4 in a)))
  (test #t (rejected? '(unpack x y = (pair 2 3) in (if x y 0))))
  )
