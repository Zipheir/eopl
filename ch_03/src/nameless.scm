;;;; PROC → Nameless compiler from section 3.7, and nameless
;;;; interpreter, extended with lists.

(import (rnrs records syntactic (6))
        (rnrs lists (6)))

(include "pmatch.scm")

(define (pair-or-null? x) (or (pair? x) (null? x)))

;; on-pair : (a → b) → ((a × a) → (b × b))
(define (on-pair f)
  (lambda (p)
    (cons (f (car p)) (f (cdr p)))))

(define-record-type program
  (fields exp1))

;;; Expressions (PROC and nameless)

(define-record-type const-exp
  (fields num))

(define-record-type diff-exp
  (fields exp1 exp2))

(define-record-type zero?-exp
  (fields exp1))

(define-record-type if-exp
  (fields exp1 exp2 exp3))

(define-record-type call-exp
  (fields rator rand))

(define-record-type cond-exp
  (fields clauses))

;; Lists

(define-record-type empty-list-exp)

(define-record-type cons-exp
  (fields exp1 exp2))

(define-record-type car-exp
  (fields exp1))

(define-record-type cdr-exp
  (fields exp1))

(define-record-type null?-exp
  (fields exp1))

(define-record-type list-exp
  (fields exps))

;;; PROC-only expressions

(define-record-type var-exp
  (fields var))

(define-record-type let-exp
  (fields var exp1 body))

(define-record-type proc-exp
  (fields var body))

(define-record-type unpack-exp
  (fields vars exp1 body))

(define (PROC-expression? obj)
  (or (const-exp? obj)
      (diff-exp? obj)
      (zero?-exp? obj)
      (if-exp? obj)
      (var-exp? obj)
      (let-exp? obj)
      (proc-exp? obj)
      (call-exp? obj)
      (cond-exp? obj)
      (unpack-exp? obj)
      (empty-list-exp? obj)
      (cons-exp? obj)
      (car-exp? obj)
      (cdr-exp? obj)
      (null?-exp? obj)
      (list-exp? obj)))

;;; Expressed values

(define-record-type num-val
  (fields num))

(define-record-type bool-val
  (fields bool))

(define-record-type proc-val
  (fields proc))

(define-record-type list-val
  (fields list))

(define (expval? obj)
  (or (num-val? obj) (bool-val? obj) (proc-val? obj)))

;; expval->num : Exp-val → Int
(define (expval->num val)
  (if (num-val? val)
      (num-val-num val)
      (report-expval-extractor-error 'num val)))

;; expval->bool : Exp-val → Bool
(define (expval->bool val)
  (if (bool-val? val)
      (bool-val-bool val)
      (report-expval-extractor-error 'bool val)))

;; expval->proc : Exp-val → Proc
(define (expval->proc val)
  (if (proc-val? val)
      (proc-val-proc val)
      (report-expval-extractor-error 'proc val)))

;; expval->list : Exp-val → List
(define (expval->list val)
  (if (list-val? val)
      (list-val-list val)
      (report-expval-extractor-error 'list val)))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;;; Nameless expressions

;; A var-exp in nameless is the lexical address of a
;; corresponding declaration.
(define-record-type nameless-var-exp
  (fields index))

(define-record-type nameless-let-exp
  (fields exp1 body))

(define-record-type nameless-proc-exp
  (fields body))

(define-record-type nameless-unpack-exp
  (fields exp1 body))

(define (nameless-expression? obj)
  (or (const-exp? obj)
      (diff-exp? obj)
      (zero?-exp? obj)
      (if-exp? obj)
      (nameless-var-exp? obj)
      (nameless-let-exp? obj)
      (nameless-proc-exp? obj)
      (nameless-unpack-exp? obj)
      (call-exp? obj)
      (cond-exp? obj)
      (cons-exp? obj)
      (car-exp? obj)
      (cdr-exp? obj)
      (null?-exp? obj)
      (list-exp? obj)))

;;; Static environments

;; Senv     = List-of(Sym)
;; Lex-addr = ℕ

;; empty-senv : () → Senv
(define (empty-senv) '())

;; extend-senv : Var × Senv → Senv
(define (extend-senv var senv) (cons var senv))

;; apply-senv : Senv × Var → Lex-addr
(define (apply-senv senv var)
  (cond ((null? senv) (error 'apply-env "unbound variable" var))
        ((eqv? var (car senv)) 0)
        (else (+ 1 (apply-senv (cdr senv) var)))))

;; Another cheap conversion!
;; list->senv : List-of(Sym) → Senv
(define (list->senv ss)
  (assert (pair-or-null? ss))
  (assert (for-all symbol? ss))
  ss)

;; The initial environment from PROC, staticized.
;; init-senv : () → Senv
(define (init-senv) (list->senv '(i v x)))

;; extend-senv-from-list : List-of(Var) × Senv → Senv
(define (extend-senv-from-list ss senv)
  (senv-append (list->senv ss) senv))

;; senv-append : Senv × Senv → Senv
(define (senv-append senv1 senv2)
  (append senv1 senv2))

;;; Compiler

;; translation-of : PROC-exp × Senv → Nameless-exp
(define (translation-of exp senv)
  (assert (PROC-expression? exp))
  (cond ((const-exp? exp) exp)
        ((var-exp? exp)
         (make-nameless-var-exp (apply-senv senv (var-exp-var exp))))
        ((diff-exp? exp)
         (make-diff-exp (translation-of (diff-exp-exp1 exp) senv)
                        (translation-of (diff-exp-exp2 exp) senv)))
        ((zero?-exp? exp)
         (make-zero?-exp (translation-of (zero?-exp-exp1 exp) senv)))
        ((if-exp? exp)
         (make-if-exp (translation-of (if-exp-exp1 exp) senv)
                      (translation-of (if-exp-exp2 exp) senv)
                      (translation-of (if-exp-exp3 exp) senv)))
        ((let-exp? exp)
         (make-nameless-let-exp
          (translation-of (let-exp-exp1 exp) senv)
          (translation-of (let-exp-body exp)
                          (extend-senv (let-exp-var exp) senv))))
        ((proc-exp? exp)
         (make-nameless-proc-exp
          (translation-of (proc-exp-body exp)
                          (extend-senv (proc-exp-var exp) senv))))
        ((call-exp? exp)
         (make-call-exp (translation-of (call-exp-rator exp) senv)
                        (translation-of (call-exp-rand exp) senv)))
        ((cond-exp? exp)
         (make-cond-exp (map (on-pair (lambda (e)
                                        (translation-of e senv)))
                             (cond-exp-clauses exp))))
        ((unpack-exp? exp)
         (make-nameless-unpack-exp
          (translation-of (unpack-exp-exp1 exp) senv)
          (translation-of (unpack-exp-body exp)
                          (extend-senv-from-list (unpack-exp-vars exp)
                                                 senv))))
        ;; Lists
        ((empty-list-exp? exp) exp)
        ((cons-exp? exp)
         (make-cons-exp (translation-of (cons-exp-exp1 exp) senv)
                        (translation-of (cons-exp-exp2 exp) senv)))
        ((car-exp? exp)
         (make-car-exp (translation-of (car-exp-exp1 exp) senv)))
        ((cdr-exp? exp)
         (make-cdr-exp (translation-of (cdr-exp-exp1 exp) senv)))
        ((null?-exp? exp)
         (make-null?-exp (translation-of (null?-exp-exp1 exp) senv)))
        ((list-exp? exp)
         (make-list-exp (map (lambda (e) (translation-of e senv))
                             (list-exp-exps exp))))
        (else (error 'translation-of "unknown expression type" exp))))

;; translation-of-program : Program → Nameless-program
(define (translation-of-program pgm)
  (make-program
   (translation-of (program-exp1 pgm) (init-senv))))

;;;; (Un)parsing

;;; PROC parser from proc-base.scm

;; Parser for a simple S-exp representation.
;; parse : List → Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) (make-const-exp n))
    ;; A slightly nicer syntax for diff-exps in an S-exp context.
    ((- ,s ,t) (make-diff-exp (parse s) (parse t)))
    ((zero? ,s) (make-zero?-exp (parse s)))
    ((if ,t ,c ,a) (make-if-exp (parse t) (parse c) (parse a)))
    (emptylist (make-empty-list-exp))
    (,v (guard (symbol? v)) (make-var-exp v))
    ((let ,v = ,s in ,b) (make-let-exp v (parse s) (parse b)))
    ((proc (,v) ,body) (guard (symbol? v))
     (make-proc-exp v (parse body)))
    ((cond . ,cs) (make-cond-exp (map (on-pair parse) cs)))
    ((unpack ,vs = ,e in ,b)
     (guard (pair-or-null? vs) (for-all symbol? vs))
     (make-unpack-exp vs (parse e) (parse b)))
    ((cons ,e1 ,e2) (make-cons-exp (parse e1) (parse e2)))
    ((car ,e) (make-car-exp (parse e)))
    ((cdr ,e) (make-cdr-exp (parse e)))
    ((null? ,e) (make-null?-exp (parse e)))
    ((list . ,es) (make-list-exp (map parse es)))
    ((,e1 ,e2) (make-call-exp (parse e1) (parse e2)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-program : List → Program
(define (parse-program sexp)
  (make-program (parse sexp)))

;;; Nameless unparser

;; unparse : Nameless-exp → List
(define (unparse exp)
  (cond ((const-exp? exp) (const-exp-num exp))
        ((nameless-var-exp? exp)
         (lex-addr->symbol (nameless-var-exp-index exp)))
        ((diff-exp? exp)
         `(- ,(unparse (diff-exp-exp1 exp))
             ,(unparse (diff-exp-exp2 exp))))
        ((zero?-exp? exp) `(zero? ,(unparse (zero?-exp-exp1 exp))))
        ((if-exp? exp)
         `(if ,(unparse (if-exp-exp1 exp))
              ,(unparse (if-exp-exp2 exp))
              ,(unparse (if-exp-exp3 exp))))
        ((cond-exp? exp)
         `(cond ,@(map (on-pair unparse) (cond-exp-clauses exp))))
        ((nameless-let-exp? exp)
         `(let ,(unparse (nameless-let-exp-exp1 exp))
           in ,(unparse (nameless-let-exp-body exp))))
        ((nameless-proc-exp? exp)
         `(proc ,(unparse (nameless-proc-exp-body exp))))
        ((nameless-unpack-exp? exp)
         `(unpack ,(unparse (nameless-unpack-exp-exp1 exp))
           in ,(unparse (nameless-unpack-exp-body exp))))
        ((empty-list-exp? exp) 'emptylist)
        ((cons-exp? exp)
         `(cons ,(unparse (cons-exp-exp1 exp))
                ,(unparse (cons-exp-exp2 exp))))
        ((car-exp? exp) `(car ,(unparse (car-exp-exp1 exp))))
        ((cdr-exp? exp) `(cdr ,(unparse (cdr-exp-exp1 exp))))
        ((null?-exp? exp) `(null? ,(unparse (null?-exp-exp1 exp))))
        ((list-exp? exp) `(list ,@(map unparse (list-exp-exps exp))))
        ((call-exp? exp)
         (list (unparse (call-exp-rator exp))
               (unparse (call-exp-rand exp))))
        (else (error 'unparse "unknown expression type" exp))))

;; The book uses #k, but that's datum syntax, so I use $k instead.
(define (lex-addr->symbol k)
  (string->symbol (string-append "$" (number->string k))))

;; unparse-program : Nameless-program → List
(define (unparse-program pgm)
  (unparse (program-exp1 pgm)))

;;;; Interpreter

;;; Nameless environments

;; nameless-environment? : Scheme-val → Bool
(define (nameless-environment? x)
  (and (pair-or-null? x)
       (for-all expval? x)))

;; empty-nameless-env : () → Nameless-env
(define (empty-nameless-env) '())

;; extend-nameless-env : Expval × Nameless-env → Nameless-env
(define (extend-nameless-env val env)
  (cons val env))

;; apply-nameless-env : Nameless-env × Lexaddr → Nameless-env
(define (apply-nameless-env env n)
  (list-ref env n))

;; init-nameless-env : () → Nameless-env
(define (init-nameless-env) (map make-num-val '(1 5 10)))

;; extend-nameless-env-from-list :
;;   List-of(Expval) × Nameless-env → Nameless-env
(define (extend-nameless-env-from-list vals env)
  (append vals env))

;;; (Nameless) procedures

(define-record-type proc
  (fields body saved-nameless-env))

;; apply-procedure : Proc × Exp-val → Exp-val
(define (apply-procedure proc1 val)
  (value-of (proc-body proc1)
            (extend-nameless-env val
                                 (proc-saved-nameless-env proc1))))

;; value-of : Nameless-exp × Nameless-env → Exp-val
(define (value-of exp env)
  (cond ((const-exp? exp) (make-num-val (const-exp-num exp)))
        ((diff-exp? exp)
         (let ((val1 (value-of (diff-exp-exp1 exp) env))
               (val2 (value-of (diff-exp-exp2 exp) env)))
           (let ((num1 (expval->num val1))
                 (num2 (expval->num val2)))
             (make-num-val (- num1 num2)))))
        ((zero?-exp? exp)
         (let ((val (value-of (zero?-exp-exp1 exp) env)))
           (if (zero? (expval->num val))
               (make-bool-val #t)
               (make-bool-val #f))))
        ((if-exp? exp)
         (let ((test-val (value-of (if-exp-exp1 exp) env)))
           (if (expval->bool test-val)
               (value-of (if-exp-exp2 exp) env)
               (value-of (if-exp-exp3 exp) env))))
        ((cond-exp? exp) (value-of-clauses (cond-exp-clauses exp) env))
        ((call-exp? exp)
         (let ((proc (expval->proc (value-of (call-exp-rator exp) env)))
               (arg (value-of (call-exp-rand exp) env)))
           (apply-procedure proc arg)))
        ((empty-list-exp? exp) (make-list-val '()))
        ((cons-exp? exp)
         (let ((car-val (value-of (cons-exp-exp1 exp) env))
               (cdr-val (value-of (cons-exp-exp2 exp) env)))
           (make-list-val (cons car-val (expval->list cdr-val)))))
        ((car-exp? exp)
         (let* ((val (value-of (car-exp-exp1 exp) env))
                (xs (expval->list val)))
           (if (null? xs)
               (error 'value-of "car: empty list" exp)
               (car xs))))
        ((cdr-exp? exp)
         (let* ((val (value-of (cdr-exp-exp1 exp) env))
                (xs (expval->list val)))
           (if (null? xs)
               (error 'value-of "car: empty list" exp)
               (make-list-val (cdr xs)))))
        ((null?-exp? exp)
         (let ((xs (expval->list (value-of (null?-exp-exp1 exp) env))))
           (if (null? xs)
               (make-bool-val #t)
               (make-bool-val #f))))
        ((list-exp? exp)
         (make-list-val (map (lambda (e) (value-of e env))
                             (list-exp-exps exp))))
        ((nameless-var-exp? exp)
         (apply-nameless-env env (nameless-var-exp-index exp)))
        ((nameless-let-exp? exp)
         (let ((val (value-of (nameless-let-exp-exp1 exp) env)))
           (value-of (nameless-let-exp-body exp)
                     (extend-nameless-env val env))))
        ((nameless-proc-exp? exp)
         (make-proc-val (make-proc (nameless-proc-exp-body exp) env)))
        ((nameless-unpack-exp? exp)
         (let ((lis (expval->list
                     (value-of (nameless-unpack-exp-exp1 exp) env))))
           (value-of (nameless-unpack-exp-body exp)
                     (extend-nameless-env-from-list lis env))))
        (else (error 'value-of "invalid expression type" exp))))

;; value-of-clauses : List-of(Exp × Exp) × Nameless-env → Exp-val
(define (value-of-clauses cs env)
  (pmatch cs
    (() (error 'value-of "cond: out of clauses"))
    (((,texp . ,cexp) . ,cs*)
     (if (expval->bool (value-of texp env))
         (value-of cexp env)
         (value-of-clauses cs* env)))))

;; value-of-program : Nameless-program → Exp-val
(define (value-of-program pgm)
  (value-of (program-exp1 pgm) (init-nameless-env)))
