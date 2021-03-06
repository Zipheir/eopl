;;;; PROC → Nameless compiler from section 3.7, and nameless
;;;; interpreter.

(import (rnrs records syntactic (6))
        (rnrs lists (6)))

(include "pmatch.scm")

(define (pair-or-null? x) (or (pair? x) (null? x)))

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

;;; PROC-only expressions

(define-record-type var-exp
  (fields var))

(define-record-type let-exp
  (fields var exp1 body))

(define-record-type proc-exp
  (fields var body))

(define (PROC-expression? obj)
  (or (const-exp? obj)
      (diff-exp? obj)
      (zero?-exp? obj)
      (if-exp? obj)
      (var-exp? obj)
      (let-exp? obj)
      (proc-exp? obj)
      (call-exp? obj)))

;;; Expressed values

(define-record-type num-val
  (fields num))

(define-record-type bool-val
  (fields bool))

(define-record-type proc-val
  (fields proc))

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

(define (nameless-expression? obj)
  (or (const-exp? obj)
      (diff-exp? obj)
      (zero?-exp? obj)
      (if-exp? obj)
      (nameless-var-exp? obj)
      (nameless-let-exp? obj)
      (nameless-proc-exp? obj)
      (call-exp? obj)))

;;; Static environments

;; Senv     = List-of(Sym)
;; Lex-addr = ℕ

;; empty-senv : () → Senv
(define (empty-env) '())

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

;;;; Compiler

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
    (,v (guard (symbol? v)) (make-var-exp v))
    ((let ,v = ,s in ,b) (make-let-exp v (parse s) (parse b)))
    ((proc (,v) ,body) (guard (symbol? v))
     (make-proc-exp v (parse body)))
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
        ((nameless-let-exp? exp)
         `(let ,(unparse (nameless-let-exp-exp1 exp))
           in ,(unparse (nameless-let-exp-body exp))))
        ((nameless-proc-exp? exp)
         `(proc ,(unparse (nameless-proc-exp-body exp))))
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
        ((call-exp? exp)
         (let ((proc (expval->proc (value-of (call-exp-rator exp) env)))
               (arg (value-of (call-exp-rand exp) env)))
           (apply-procedure proc arg)))
        ((nameless-var-exp? exp)
         (apply-nameless-env env (nameless-var-exp-index exp)))
        ((nameless-let-exp? exp)
         (let ((val (value-of (nameless-let-exp-exp1 exp) env)))
           (value-of (nameless-let-exp-body exp)
                     (extend-nameless-env val env))))
        ((nameless-proc-exp? exp)
         (make-proc-val (make-proc (nameless-proc-exp-body exp) env)))
        (else (error 'value-of "invalid expression type" exp))))

;; value-of-program : Nameless-program → Exp-val
(define (value-of-program pgm)
  (value-of (program-exp1 pgm) (init-nameless-env)))
