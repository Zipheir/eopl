;;;; Store-passing version of the EXPLICIT-REFS language.

(import (rnrs lists (6))
        (rnrs records syntactic (6)))

(include "pmatch.scm")
(include "../../src/test.scm")

;;;; Stores

;; empty-store : () -> Sto
(define (empty-store) '())

;; reference? : Scheme-val -> Bool
(define (reference? x)
  (integer? x))

;; newref : Exp-val x Sto -> Ref x Sto
(define (newref val store)
  (let ((next-ref (length store)))
    (list next-ref (append store (list val)))))

;; deref : Ref x Sto -> Exp-val
(define (deref ref store)
  (list-ref store ref))

;; setref : Ref x Exp-val x Sto -> Sto
(define (setref ref val store)
  (letrec
    ((replace
      (lambda (store1 ref1)
        (cond ((null? store1)
               (report-invalid-reference ref store))
              ((zero? ref1) (cons val (cdr store1)))
              (else (cons (car store1)
                          (replace (cdr store1) (- ref1 1))))))))
    (replace store ref)))

;; report-invalid-reference : Ref x Sto -> ()
(define (report-invalid-reference ref store)
  (error 'setref "invalid reference" ref store))

;;;; Expressions

(define-record-type const-exp
  (fields num))

(define-record-type diff-exp
  (fields exp1 exp2))

(define-record-type zero?-exp
  (fields exp1))

(define-record-type if-exp
  (fields exp1 exp2 exp3))

(define-record-type var-exp
  (fields var))

(define-record-type let-exp
  (fields var exp1 body))

(define-record-type proc-exp
  (fields var body))

(define-record-type call-exp
  (fields rator rand))

(define-record-type letrec-exp
  (fields p-name b-var p-body letrec-body))

(define-record-type newref-exp
  (fields exp1))

(define-record-type deref-exp
  (fields exp1))

(define-record-type setref-exp
  (fields exp1 exp2))

(define-record-type begin-exp
  (fields exps))

;;;; Expressed values

(define-record-type ref-val
  (fields loc))

(define-record-type num-val
  (fields num))

(define-record-type bool-val
  (fields bool))

(define-record-type proc-val
  (fields proc))

;; expval->num : Exp-val -> Int
(define (expval->num val)
  (if (num-val? val)
      (num-val-num val)
      (report-expval-extractor-error 'num val)))

;; expval->bool : Exp-val -> Bool
(define (expval->bool val)
  (if (bool-val? val)
      (bool-val-bool val)
      (report-expval-extractor-error 'bool val)))

;; expval->loc : Exp-val -> Ref
(define (expval->ref val)
  (if (ref-val? val)
      (ref-val-loc val)
      (report-expval-extractor-error 'ref val)))

;; expval->proc : Exp-val → Proc
(define (expval->proc val)
  (if (proc-val? val)
      (proc-val-proc val)
      (report-expval-extractor-error 'proc val)))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;;;; Procedures

(define-record-type proc
  (fields var body saved-env))

(define procedure make-proc)

;; apply-procedure : Proc x Exp-val x Sto -> Answer
(define (apply-procedure proc1 val sto)
  (value-of (proc-body proc1)
            (extend-env (proc-var proc1) val (proc-saved-env proc1))
            sto))

;;;; Environments

(define-record-type (empty-environment empty-env empty-env?))

(define-record-type (extended-env extend-env extended-env?)
  (fields var val rest-env))

(define-record-type (extended-env-rec extend-env-rec extended-env-rec?)
  (fields p-name b-var p-body env))

(define (environment? obj)
  (or (empty-env? obj)
      (extended-env? obj)
      (extended-env-rec? obj)))

;; apply-env : Env × Var → Scheme-val
(define (apply-env env search-var)
  (cond ((empty-env? env) (report-no-binding-found search-var))
        ((extended-env? env)
         (if (eqv? search-var (extended-env-var env))
             (extended-env-val env)
             (apply-env (extended-env-rest-env env) search-var)))
        ((extended-env-rec? env)
         (if (eqv? search-var (extended-env-rec-p-name env))
             (make-proc-val (procedure (extended-env-rec-b-var env)
                                       (extended-env-rec-p-body env)
                                       env))
             (apply-env (extended-env-rec-env env) search-var)))
        (else (error 'apply-env "invalid environment" env))))

(define (report-no-binding-found var)
  (error 'apply-env "no binding found" var))

;; alist->env : List-of(Var × Scheme-val) → Env
;; No recursive bindings.
(define (alist->env as)
  (fold-right (lambda (p env) (extend-env (car p) (cdr p) env))
              (empty-env)
              as))

;;; Initial environment

;; init-env : () -> Env
(define (init-env)
  (alist->env `((i . ,(make-num-val 1))
                (v . ,(make-num-val 5))
                (x . ,(make-num-val 10)))))

;;;; Programs

(define-record-type program
  (fields exp1))

;;;; Main interpreter

;;; Answer = Exp-val x Sto

(define the-unspecified-value (make-num-val 23))

;; value-of-program : Program -> Exp-val
(define (value-of-program pgm)
  (car (value-of (program-exp1 pgm) (init-env) (empty-store))))

;; value-of : Exp x Env x Sto -> Answer
(define (value-of exp env sto)
  (cond ((const-exp? exp)
         (list (make-num-val (const-exp-num exp)) sto))
        ((var-exp? exp) (list (apply-env env (var-exp-var exp)) sto))
        ((diff-exp? exp) (value-of-diff-exp exp env sto))
        ((zero?-exp? exp) (value-of-zero?-exp exp env sto))
        ((if-exp? exp) (value-of-if-exp exp env sto))
        ((let-exp? exp) (value-of-let-exp exp env sto))
        ((letrec-exp? exp)
         (value-of (letrec-exp-letrec-body exp)
                   (extend-env-rec (letrec-exp-p-name exp)
                                   (letrec-exp-b-var exp)
                                   (letrec-exp-p-body exp)
                                   env)
                   sto))
        ((proc-exp? exp)
         (list (make-proc-val
                (procedure (proc-exp-var exp) (proc-exp-body exp)))
               sto))
        ((call-exp? exp) (value-of-call-exp exp env sto))
        ((newref-exp? exp) (value-of-newref-exp exp env sto))
        ((deref-exp? exp) (value-of-deref-exp exp env sto))
        ((setref-exp? exp) (value-of-setref-exp exp env sto))
        ((begin-exp? exp) (value-of-begin-exp exp env sto))
        (else (error 'value-of "invalid expression" exp))))

;; value-of-diff-exp : Exp x Env x Sto -> Answer
(define (value-of-diff-exp exp env sto0)
  (pmatch (value-of (diff-exp-exp1 exp) env sto0)
    ((,val1 ,sto1)
     (pmatch (value-of (diff-exp-exp2 exp) env sto1)
       ((,val2 ,sto2)
        (list (make-num-val (- (expval->num val1) (expval->num val2)))
              sto2))))))

;; value-of-zero?-exp : Exp x Env x Sto -> Answer
(define (value-of-zero?-exp exp env sto0)
  (pmatch (value-of (zero?-exp-exp1 exp) env sto0)
    ((,val ,sto1)
     (list (make-bool-val (zero? (expval->num val))) sto1))))

;; value-of-if-exp : Exp x Env x Sto -> Answer
(define (value-of-if-exp exp env sto0)
  (pmatch (value-of (if-exp-exp1 exp) env sto0)
    ((,val1 ,sto1)
     (if (expval->bool val1)
         (value-of (if-exp-exp2 exp) env sto1)
         (value-of (if-exp-exp3 exp) env sto1)))))

;; value-of-let-exp : Exp x Env x Sto -> Answer
(define (value-of-let-exp exp env sto0)
  (pmatch (value-of (let-exp-exp1 exp) env sto0)
    ((,val ,sto1)
     (value-of (let-exp-body exp)
               (extend-env (let-exp-var exp) val env)
               sto1))))

;; value-of-call-exp : Exp x Env x Sto -> Answer
(define (value-of-call-exp exp env sto0)
  (pmatch (value-of (call-exp-rator exp) env sto0)
    ((,vrat ,sto1)
     (pmatch (value-of (call-exp-rand exp) env sto1)
       ((,vrand ,sto2)
        (apply-procedure (expval->proc vrat) vrand sto2))))))

;; value-of-newref-exp : Exp x Env x Sto -> Answer
(define (value-of-newref-exp exp env sto0)
  (pmatch (value-of (newref-exp-exp1 exp) env sto0)
    ((,val ,sto1)
     (pmatch (newref val sto1)
       ((,ref ,sto2) (list (make-ref-val ref) sto2))))))


;; value-of-deref-exp : Exp x Env x Sto -> Answer
(define (value-of-deref-exp exp env sto0)
  (pmatch (value-of (deref-exp-exp1 exp) env sto0)
    ((,val ,sto1)
     (list (deref (expval->ref val) sto1) sto1))))

;; value-of-setref-exp : Exp x Env x Sto -> Answer
(define (value-of-setref-exp exp env sto0)
  (pmatch (value-of (setref-exp-exp1 exp) env sto0)
    ((,lval ,sto1)
     (pmatch (value-of (setref-exp-exp2 exp) env sto1)
       ((,val ,sto2)
        (list (make-num-val 23)
              (setref (expval->ref lval) val sto2)))))))

;; value-of-begin-exp : Exp x Env x Sto -> Answer
;; This is fun.
(define (value-of-begin-exp exp env sto0)
  (fold-left (lambda (ans e) (value-of e env (cadr ans)))
             (list the-unspecified-value sto0)
             (begin-exp-exps exp)))

;; Parser for a simple S-exp representation.
;; parse : List -> Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) (make-const-exp n))
    ((- ,s ,t) (make-diff-exp (parse s) (parse t)))
    ((zero? ,s) (make-zero?-exp (parse s)))
    ((if ,t ,c ,a) (make-if-exp (parse t) (parse c) (parse a)))
    (,v (guard (symbol? v)) (make-var-exp v))
    ((let ,v = ,s in ,b) (guard (symbol? v))
     (make-let-exp v (parse s) (parse b)))
    ((proc (,v) ,body) (guard (symbol? v))
     (make-proc-exp v (parse body)))
    ((letrec ,name (,v) = ,p-body in ,body)
     (guard (symbol? name) (symbol? v))
     (make-letrec-exp name v (parse p-body) (parse body)))
    ((newref ,e) (make-newref-exp (parse e)))
    ((deref ,e) (make-deref-exp (parse e)))
    ((setref ,re ,ve) (make-setref-exp (parse re) (parse ve)))
    ((begin . ,es) (make-begin-exp (map parse es)))
    ((,e1 ,e2) (make-call-exp (parse e1) (parse e2)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-program : List -> Program
(define (parse-program sexp)
  (make-program (parse sexp)))

;;;; Convenience drivers

;; run : Bool x List -> Exp-val
(define (run sexp)
  (value-of-program (parse-program sexp)))

;;;; Tests

(define (eval-to-num sexp)
  (expval->num (run sexp)))

(define (run-tests)
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
              (letrec f (a) = (if (zero? a) 0 (add1 (f (- a 1)))) in
                (f 5)))))

  (test 1 (eval-to-num '(let pn = (newref 1) in (deref pn))))
  (test 1 (eval-to-num
           '(let pn = (newref (newref 1)) in (deref (deref pn)))))
  (test 3 (eval-to-num
           '(let pn = (newref 0) in
              (let dummy = (setref pn 3) in
                (deref pn)))))
  (test 4 (eval-to-num
           '(let pn = (newref 3) in
              (let dummy = (setref pn (- (deref pn) (- 0 1))) in
                (deref pn)))))

  ;; begin (ex. 4.4)
  (test 3 (eval-to-num '(begin 1 2 3)))
  (test 3 (eval-to-num
           '(let a = (newref 0) in (begin (setref a 3) (deref a)))))
  (test 5 (eval-to-num '(begin (let v = 7 in (begin)) v)))
  (test 4 (eval-to-num
           '(let g = (let c = (newref 0)
                      in (proc (dum)
                           (begin
                            (setref c (- (deref c) (- 0 1)))
                            (deref c))))
             ;in (begin (g 0) (g 0) (g 0) (g 0)))))
             in (g 0))))
  )
