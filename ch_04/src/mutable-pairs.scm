;;;; MUTABLE-PAIRS language from Ch. 4 with extensions from
;;;; the exercises.

(import (rnrs lists (6))
        ; (srfi srfi-11)   ; guile, shouldn't be necessary.
        (rnrs records syntactic (6)))

(include "pmatch.scm")
(include "../../src/test.scm")

;;;; Utility

;; make-list : Nat x Scheme-val -> List
(define (make-list len x)
  (assert (and (integer? len) (not (negative? len))))
  (letrec
    ((build
      (lambda (k)
        (if (zero? k)
            '()
            (cons x (build (- k 1)))))))

    (build len)))

;;;; Stores

;; Contains the current state of the store.
(define the-store 'uninitialized)

;; empty-store : () -> Sto
(define (empty-store) '())

;; initialize-store! : () -> Unspecified
(define (initialize-store!)
  (set! the-store (empty-store)))

;; reference? : Scheme-val -> Bool
(define (reference? x)
  (integer? x))

;; newref : Exp-val -> Ref
(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val)))
    next-ref))

;; alloc-array : Nat x Exp-val -> Ref
(define (alloc-array n val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (make-list n val)))
    next-ref))

;; deref : Ref -> Exp-val
(define (deref ref)
  (list-ref the-store ref))

;; setref! : Ref x Exp-val -> Unspecified
(define (setref! ref val)
  (letrec
    ((setref-inner
      (lambda (store1 ref1)
        (cond ((null? store1)
               (report-invalid-reference ref the-store))
              ((zero? ref1) (cons val (cdr store1)))
              (else (cons (car store1)
                          (setref-inner (cdr store1)
                                        (- ref1 1))))))))
    (set! the-store (setref-inner the-store ref))))

(define (report-invalid-reference ref store)
  (error 'setref! "invalid reference" ref store))

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
  (fields p-names b-vars p-bodies letrec-body))

(define-record-type assign-exp
  (fields var exp1))

(define-record-type empty-list-exp)

(define-record-type newpair-exp
  (fields exp1 exp2))

(define-record-type left-exp
  (fields exp1))

(define-record-type right-exp
  (fields exp1))

(define-record-type setleft-exp
  (fields exp1 exp2))

(define-record-type setright-exp
  (fields exp1 exp2))

(define-record-type newarray-exp
  (fields len exp1))

(define-record-type arrayref-exp
  (fields arr addr))

(define-record-type arrayset-exp
  (fields arr addr exp1))

;;;; Expressed values

(define-record-type num-val
  (fields num))

(define-record-type bool-val
  (fields bool))

(define-record-type proc-val
  (fields proc))

(define-record-type empty-list-val)

(define-record-type mutpair-val
  (fields pair))

(define-record-type array-val
  (fields arr))

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

;; expval->proc : Exp-val -> Proc
(define (expval->proc val)
  (if (proc-val? val)
      (proc-val-proc val)
      (report-expval-extractor-error 'proc val)))

;; expval->mutpair : Exp-val -> Mut-pair
(define (expval->mutpair val)
  (if (mutpair-val? val)
      (mutpair-val-pair val)
      (report-expval-extractor-error 'mutpair val)))

;; expval->array : Exp-val -> Arr
(define (expval->array val)
  (if (array-val? val)
      (array-val-arr val)
      (report-expval-extractor-error 'array val)))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;; the-unspecified-value : Exp-val
(define the-unspecified-value (make-num-val 27))

;;;; Mutable pairs

(define-record-type (mut-pair a-pair mut-pair?)
  (fields val1 val2))

;; make-pair : Exp-val x Exp-val -> Mut-pair
(define (make-pair val1 val2)
  (a-pair (newref val1) (newref val2)))

;; left : Mut-pair -> Exp-val
(define (left p)
  (deref (mut-pair-val1 p)))

;; right : Mut-pair -> Exp-val
(define (right p)
  (deref (mut-pair-val2 p)))

;; setleft : Mut-pair x Exp-val -> Unspecified
(define (setleft p val)
  (setref! (mut-pair-val1 p) val))

;; setright : Mut-pair x Exp-val -> Unspecified
(define (setright p val)
  (setref! (mut-pair-val2 p) val))

;;;; Arrays

(define-record-type (array make-raw-array array?)
  (fields base length))

;; make-array : Nat x Exp-val -> Arr
(define (make-array len val)
  (make-raw-array (alloc-array len val) len))

;; array-ref : Arr x Nat -> Exp-val
(define (array-ref arr k)
  (let ((len (array-length arr)))
    (if (< k len)
        (deref (+ (array-base arr) k))
        (report-bounds-error k))))

;; set-array! : Arr x Nat x Exp-val -> Unspecified
(define (set-array! arr k val)
  (let ((len (array-length arr)))
    (if (< k len)
        (setref! (+ (array-base arr) k) val)
        (report-bounds-error k))))

;; report-bounds-error : Nat -> ()
(define (report-bounds-error k)
  (error 'array-ref "array index out of bounds" k))

;;;; Procedures

(define-record-type proc
  (fields var body saved-env))

(define procedure make-proc)

;; apply-procedure : Proc x Exp-val -> Exp-val
(define (apply-procedure proc1 val)
  (value-of (proc-body proc1)
            (extend-env (proc-var proc1)
                        (newref val)
                        (proc-saved-env proc1))))

;;;; Environments

(define-record-type (empty-environment empty-env empty-env?))

(define-record-type (extended-env extend-env extended-env?)
  (fields var val rest-env))

(define-record-type (extended-env-rec extend-env-rec extended-env-rec?)
  (fields p-names b-vars p-bodies env))

(define (environment? obj)
  (or (empty-env? obj)
      (extended-env? obj)
      (extended-env-rec? obj)))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (cond ((empty-env? env) (report-no-binding-found search-var))
        ((extended-env? env)
         (if (eqv? search-var (extended-env-var env))
             (extended-env-val env)
             (apply-env (extended-env-rest-env env) search-var)))
        ((extended-env-rec? env)
         (let ((b-vars (extended-env-rec-b-vars env))
               (p-bodies (extended-env-rec-p-bodies env)))
           (cond ((location search-var
                            (extended-env-rec-p-names env)) =>
                  (lambda (n)
                    (newref
                      (make-proc-val (procedure (list-ref b-vars n)
                                                (list-ref p-bodies n)
                                                env)))))
                 (else
                  (apply-env (extended-env-rec-env env) search-var)))))
        (else (error 'apply-env "invalid environment" env))))

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
  (fold-right (lambda (p env)
                (extend-env (car p) (newref (cdr p)) env))
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

;; value-of-program : Program -> Exp-val
(define (value-of-program pgm)
  (initialize-store!)
  (value-of (program-exp1 pgm) (init-env)))

;; value-of : Exp x Env -> Exp-val
(define (value-of exp env)
  (cond ((const-exp? exp) (make-num-val (const-exp-num exp)))
        ((var-exp? exp) (deref (apply-env env (var-exp-var exp))))
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
        ((let-exp? exp)
         (let ((val (value-of (let-exp-exp1 exp) env)))
           (value-of (let-exp-body exp)
                     (extend-env (let-exp-var exp)
                                 (newref val)
                                 env))))
        ((proc-exp? exp)
         (make-proc-val (procedure (proc-exp-var exp)
                                   (proc-exp-body exp)
                                   env)))
        ((call-exp? exp)
         (let ((proc (expval->proc (value-of (call-exp-rator exp) env)))
               (arg (value-of (call-exp-rand exp) env)))
           (apply-procedure proc arg)))
        ((letrec-exp? exp)
         (value-of (letrec-exp-letrec-body exp)
                   (extend-env-rec (letrec-exp-p-names exp)
                                   (letrec-exp-b-vars exp)
                                   (letrec-exp-p-bodies exp)
                                   env)))
        ((assign-exp? exp)
         (setref! (apply-env env (assign-exp-var exp))
                  (value-of (assign-exp-exp1 exp) env))
         the-unspecified-value)
        ((empty-list-exp? exp) (make-empty-list-val))
        ((newpair-exp? exp)
         (let ((val1 (value-of (newpair-exp-exp1 exp) env))
               (val2 (value-of (newpair-exp-exp2 exp) env)))
           (make-mutpair-val (make-pair val1 val2))))
        ((left-exp? exp)
         (let ((val1 (value-of (left-exp-exp1 exp) env)))
           (left (expval->mutpair val1))))
        ((right-exp? exp)
         (let ((val1 (value-of (right-exp-exp1 exp) env)))
           (right (expval->mutpair val1))))
        ((setleft-exp? exp)
         (let ((val1 (value-of (setleft-exp-exp1 exp) env))
               (val2 (value-of (setleft-exp-exp2 exp) env)))
           (begin
            (setleft (expval->mutpair val1) val2)
            the-unspecified-value)))
        ((setright-exp? exp)
         (let ((val1 (value-of (setright-exp-exp1 exp) env))
               (val2 (value-of (setright-exp-exp2 exp) env)))
           (begin
            (setright (expval->mutpair val1) val2)
            the-unspecified-value)))
        ((newarray-exp? exp)
         (let ((vlen (value-of (newarray-exp-len exp) env))
               (val (value-of (newarray-exp-exp1 exp) env)))
           (make-array-val (make-array (expval->num vlen) val))))
        ((arrayref-exp? exp)
         (let ((varr (value-of (arrayref-exp-arr exp) env))
               (vk (value-of (arrayref-exp-addr exp) env)))
           (array-ref (expval->array varr) (expval->num vk))))
        ((arrayset-exp? exp)
         (let ((varr (value-of (arrayset-exp-arr exp) env))
               (vk (value-of (arrayset-exp-addr exp) env))
               (val (value-of (arrayset-exp-exp1 exp) env)))
           (set-array! (expval->array varr) (expval->num vk) val)
           the-unspecified-value))
        (else (error 'value-of "invalid expression" exp))))

;; Parser for a simple S-exp representation.
;; parse : List -> Exp
(define (parse sexp)
  (pmatch sexp
    (emptylist (make-empty-list-exp))
    (,n (guard (number? n)) (make-const-exp n))
    ((- ,s ,t) (make-diff-exp (parse s) (parse t)))
    ((zero? ,s) (make-zero?-exp (parse s)))
    ((if ,t ,c ,a) (make-if-exp (parse t) (parse c) (parse a)))
    (,v (guard (symbol? v)) (make-var-exp v))
    ((let ,v = ,s in ,b) (guard (symbol? v))
     (make-let-exp v (parse s) (parse b)))
    ((proc (,v) ,body) (guard (symbol? v))
     (make-proc-exp v (parse body)))
    ((letrec ,bs in ,body) (parse-letrec bs body))
    ((set ,v ,ve) (guard (symbol? v))
     (make-assign-exp v (parse ve)))
    ((: ,a ,d) (make-newpair-exp (parse a) (parse d)))
    ((left ,e) (make-left-exp (parse e)))
    ((right ,e) (make-right-exp (parse e)))
    ((setl ,e1 ,e2) (make-setleft-exp (parse e1) (parse e2)))
    ((setr ,e1 ,e2) (make-setright-exp (parse e1) (parse e2)))
    ((newarray ,l ,e) (make-newarray-exp (parse l) (parse e)))
    ((arrayref ,a ,k) (make-arrayref-exp (parse a) (parse k)))
    ((arrayset ,a ,k ,e)
     (make-arrayset-exp (parse a) (parse k) (parse e)))
    ((,e1 ,e2) (make-call-exp (parse e1) (parse e2)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-letrec : List x List -> Exp
(define (parse-letrec binds body)
  (letrec
    ((collect
      (lambda (bs names vars bodies)
        (pmatch bs
          (() (values names vars bodies))
          (((,name (,var) = ,body) . ,bs*)
           (guard (symbol? name) (symbol? var))
           (collect bs*
                    (cons name names)
                    (cons var vars)
                    (cons (parse body) bodies)))))))

    (let-values (((names vars bodies) (collect binds '() '() '())))
      (make-letrec-exp names vars bodies (parse body)))))

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
              (letrec ((f (a) = (if (zero? a) 0 (add1 (f (- a 1))))))
               in (f 5)))))
  (test 0 (eval-to-num
           '(letrec ((even (k) = (if (zero? k) 1 (odd (- k 1))))
                     (odd  (k) = (if (zero? k) 0 (even (- k 1)))))
             in (- (even 4) (odd 3)))))

  (test 5 (eval-to-num '(let y = 0 in (let dum = (set y 5) in y))))
  (test 0 (eval-to-num
           '(let x = 0 in
              (letrec ((even (dum) = (if (zero? x)
                                         1
                                         (let dum = (set x (- x 1)) in
                                           (odd 4))))
                       (odd (dum) = (if (zero? x)
                                        0
                                        (let dum = (set x (- x 1)) in
                                          (even 4)))))
               in (let dum = (set x 5) in
                    (even 888))))))
  )
