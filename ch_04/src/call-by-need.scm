;;;; CALL-BY-NEED language from Ch. 4.

(import (rnrs base (6))
        (rnrs lists (6))
        (rnrs records syntactic (6)))

(include "pmatch.scm")
(include "../../src/test.scm")

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

;; deref : Ref -> Exp-val
(define (deref ref)
  (list-ref the-store ref))

;; setref! : Ref x Exp-val -> Unspecified
(define (setref! ref val)
  (letrec
    ((setref-inner
      (lambda (store1 ref1)
        (pmatch store1
          (() (report-invalid-reference ref the-store))
          ((,v . ,store*)
           (if (zero? ref1)
               (cons val store*)
               (cons v (setref-inner store* (- ref1 1)))))))))

    (set! the-store (setref-inner the-store ref))))

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

;; the-unspecified-value : Exp-val
(define the-unspecified-value '(num-val 27))

;;;; Procedures

(define (procedure b-var body saved-env)
  (list 'proc b-var body saved-env))

;; apply-procedure : Proc x Ref -> Exp-val
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

;; extend-env-rec : List-of(Var) x List-of(Var) x List-of(Exp-val)
;;                  x Env -> Env
(define (extend-env-rec p-names b-vars p-bodies env)
  (cons (list 'ext-rec p-names b-vars p-bodies) env))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (pmatch env
    (() (report-no-binding-found search-var))
    (((ext ,var ,val) . ,env*)
     (if (eqv? search-var var) val (apply-env env* search-var)))
    (((ext-rec ,p-names ,b-vars ,p-bodies) . ,env*)
     (cond ((location search-var p-names) =>
            (lambda (n)
              (newref
               (list 'proc-val
                     (procedure (list-ref b-vars n)
                                (list-ref p-bodies n)
                                env)))))
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
  (fold-right (lambda (p env)
                (extend-env (car p) (newref (cdr p)) env))
              (empty-env)
              as))

;;; Initial environment

;; init-env : () -> Env
(define (init-env)
  (alist->env `((i . (num-val 1))
                (v . (num-val 5))
                (x . (num-val 10)))))

;;;; Main interpreter

;; value-of-program : Program -> Exp-val
(define (value-of-program pgm)
  (pmatch pgm
    ((program ,exp)
     (initialize-store!)
     (value-of exp (init-env)))
    (? (error 'value-of-program "invalid program" pgm))))

;; value-of : Exp x Env -> Exp-val
(define (value-of exp env)
  (pmatch exp
    ((const-exp ,n) `(num-val ,n))
    ((var-exp ,var) (value-of-variable var env))
    ((diff-exp ,e1 ,e2)
     (let ((val1 (value-of e1 env))
           (val2 (value-of e2 env)))
       (let ((num1 (expval->num val1))
             (num2 (expval->num val2)))
         `(num-val ,(- num1 num2)))))
    ((zero?-exp ,e)
     (let ((val (value-of e env)))
       (if (zero? (expval->num val))
           '(bool-val #t)
           '(bool-val #f))))
    ((if-exp ,test ,con ,alt)
     (let ((test-val (value-of test env)))
       (if (expval->bool test-val)
           (value-of con env)
           (value-of alt env))))
    ((let-exp ,var ,exp1 ,body)
     (let ((val (value-of-operand exp1 env)))
       (value-of body (extend-env var val env))))
    ((proc-exp ,var ,body)
     `(proc-val ,(procedure var body env)))
    ((call-exp ,rator ,rand)
     (let ((proc (expval->proc (value-of rator env)))
           (arg (value-of-operand rand env)))
       (apply-procedure proc arg)))
    ((letrec-exp ,p-names ,b-vars ,p-bodies ,letrec-body)
     (value-of letrec-body
               (extend-env-rec p-names b-vars p-bodies env)))
    ((assign-exp ,var ,e)
     (setref! (apply-env env var) (value-of e env))
     the-unspecified-value)
    ((begin-exp ,es) (value-of-sequence es env))
    (? (error 'value-of "invalid expression" exp))))

;; value-of-variable : Var x Env -> Exp-val
(define (value-of-variable var env)
  (let* ((ref1 (apply-env env var))
         (w (deref ref1)))
    (pmatch w
      ((thunk ,exp1 ,senv)
       (let ((val1 (value-of exp1 senv)))
         (setref! ref1 val1)   ; memoize
         val1))
      (? w))))

;; value-of-operand : Exp x Env -> Ref
(define (value-of-operand exp env)
  (pmatch exp
    ((const-exp ,n) (newref `(num-val ,n)))
    ((proc-exp ,var ,body)
     (newref `(proc-val ,(procedure var body env))))
    ((var-exp ,var) (apply-env env var))
    (? (newref `(thunk ,exp ,env)))))

;; value-of-sequence : List-of(Exp) -> Exp-val
(define (value-of-sequence exps env)
  (letrec
    ((sequence
      (lambda (es)
        (pmatch es
          (() the-unspecified-value)
          ((,e) (value-of e env))
          ((,e . ,es*)
           (value-of e env)
           (sequence es*))))))

    (sequence exps)))

;; Parser for a simple S-exp representation.
;; parse : List -> Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) `(const-exp ,n))
    ((- ,s ,t) `(diff-exp ,(parse s) ,(parse t)))
    ((zero? ,s) `(zero?-exp ,(parse s)))
    ((if ,t ,c ,a) `(if-exp ,(parse t) ,(parse c) ,(parse a)))
    (,v (guard (symbol? v)) `(var-exp ,v))
    ((let ,v = ,s in ,b) (guard (symbol? v))
     `(let-exp ,v ,(parse s) ,(parse b)))
    ((proc (,v) ,body) (guard (symbol? v))
     `(proc-exp ,v ,(parse body)))
    ((letrec ,bs in ,body) (parse-letrec bs body))
    ((set ,v ,ve) (guard (symbol? v))
     `(assign-exp ,v ,(parse ve)))
    ((begin . ,es) `(begin-exp ,(map parse es)))
    ((,e1 ,e2) `(call-exp ,(parse e1) ,(parse e2)))
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
      (list 'letrec-exp names vars bodies (parse body)))))

;; parse-program : List -> Program
(define (parse-program sexp)
  (list 'program (parse sexp)))

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
  )
