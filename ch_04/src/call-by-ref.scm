;;;; CALL-BY-REFERENCE language from Ch. 4, with extensions from
;;;; the exercises.
;;;;
;;;; Ex. 4.32: Multi-argument procedures.
;;;; Ex. 4.33: Call-by-value procedures (valprocs).
;;;; Ex. 4.34: letref

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

;; alloc-array : Nat x Exp-val -> Ref
(define (alloc-array len val)
  (let ((next-ref (length the-store))
        (store* (append the-store (make-list len val))))
    (set! the-store store*)
    next-ref))

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

;; expval->array : Exp-val -> Arr
(define (expval->array val)
  (pmatch val
    ((array-val ,a) a)
    (? (report-expval-extractor-error 'array val))))

;; expval->proc+is-ref : Exp-val -> Proc x Bool
(define (expval->proc+is-ref val)
  (pmatch val
    ((refproc-val ,proc) (cons proc #t))
    ((valproc-val ,proc) (cons proc #f))
    (? (report-expval-extractor-error 'proc val))))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

;; the-unspecified-value : Exp-val
(define the-unspecified-value '(num-val 27))

;;;; Arrays

;; make-array : Nat x Exp-val -> Arr
(define (make-array len val)
  `(array ,(alloc-array len val) ,len))

;; array-ref : Arr x Nat -> Ref
;; Note that this just returns the location.
(define (array-ref arr k)
  (pmatch arr
    ((array ,base ,len)
     (if (< k len)
         (+ base k)
         (report-bounds-error k)))))

;; array-set! : Arr x Nat x Exp-val -> Unspecified
(define (array-set! arr k val)
  (pmatch arr
    ((array ,base ,len)
     (if (< k len)
         (setref! (+ base k) val)
         (report-bounds-error k)))))

;; report-bounds-error : Nat -> ()
(define (report-bounds-error k)
  (error 'array-ref "array index out of bounds" k))

;;;; Procedures

(define (procedure b-vars body saved-env)
  (list 'proc b-vars body saved-env))

;; apply-procedure : Proc x List-of(Ref) -> Exp-val
(define (apply-procedure proc1 vals)
  (pmatch proc1
    ((proc ,vars ,body ,env)
     (value-of body (extend-env vars vals env)))))

;;;; Environments

;; empty-env : () -> Env
(define (empty-env) '())

;; extend-env : List-of(Var) x List-of(Exp-val) x Env -> Env
(define (extend-env vars vals env)
  (cons (list 'ext vars vals) env))

;; extend-env1 : Var x Exp-val x Env -> Env
(define (extend-env1 var val env)
  (extend-env (list var) (list val) env))

;; extend-env-rec : List-of(Var) x List-of(Var) x List-of(Exp-val)
;;                  x Env -> Env
(define (extend-env-rec p-names b-vars p-bodies env)
  (cons (list 'ext-rec p-names b-vars p-bodies) env))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (pmatch env
    (() (report-no-binding-found search-var))
    (((ext ,vars ,vals) . ,env*)
     (cond ((location search-var vars) =>
            (lambda (n) (list-ref vals n)))
           (else (apply-env env* search-var))))
    (((ext-rec ,p-names ,b-vars ,p-bodies) . ,env*)
     (cond ((location search-var p-names) =>
            (lambda (n)
              (newref
               (list 'refproc-val
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
  (extend-env (map car as) (map cdr as) (empty-env)))

;;; Initial environment

;; init-env : () -> Env
(define (init-env)
  (alist->env `((i . ,(newref '(num-val 1)))
                (v . ,(newref '(num-val 5)))
                (x . ,(newref '(num-val 10))))))

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
    ((var-exp ,var) (deref (apply-env env var)))
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
     (let ((val (value-of exp1 env)))
       (value-of body
                 (extend-env1 var (newref val) env))))
    ((refproc-exp ,vars ,body)
     `(refproc-val ,(procedure vars body env)))
    ((valproc-exp ,vars ,body)
     `(valproc-val ,(procedure vars body env)))
    ((call-exp ,rator ,rands)
     (pmatch (expval->proc+is-ref (value-of rator env))
       ((,proc . ,is-refproc)
        (let ((args
               ((if is-refproc
                    value-of-ref-operands
                    value-of-val-operands)
                rands
                env)))
          (apply-procedure proc args)))))
    ((letrec-exp ,p-names ,b-vars ,p-bodies ,letrec-body)
     (value-of letrec-body
               (extend-env-rec p-names b-vars p-bodies env)))
    ((assign-exp ,var ,e)
     (setref! (apply-env env var) (value-of e env))
     the-unspecified-value)
    ((begin-exp ,es) (value-of-sequence es env))
    ((letref-exp ,var ,exp1 ,body)
     (let ((val (value-of-ref-operand exp1 env)))
       (value-of body (extend-env1 var val env))))
    ((newarray-exp ,le ,exp1)
     (let ((len (expval->num (value-of le env)))
           (val (value-of exp1 env)))
       `(array-val ,(make-array len val))))
    ((arrayref-exp ,arr ,addr)
     (let ((array1 (expval->array (value-of arr env)))
           (k (expval->num (value-of addr env))))
       (deref (array-ref array1 k))))
    ((arrayset-exp ,arr ,addr ,exp1)
     (let ((array1 (expval->array (value-of arr env)))
           (k (expval->num (value-of addr env)))
           (val (value-of exp1 env)))
       (array-set! array1 k val)
       the-unspecified-value))
    (? (error 'value-of "invalid expression" exp))))

;; value-of-ref-operand : Exp x Env -> Ref
(define (value-of-ref-operand exp env)
  (pmatch exp
    ((var-exp ,var) (apply-env env var))
    ((arrayref-exp ,arr ,addr)
     (let ((array1 (expval->array (value-of arr env)))
           (k (expval->num (value-of addr env))))
       (array-ref array1 k)))
    (? (newref (value-of exp env)))))

;; value-of-ref-operands : List-of(Exp) x Env -> List-of(Ref)
(define (value-of-ref-operands exps env)
  (map (lambda (e) (value-of-ref-operand e env)) exps))

;; value-of-val-operands : List-of(Exp) x Env -> List-of(Ref)
(define (value-of-val-operands exps env)
  (map (lambda (e) (newref (value-of e env))) exps))

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
    ((refproc ,vs ,body)
     (guard (pair? vs) (for-all symbol? vs))
     `(refproc-exp ,vs ,(parse body)))
    ((valproc ,vs ,body)
     (guard (pair? vs) (for-all symbol? vs))
     `(valproc-exp ,vs ,(parse body)))
    ((letrec ,bs in ,body) (parse-letrec bs body))
    ((set ,v ,ve) (guard (symbol? v))
     `(assign-exp ,v ,(parse ve)))
    ((begin . ,es) `(begin-exp ,(map parse es)))
    ((letref ,v = ,e in ,body) (guard (symbol? v))
     `(letref-exp ,v ,(parse e) ,(parse body)))
    ((newarray ,le ,ve) `(newarray-exp ,(parse le) ,(parse ve)))
    ((arrayref ,a ,k) `(arrayref-exp ,(parse a) ,(parse k)))
    ((arrayset ,a ,k ,e)
     `(arrayset-exp ,(parse a) ,(parse k) ,(parse e)))
    ((,et . ,ens) `(call-exp ,(parse et) ,(map parse ens)))
    (? (error 'parse "invalid syntax" sexp))))

;; parse-letrec : List x List -> Exp
(define (parse-letrec binds body)
  (letrec
    ((collect
      (lambda (bs names var-lists bodies)
        (pmatch bs
          (() (values names var-lists bodies))
          (((,name ,vs = ,body) . ,bs*)
           (guard (symbol? name) (for-all symbol? vs))
           (collect bs*
                    (cons name names)
                    (cons vs var-lists)
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
           '(let add1 = (refproc (a) (- a (- 0 1))) in (add1 v))))
  (test 5 (eval-to-num
           '(let add1 = (refproc (b) (- b (- 0 1))) in
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

  ;; Call-by-reference

  (test 5 (eval-to-num
           '(let f = (refproc (x) (set x 5)) in
              (let a = 3 in
                (begin (f a) a)))))
  (test 44 (eval-to-num
            '(let f = (refproc (x) (set x 44)) in
               (let g = (refproc (y) (f y)) in
                 (let z = 55 in
                   (begin (g z) z))))))
  (test 11 (eval-to-num
            '(let swap = (refproc (x) (refproc (y)
                           (let temp = x in
                             (begin (set x y) (set y temp)))))
               in (let a = 33 in
                    (let b = 44 in
                      (begin ((swap a) b) (- a b)))))))
  (test 44 (eval-to-num
            '(letrec ((f (x) = (set x 44))
                      (g (y) = (f y))) in
               (let z = 55 in
                 (begin (g z) z)))))

  (test 5 (eval-to-num
           '(letref a = 3 in
              (letref b = a in
                (begin (set a 5) b)))))
  (test 5 (eval-to-num
           '(letref a = 3 in
              (letref b = a in
                (begin (set b 5) a)))))

  ;; Call-by-value

  (test 5 (eval-to-num
           '(let a = 5 in
              (let f = (valproc (x) (set x 3)) in
                (begin (f a) a)))))

  ;; Call-by-ref. arrays

  (test 5 (eval-to-num '(let a = (newarray 4 5) in (arrayref a 0))))
  (test 3 (eval-to-num
           '(let a = (newarray 4 5) in
              (begin (arrayset a 2 3) (arrayref a 2)))))
  (test 3 (eval-to-num
           '(let a = (newarray 4 5) in
              (let f = (refproc (x) (set x 3)) in
                (begin (f (arrayref a 0)) (arrayref a 0))))))
  (test 3 (eval-to-num
           '(let a = (newarray 4 5) in
              (let swap = (refproc (x) (refproc (y)
                            (let temp = x in
                              (begin (set x y)
                                     (set y temp)))))
              in (begin (arrayset a 3 3)
                        ((swap (arrayref a 0)) (arrayref a 3))
                        (arrayref a 0))))))
  )
