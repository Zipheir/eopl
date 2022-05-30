;;;; INFERRED language from Ch. ,4 (2nd ed.)
;;;; This is rather different from the 3rd edition typed language
;;;; implementations.

(import (rnrs base (6))
        (rnrs exceptions (6))
        (rnrs records syntactic (6))
        (rename (rnrs lists (6)) (for-all every)))

(include "../../../src/pmatch.scm")
(include "../../../src/test.scm")

;;; Utility

(define (unzip ps)
  (pmatch ps
    (() '(() ()))
    (((,a . ,b) . ,ps*)
     (pmatch (unzip ps*)
       ((,as ,bs)
        (list (cons a as) (cons b bs)))))))

(define (natural? x)
  (and (integer? x) (not (negative? x))))

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

(define (atomic-type? t)
  (symbol? t))

(define (expand-optional-type-expression otexp)
  (pmatch otexp
    (no-type-exp (fresh-tvar))
    ((a-type-exp ,texp) (expand-type-expression texp))
    (? (error 'expand-optional-type-expression
              "invalid expression"
              otexp))))

(define (expand-type-expression texp)
  (pmatch texp
    (int-type-exp 'int-type)
    (bool-type-exp 'bool-type)
    ((proc-type-exp ,arg-texps ,res-texp)
     (list 'proc-type
           (map expand-type-expression arg-texps)
           (expand-type-expression res-texp)))))

(define fresh-tvar
  (let ((serial-number 0))
    (lambda ()
      (set! serial-number (+ serial-number 1))
      `(tvar-type ,serial-number ,(vector '())))))

(define (tvar-type? t)
  (pmatch t
    ((tvar-type ? ?) #t)
    (else #f)))

(define (tvar-contents ty)
  (pmatch ty
    ((tvar-type ? ,box) (vector-ref box 0))))

(define (tvar-set-contents! ty val)
  (pmatch ty
    ((tvar-type ? ,box) (vector-set! box 0 val))))

(define (tvar-non-empty? ty)
  (pmatch ty
    ((tvar-type ? ,box)
     (not (null? (vector-ref box 0))))))

(define (type-to-external-form ty)
  (pmatch ty
    (int-type 'int)
    (bool-type 'bool)
    ((proc-type ,arg-types ,res-type)
     `(-> ,@(map type-to-external-form arg-types)
          ,(type-to-external-form res-type)))
    ((tvar-type ,serial ?)
     (if (tvar-non-empty? ty)
         (type-to-external-form (tvar-contents ty))
         (string->symbol
          (string-append "tvar" (number->string serial)))))
    (? (error 'type-to-external-form "invalid type" ty))))

;;; Type error condition

(define-record-type (&type-cond make-type-cond type-cond?)
  (parent &condition)
  (fields
   (immutable type1 type-cond-type1)
   (immutable type2 type-cond-type2)
   (immutable expression type-cond-expression)))

(define (raise-type-error t1 t2 exp)
  (raise (make-type-cond t1 t2 exp)))

;;; Inference

(define (type-of exp tenv)
  (display "type-of: ")
  (display exp)
  (newline)
  (pmatch exp
    (true-exp 'bool-type)
    (false-exp 'bool-type)
    ((lit-exp ?) 'int-type)
    ((var-exp ,var) (apply-tenv tenv var))
    ((if-exp ,test-exp ,true-exp ,false-exp)
     (let ((true-type (type-of true-exp tenv)))
       (check-equal-types! (type-of test-exp tenv) 'bool-type test-exp)
       (check-equal-types! (type-of false-exp tenv) true-type exp)
       true-type))
    ((proc-exp ,texps ,ids ,body)
     (type-of-proc-exp texps ids body tenv))
    ((primapp-exp ,prim ,rands)
     (type-of-application (type-of-primitive prim)
                          (types-of-exps rands tenv)
                          prim
                          rands
                          exp))
    ((app-exp ,rator ,rands)
     (type-of-application (type-of rator tenv)
                          (types-of-exps rands tenv)
                          rator
                          rands
                          exp))
    ((let-exp ,ids ,rands ,body) (type-of-let-exp ids rands body tenv))
    ((letrec-exp . ,rest)
     (apply type-of-letrec-exp (append rest (list tenv))))
    (? (error 'type-of "invalid expression" exp))))

(define (types-of-exps exps tenv)
  (map (lambda (e) (type-of e tenv)) exps))

(define (type-of-proc-exp texps ids body tenv)
  (let* ((arg-types (map (lambda (texp)
                           (expand-optional-type-expression texp))
                         texps))
         (res-type (type-of body (extend-tenv* ids arg-types tenv))))
    `(proc-type ,arg-types ,res-type)))

(define (type-of-application rator-type actual-types rator rands exp)
  (let ((res-type (fresh-tvar)))
    (check-equal-types! rator-type   ; unify, filling in res-type
                        `(proc-type ,actual-types ,res-type)
                        exp)
    res-type))

(define (type-of-primitive prim)
  (case prim
    ((add-prim sub-prim mul-prim div-prim mod-prim)
     '(proc-type (int-type int-type) int-type))
    ((zero?-prim) '(proc-type (int-type) bool-type))
    (else (error 'type-of-primitive "unknown primitive" prim))))

(define (type-of-let-exp ids rands body tenv)
  (let ((body-tenv (extend-tenv* ids (types-of-exps rands tenv) tenv)))
    (type-of body body-tenv)))

(define (type-of-letrec-exp res-texps p-names texpss idss p-bodies
                            lr-body tenv)
  (let* ((arg-typess
          (map (lambda (texps)
                 (map expand-optional-type-expression texps))
               texpss))
         (res-types (map expand-optional-type-expression res-texps))
         (proc-types
          (map (lambda (ats rt) `(proc-type ,ats ,rt))
               arg-typess
               res-types))
         (body-tenv (extend-tenv* p-names proc-types tenv)))
    (for-each
     (lambda (ids arg-types p-body res-type)
       (check-equal-types!
        (type-of p-body (extend-tenv* ids arg-types body-tenv))
        res-type
        p-body))
     idss arg-typess p-bodies res-types)
    (type-of lr-body body-tenv)))

(define (check-equal-types! t1 t2 exp)
  (cond ((eqv? t1 t2))
        ((tvar-type? t1) (check-tvar-equal-type! t1 t2 exp))
        ((tvar-type? t2) (check-tvar-equal-type! t2 t1 exp))
        ((and (atomic-type? t1) (atomic-type? t2))
         (unless (eqv? (atomic-type->name t1) (atomic-type->name t2))
           (raise-type-error t1 t2 exp)))
        (else
         (pmatch (list t1 t2)
           (((proc-type ,arg-types1 ,res-type1)
             (proc-type ,arg-types2 ,res-type2))
            (unless (= (length arg-types1) (length arg-types2))
              (raise-arity-error t1 t2 exp))
            (for-each (lambda (at1 at2)
                        (check-equal-types! at1 at2 exp))
                      arg-types1
                      arg-types2)
            (check-equal-types! res-type1 res-type2 exp))
           (? (raise-type-error t1 t2 exp))))))

(define (check-tvar-equal-type! tvar ty exp)
  (if (tvar-non-empty? tvar)
      (check-equal-types! (tvar-contents tvar) ty exp)
      (begin
       (check-no-occurrence! tvar ty exp)
       (tvar-set-contents! tvar ty))))

(define (check-no-occurrence! tvar ty exp)
  (letrec
   ((check
     (lambda (ty1)
       (pmatch ty1
         (,t (guard (atomic-type? t)) #t)
         ((proc-type ,arg-types ,res-type)
          (for-each check arg-types)
          (check res-type))
         ((tvar-type ? ?)
          (if (tvar-non-empty? ty1)
              (check (tvar-contents ty1))
              (if (eqv? tvar ty1)
                  (error 'check-no-occurrence!
                         "occurrence check failed" tvar ty1 exp))))))))

    (check ty)))

(define (raise-arity-error t1 t2 exp)
  (error 'check-equal-types! "too few/many arguments" t1 t2 exp))

;; Main entry point.
(define (infer-type exp)
  (type-of exp (init-tenv)))

;;; Parser

;; parse : S-exp -> Exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (natural? n)) `(lit-exp ,n))
    (true 'true-exp)
    (false 'false-exp)
    (,v (guard (symbol? v)) `(var-exp ,v))
    ((zero? ,e) `(primapp-exp zero?-prim ,(list (parse e))))
    ((+ ,e1 ,e2)
     `(primapp-exp add-prim ,(list (parse e1) (parse e2))))
    ((- ,e1 ,e2)
     `(primapp-exp sub-prim ,(list (parse e1) (parse e2))))
    ((* ,e1 ,e2)
     `(primapp-exp mul-prim ,(list (parse e1) (parse e2))))
    ((if ,e1 ,e2 ,e3)
     `(if-exp ,(parse e1) ,(parse e2) ,(parse e3)))
    ((let ,binds in ,b) (parse-let-exp binds b))
    ((proc ,args ,e) (parse-proc-exp args e))
    ((letrec ,binds in ,b) (parse-letrec-exp binds b))
    ((,e1 . ,es) `(app-exp ,(parse e1) ,(map parse es)))
    (? (error 'parse "syntax error" sexp))))

(define (parse-optional-type-syntax sexp)
  (if (eqv? sexp '?)
      'no-type-exp
      (list 'a-type-exp (parse-type-syntax sexp))))

(define (parse-type-syntax sexp)
  (pmatch sexp
    (int 'int-type-exp)
    (bool 'bool-type-exp)
    ((-> ,ats ,rt)
     `(proc-type-exp ,(map parse-optional-type-syntax ats)
                     ,(parse-optional-type-syntax rt)))
    (? (error 'parse-type-syntax "invalid type expression" sexp))))

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
                     (cons (parse-optional-type-syntax rt) res-ts)
                     (cons nm p-names)
                     (cons ts texpss)
                     (cons ids idss)
                     (cons (parse body) bodies))))))))

    (let-values (((res-ts p-names texpss idss bodies)
                  (collect binds '() '() '() '() '())))
      (list 'letrec-exp res-ts p-names texpss idss bodies
            (parse lr-body)))))

;; parse-args : List -> (List-of(Sym) x List-of(Type))
(define (parse-args args+types)
  (pmatch (unzip args+types)
    ((,ids ,ts) (guard (every symbol? ids))
     (values ids (map parse-optional-type-syntax ts)))))

;; parse-proc-exp : List x List -> Exp
(define (parse-proc-exp args body)
  (let-values (((ids ts) (parse-args args)))
    `(proc-exp ,ts ,ids ,(parse body))))

;;; Main driver

(define (parse-and-infer sexp)
  (type-to-external-form
   (infer-type
    (parse sexp))))

;;; Tests

(define (run-tests)
  (define (rejected? sexp)
    (guard (con
             ((type-cond? con) #t)
             (else (raise con)))
      (parse-and-infer sexp)))

  (test 'bool (parse-and-infer 'true))
  (test 'bool (parse-and-infer 'false))
  (test 'int (parse-and-infer 4))
  (test 'bool (parse-and-infer '(zero? 4)))
  (test 'int (parse-and-infer '(- 4 1)))
  (test 'int (parse-and-infer '(if (zero? 3) 1 0)))
  (test 'int (parse-and-infer '(let ((x = 4)) in x)))
  (test 'bool (parse-and-infer '(let ((z = (zero? 3))) in z)))
  (test '(-> int int)
        (parse-and-infer '(proc ((x . int)) 0)))
  (test '(-> int int)
         (parse-and-infer
          '(let ((f = (proc ((x . int)) (- x (- 0 1)))))
            in (proc ((y . int)) (- (f y) 4)))))
  (test '(-> int bool)
        (parse-and-infer '(proc ((x . int)) (zero? x))))
  (test '(-> ((-> (int) int)) (-> (int) bool))
        (parse-and-infer
         '(proc ((f . (-> (int) int)))
            (proc ((x . int)) (zero? (f x))))))
  (test '(-> (int) int)
        (parse-and-infer '(letrec ((int f ((x . int)) = x)) in f)))
  (test 'bool
        (parse-and-infer
         '(letrec ((bool g ((x . int)) = (zero? (- x 1))))
           in (g 10))))
  (test 'int
        (parse-and-infer
         '((proc ((x . int))
             ((proc ((y . int)) (- x y)) (- x 2)))
           4)))
  (test 'int
        (parse-and-infer '(let ((x = 10) (y = 11)) in (- y x))))
  (test 'int
        (parse-and-infer '(let ((b = true) (x = 4)) in (if b x 0))))

  (test #t (rejected? '(- (zero? 3) 2)))
  (test #t (rejected? '(- 3 (proc ((x . int)) x))))
  (test #t (rejected? '(zero? (zero? 0))))
  (test #t (rejected? '(if 3 1 0)))
  (test #t (rejected? '(if (zero? 3) (zero? 1) 4)))
  (test #t (rejected? '(if (zero? 0) 3 ((proc ((x . int)) (zero? x)) 4))))
  (test #t (rejected? '(let ((x = 4)) in (if x 0 1))))
  (test #t (rejected? '((proc ((f . (-> (int) int))) (f 10))
                        (proc ((x . int)) (zero? x)))))
  (test #t (rejected? '(letrec ((int f ((x . bool)) = (f (f x)))) in 4)))
  (test #t (rejected? '(4 4)))
  (test #t (rejected? '(((proc ((x . int)) x) 10) 3)))
  (test #t (rejected? '(let ((b = false) (x = 5)) in (if x b true))))
  )
