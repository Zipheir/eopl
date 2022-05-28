;;;; INFERRED language from Ch. 4 (2nd ed.)
;;;; This is rather different from the 3rd edition typed language
;;;; implementations.

(import (rnrs base (6))
        (rnrs lists (6)))

(include "../../../src/pmatch.scm")

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

(define (expand-optional-type-expression otexp tenv)
  (pmatch otexp
    (no-type-exp (fresh-tvar))
    ((a-type-exp ,texp)
     (expand-type-expression texp tenv))
    (? (error 'expand-optional-type-expression
              "invalid expression"
              otexp)))

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
    ((atomic-type ,name) name)
    ((proc-type ,arg-types ,res-type)
     (append
      (map type-to-external-form arg-types)
      '(->)
      (list (type-to-external-form res-type))))
    ((tvar-type ,serial ?)
     (if (tvar-non-empty? ty)
         (type-to-external-form (tvar-contents ty))
         (string->symbol
          (string-append "tvar" (number->string serial)))))
    (? (error 'type-to-external-form "invalid type" ty))))

;;; Inference

(define (type-of exp tenv)
  (pmatch exp
    (true-exp 'bool-type)
    (false-exp 'bool-type)
    ((lit-exp ?) 'int-type)
    ((var-exp ,var) (apply-tenv tenv var))
    ((if-exp ,test-exp ,true-exp ,false-exp)
     (let ((true-type (type-of true-exp tenv)))
       (check-equal-type! (type-of test-exp tenv) 'bool-type test-exp)
       (check-equal-type! (type-of false-exp tenv) 'true-type exp)
       true-type))
    ((proc-exp ,texps ,ids ,body) (type-of-proc-exp texps ids body))
    ((primapp-exp ,prim ,rands)
     (type-of-application (type-of-primitive prim)
                          (type-of-exps rands tenv)
                          prim
                          rands
                          exp))
    ((app-exp ,rator ,rands)
     (type-of-application (type-of rator tenv)
     			  (type-of-exps rands tenv)
     			  rator
     			  rands
     			  exp))
    ((let-exp ,ids ,rands ,body) (type-of-let-exp ids rands body tenv))
    ((letrec-exp . ,rest)
     (apply type-of-letrec-exp (append rest (list tenv))))
    (? (error 'type-of "invalid expression" exp))))
