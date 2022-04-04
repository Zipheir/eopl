;;;; EXPLICIT-REFS language from Ch. 4.

(import (rnrs lists (6))
        (rnrs records syntactic (6)))

(include "pmatch.scm")

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
        (cond ((null? store1)
               (report-invalid-reference ref the-store))
              ((zero? ref1) (cons val (cdr store1)))
              (else (cons (car store1
                               (setref-inner (cdr store1)
                                             (- ref1 1)))))))))
    (setref-inner the-store ref)))
