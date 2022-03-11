(import (rnrs records syntactic (6)))

(include "pmatch.scm")
(include "test.scm")

;;; Lc-exp ::= Identifier
;;;            [var-exp (var)]
;;;
;;;        ::= (lambda ({Identifier}*) Lc-exp)
;;;            [lambda-exp (bound-vars body)]
;;;
;;;        ::= (Lc-exp {Lc-exp}*)
;;;            [app-exp (rator rands)]

(define-record-type var-exp
  (fields var))

(define-record-type lambda-exp
  (fields bound-vars body))

(define-record-type app-exp
  (fields rator rands))

;; parse-expression : Scheme-val → Lc-exp
(define (parse-expression obj)
  (pmatch obj
    (,sym (guard (symbol? sym)) (make-var-exp sym))
    ((lambda ,vars ,body)
     (make-lambda-exp vars (parse-expression body)))
    ((,rator . ,rands)
     (make-app-exp (parse-expression rator)
                   (map parse-expression rands)))
    (? (error 'parse-expression "syntax error" obj))))
