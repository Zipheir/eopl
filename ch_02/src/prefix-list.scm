;;;; Exercise 2.31

(import (rnrs records syntactic (6)))

(include "pmatch.scm")
(include "test.scm")

;;; The concrete syntax:
;;;
;;; Prefix-list ::= '(' Prefix-exp ')'
;;; Prefix-exp  ::= Int
;;;             ::= '-' Prefix-exp Prefix-exp

(define-record-type const-exp
  (fields num))

(define-record-type diff-exp
  (fields operand1 operand2))

;; parse-expression : List → Prefix-exp
(define (parse-prefix-list obj)
  (pmatch (parse-one obj)
    ((,e ()) e)
    (? (error 'parse-prefix-list "syntax error" obj))))

;; parse-one : List → Prefix-exp × List
;; Usage: Parses the first prefix-exp of xs and returns it along
;; with the remainder of xs.
(define (parse-one xs)
  (pmatch xs
    ((,n . ,xs*) (guard (integer? n)) (list (make-const-exp n) xs*))
    ((- . ,xs*)
     (pmatch (parse-one xs*)
       ((,op1 ,xs**)
        (pmatch (parse-one xs**)
          ((,op2 ,xs***)
           (list (make-diff-exp op1 op2) xs***))))))
    (() (error 'parse-prefix-list "syntax error: short list" xs))))

;; Bonus:
;; unparse-prefix-list : Prefix-exp → List
;; Usage: Unparses a prefix list expression to its extern rep..
(define (unparse-prefix-list exp)
  (if (const-exp? exp)
      (list (const-exp-num exp))
      (let ((op1-lis (unparse-prefix-list (diff-exp-operand1 exp)))
            (op2-lis (unparse-prefix-list (diff-exp-operand2 exp))))
        (append '(-) op1-lis op2-lis))))

;;;; Tests

(define (run-tests)
  (define test-lists
    '((3)
      (- 3 2)
      (- - 3 2 - 4 - 12 7)
      (- - - - 8 2 1 3 4)
      (- 8 - 7 - 6 - 5 4)
      ))

   (test #t (for-all (lambda (xs)
                       (equal? xs (unparse-prefix-list
                                   (parse-prefix-list xs))))
                     test-lists))
   )
