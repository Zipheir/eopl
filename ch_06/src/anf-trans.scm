;;;; ANF-IN to ANF-OUT translator from Ex. 6.34.

(import (rnrs base (6))
        (rename (rnrs lists (6)) (for-all every)))

(include "../../src/pmatch.scm")

(define (simple? exp)
  (and (pair? exp) (memv (car exp) '(const-exp var-exp))))

(define (normalize-term exp)
  (normalize exp (lambda (x) x)))

(define (normalize exp cont)
  (pmatch exp
    ((const-exp ?) (cont exp))
    ((var-exp ?) (cont exp))
    ((if-exp ,exp1 ,exp2 ,exp3)
     (normalize-if-exp exp1 exp2 exp3 cont))
    ((zero?-exp ,exp1)
     (normalize-unary-exp 'anf-zero?-exp exp1 cont))
    ((diff-exp ,exp1 ,exp2)
     (normalize-diff-exp exp1 exp2 cont))
    ((proc-exp ,vars ,body)
     (cont `(anf-proc-exp ,vars ,(normalize-term body))))
    ((call-exp ,rator ,rands) (normalize-call-exp rator rands cont))
    ((let-exp ,var ,rhs ,body)
     (normalize-let-exp var rhs body cont))
    ((letrec-exp ,names ,b-varss ,p-bodies ,lr-body)
     (normalize-letrec-exp names b-varss p-bodies lr-body cont))
    ((sum-exp ,exps) (normalize-sum-exp exps cont))
    (? (error 'normalize "invalid expression" exp))))

(define (normalize-name exp cont)
  (normalize exp
             (lambda (res)
               (if (simple? res)
                   (cont res)
                   (let ((var (gensym "var")))
                     `(anf-let-exp ,var ,res ,(cont var)))))))

;; Very much an *idiom*.
(define (normalize-name* exps cont)
  (pmatch exps
    (() (cont '()))
    ((,e . ,es)
     (normalize-name
      e
      (lambda (v)
        (normalize-name* es
                         (lambda (vs)
                           (cont (cons v vs)))))))))

(define (normalize-if-exp exp1 exp2 exp3 cont)
  (normalize-name
   exp1
   (lambda (vexp)
     (cont `(anf-if-exp ,vexp
                        ,(normalize-term exp2)
                        ,(normalize-term exp3))))))

(define (normalize-unary-exp outform exp1 cont)
  (normalize-name
   exp1
   (lambda (vexp)
     (cont (list outform vexp)))))

(define (normalize-diff-exp exp1 exp2 cont)
  (normalize-name
   exp1
   (lambda (v1)
     (normalize-name
      exp2
      (lambda (v2)
        (cont `(anf-diff-exp ,v1 ,v2)))))))

(define (normalize-call-exp rator rands cont)
  (if (simple? rator)
      (normalize-name* rands
                       (lambda (vs)
                         (cont `(anf-call-exp ,rator ,vs))))
      (normalize-name
       rator
       (lambda (vrat)
         (normalize-name*
          rands
          (lambda (vrands)
            (cont `(anf-call-exp ,vrat ,vrands))))))))

(define (normalize-let-exp var rhs body cont)
  (normalize
   rhs
   (lambda (v)
     `(anf-let-exp ,var ,v ,(normalize body cont)))))

(define (normalize-letrec-exp names b-varss p-bodies lr-body cont)
  (let ((bs (map normalize-term p-bodies)))
    `(anf-letrec-exp ,names ,b-varss ,bs ,(normalize lr-body cont))))

(define (normalize-sum-exp exps cont)
  (normalize-name*
   exps
   (lambda (vs)
     (cont `(anf-sum-exp ,vs)))))

;;; Parser

;; Parser for a simple S-exp representation.
;; parse : List -> Inp-exp
(define (parse sexp)
  (pmatch sexp
    (,n (guard (number? n)) `(const-exp ,n))
    ((- ,s ,t) `(diff-exp ,(parse s) ,(parse t)))
    ((+ . ,es) `(sum-exp ,(map parse es)))
    ((zero? ,s) `(zero?-exp ,(parse s)))
    ((if ,t ,c ,a) `(if-exp ,(parse t) ,(parse c) ,(parse a)))
    (,v (guard (symbol? v)) `(var-exp ,v))
    ((let ,v = ,e in ,b) (guard (symbol? v))
     `(let-exp ,v ,(parse e) ,(parse b)))
    ((proc ,vs ,body) (guard (every symbol? vs))
     `(proc-exp ,vs ,(parse body)))
    ((letrec ,bs in ,body) (parse-letrec-exp bs body))
    ((,e1 . ,es) `(call-exp ,(parse e1) ,(map parse es)))
    (? (error 'parse "invalid syntax" sexp))))

(define (parse-letrec-exp binds body)
  (let* ((f (lambda args
              (pmatch args
                (((,nm ,vs = ,e) (,names ,b-varss ,bodies))
                 (guard (symbol? nm) (every symbol? vs))
                 (list (cons nm names)
                       (cons vs b-varss)
                       (cons (parse e) bodies))))))
         (ts (fold-right f '(() () ()) binds)))
    (pmatch ts
      ((,names ,vars ,bodies)
       `(letrec-exp ,names ,vars ,bodies ,(parse body))))))

;; translate : List -> Anf-exp
(define (translate sexp)
  (normalize-term (parse sexp)))
