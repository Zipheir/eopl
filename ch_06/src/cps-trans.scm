;;;; CPS-IN -> CPS-OUT translator from Ch. 6

(import (rnrs base (6))
        (rename (rnrs lists (6)) (for-all every))
        )

(include "cps-out-library.scm")
(import (cps-out))

(include "../../src/pmatch.scm")
(include "../../src/test.scm")

;;; Utility

;; list-index : List-of(A) x (A -> Bool) -> (Int + False)
(define (list-index pred xs)
  (letrec
   ((index
     (lambda (xs i)
       (pmatch xs
         (() #f)
         ((,x . ,xs*)
          (if (pred x)
              i
              (index xs* (+ i 1))))))))
    (index xs 0)))

;; list-set : List x Int x Scheme-val -> List
(define (list-set xs k y)
  (pmatch xs
    (() (error 'list-set "short list"))
    ((,x . ,xs*)
     (if (zero? k)
         (cons y xs*)
         (cons x (list-set xs* (- k 1) y))))))

;;; Simple gensyms

(define fresh-identifier
  (let ((name-counter 0))
    (lambda (prefix)
      (let ((res (string->symbol
                  (string-append (symbol->string prefix)
           	                 (number->string name-counter)))))
        (set! name-counter (+ name-counter 1))
        res))))

;; cps-of-exps : List-of(Inp-exp) x (List-of(Inp-exp) -> Tf-exp) ->
;;		   Tf-exp
;; Usage: CPSs a list of subexpressions.  The translated list is
;; passed to builder.
(define (cps-of-exps exps builder)
  (letrec
   ((cps-of-rest
     (lambda (exps)
       (let ((pos (list-index
                   (lambda (exp)
	             (not (inp-exp-simple? exp)))
	           exps)))
	 (if (not pos)
	     (builder (map cps-of-simple-exp exps))
	     (let ((var (fresh-identifier 'var)))
	       (cps-of-exp (list-ref exps pos)
	                   `(cps-proc-exp
	                     ,(list var)
	                     ,(cps-of-rest
	                       (list-set exps
	                                 pos
	                                 `(var-exp ,var)))))))))))
    (cps-of-rest exps)))

;; inp-exp-simple? : Inp-exp -> Bool
(define (inp-exp-simple? exp)
  (pmatch exp
    ((const-exp ?) #t)
    ((var-exp ?) #t)
    ((diff-exp ,exp1 ,exp2)
     (and (inp-exp-simple? exp1) (inp-exp-simple? exp2)))
    ((zero?-exp ,exp1) (inp-exp-simple? exp1))
    ((proc-exp ? ?) #t)
    ((sum-exp ,exps) (every inp-exp-simple? exps))
    (? #f)))

;; make-send-to-cont : Simple-exp x Simple-exp -> Tf-exp
(define (make-send-to-cont k-exp simple)
  (pmatch k-exp
    ((cps-proc-exp (,v) ,e)
     `(cps-let-exp ,v ,simple ,e))
    (? `(cps-call-exp ,k-exp ,(list simple)))))

;; cps-of-sum-exp : List-of(Inp-exp) x Simple-exp -> Tf-exp
(define (cps-of-sum-exp exps k-exp)
  (cps-of-exps
   exps
   (lambda (sms)
     (make-send-to-cont k-exp `(cps-sum-exp ,sms)))))

;; cps-of-diff-exp : Inp-exp x Inp-exp x Simple-exp -> Tf-exp
(define (cps-of-diff-exp exp1 exp2 k-exp)
  (cps-of-exps
   (list exp1 exp2)
   (lambda (sms)
     (pmatch sms
       ((,s1 ,s2)
        (make-send-to-cont k-exp `(cps-diff-exp ,s1 ,s2)))))))

;; cps-of-if-exp : Inp-exp x Inp-exp x Inp-exp x Simple-exp -> Tf-exp
(define (cps-of-if-exp exp1 exp2 exp3 k-exp)
  (if (inp-exp-simple? exp1)
      `(cps-if-exp ,(cps-of-simple-exp exp1)
                   ,(cps-of-exp exp2 k-exp)
                   ,(cps-of-exp exp3 k-exp))
      (cps-of-exps
       (list exp1)
       (lambda (sms)
         (let ((k (fresh-identifier 'k)))
           `(cps-let-exp
             ,k
             ,k-exp
             (cps-if-exp ,(car sms)
                         ,(cps-of-exp exp2 `(cps-var-exp ,k))
                         ,(cps-of-exp exp3 `(cps-var-exp ,k)))))))))

;; cps-of-let-exp : Var x Inp-exp x Inp-exp x Simple-exp -> Tf-exp
(define (cps-of-let-exp id rhs body k-exp)
  (cps-of-exps
   (list rhs)
   (lambda (sms)
     `(cps-let-exp ,id ,(car sms) ,(cps-of-exp body k-exp)))))

;; cps-of-letrec-exp : List-of(Var) x List-of(List-of(Var)) x
;;                       List-of(Inp-exp) x Simple-exp -> Tf-exp
(define (cps-of-letrec-exp p-names b-varss p-bodies lr-body k-exp)
  `(cps-letrec-exp
    ,p-names
    ,(map (lambda (b-vars)
            (append b-vars (list 'k%00)))
          b-varss)
    ,(map (lambda (p-body)
            (cps-of-exp p-body `(cps-var-exp k%00)))
          p-bodies)
    ,(cps-of-exp lr-body k-exp)))

;; cps-of-simple-exp : Simple-inp-exp -> Simple-exp
(define (cps-of-simple-exp exp)
  (pmatch exp
    ((const-exp ,num) `(cps-const-exp ,num))
    ((var-exp ,var) `(cps-var-exp ,var))
    ((diff-exp ,exp1 ,exp2)
     `(cps-diff-exp ,(cps-of-simple-exp exp1)
                    ,(cps-of-simple-exp exp2)))
    ((zero?-exp ,exp1)
     `(cps-zero?-exp ,(cps-of-simple-exp exp1)))
    ((proc-exp ,vars ,body)
     `(cps-proc-exp ,(append vars (list 'k%00))
                    ,(cps-of-exp body '(cps-var-exp k%00))))
    ((sum-exp ,exps)
     `(cps-sum-exp ,(map cps-of-simple-exp exps)))
    (? (error 'cps-of-simple-exp "invalid simple exp" exp))))

;; cps-of-call-exp : Inp-exp x List-of(Inp-exp) x Simple-exp -> Tf-exp
(define (cps-of-call-exp rator rands k-exp)
  (cps-of-exps
   (cons rator rands)
   (lambda (sms)
     `(cps-call-exp ,(car sms)
     		    ,(append (cdr sms) (list k-exp))))))

;; cps-of-zero?-exp : Inp-exp x Simple-exp -> Tf-exp
(define (cps-of-zero?-exp exp1 k-exp)
  (cps-of-exps (list exp1)
               (lambda (sms)
                 (make-send-to-cont
                  k-exp
                  `(cps-zero?-exp ,(car sms))))))

;;; Main translator dispatch

;; cps-of-exp : Inp-exp x Simple-exp -> Tf-exp
(define (cps-of-exp exp k-exp)
  (pmatch exp
    ((const-exp ,num)
     (make-send-to-cont k-exp `(cps-const-exp ,num)))
    ((var-exp ,var)
     (make-send-to-cont k-exp `(cps-var-exp ,var)))
    ((proc-exp ,vars ,body)
     (make-send-to-cont
      k-exp
      `(cps-proc-exp (append vars (list 'k%00))
                     (cps-of-exp body '(cps-var-exp k%00)))))
    ((zero?-exp ,exp1) (cps-of-zero?-exp exp1 k-exp))
    ((diff-exp ,exp1 ,exp2) (cps-of-diff-exp exp1 exp2 k-exp))
    ((sum-exp ,exps) (cps-of-sum-exp exps k-exp))
    ((if-exp ,exp1 ,exp2 ,exp3) (cps-of-if-exp exp1 exp2 exp3 k-exp))
    ((let-exp ,var ,exp1 ,body) (cps-of-let-exp var exp1 body k-exp))
    ((letrec-exp ,nms ,vars ,pbs ,lr-body)
     (cps-of-letrec-exp nms vars pbs lr-body k-exp))
    ((call-exp ,rator ,rands) (cps-of-call-exp rator rands k-exp))
    (? (error 'cps-of-exp "invalid expression" exp))))

;; cps-of-program : Inp-program -> Tf-program
(define (cps-of-program pgm)
  (pmatch pgm
    ((program ,exp1)
     `(cps-program
       ,(cps-of-exps (list exp1)
                     (lambda (new)
                       `(simple-exp->exp ,(car new))))))))

;;; Parser

;; Parser for a simple S-exp representation.
;; parse : List -> Exp
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

;; parse-program : List -> Program
(define (parse-program sexp)
  (list 'program (parse sexp)))

;; run : List x Bool -> Tf-program
(define (translate sexp)
  (cps-of-program (parse-program sexp)))

;;;; Tests

(define (run-tests)
  (define (eval-to-num lis)
    (expval->num (value-of-program (translate lis))))

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
  (test 1 (eval-to-num
           '(letrec ((even (x) = (if (zero? x) 1 (odd (- x 1))))
                     (odd (x) = (if (zero? x) 0 (even (- x 1)))))
             in (even 4))))
  (test 0 (eval-to-num
           '(letrec ((even (x) = (if (zero? x) 1 (odd (- x 1))))
                     (odd (x) = (if (zero? x) 0 (even (- x 1)))))
             in (even 5))))

  ;;; Multi-arg procs

  (test 5 (eval-to-num
           '(let add = (proc (x y) (- x (- 0 y))) in
              (add (add 1 1) (add 1 (add 1 1))))))
  (test 5 (eval-to-num
           '(letrec ((f (x y z) = (- x (- y z)))) in
              (f 8 5 2))))
  (test 5 (eval-to-num '(let t = (proc () 5) in (t))))

  ;;; Calls with non-simple operands.

  (test 9 (eval-to-num
           '((proc (x y) (+ x y))
             (let a = 7 in a)
             (let b = 2 in b))))
  (test 5 (eval-to-num
           '(+ ((proc (a) (- a 2)) 3)
               ((proc (b) (if (zero? b) 4 6)) 0))))
  )
