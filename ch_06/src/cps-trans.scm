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
(define (cps-of-exps exps builder)
  (letrec
   ((cps-of-rest
     (lambda (exps acc)
       (pmatch exps
         (() (builder (reverse acc)))
         ((,e . ,es)
          (if (inp-exp-simple? e)
              (cps-of-rest es (cons (cps-of-simple-exp e) acc))
              (make-bind e es acc))))))

    (make-bind
     (lambda (exp rest-exps acc)
       (let ((var (fresh-identifier 'var)))
         (cps-of-exp exp
                     `(cps-proc-exp
                       (,var)
                       ,(cps-of-rest
                         rest-exps
                         (cons (cps-of-simple-exp `(var-exp ,var))
                               acc))))))))

    (cps-of-rest exps '())))

;; inp-exp-simple? : Inp-exp -> Bool
(define (inp-exp-simple? exp)
  (pmatch exp
    (emptylist-exp #t)
    ((const-exp ?) #t)
    ((var-exp ?) #t)
    ((diff-exp ,exp1 ,exp2)
     (and (inp-exp-simple? exp1) (inp-exp-simple? exp2)))
    ((zero?-exp ,exp1) (inp-exp-simple? exp1))
    ((proc-exp ? ?) #t)
    ((sum-exp ,exps) (every inp-exp-simple? exps))
    ((car-exp ,exp1) (inp-exp-simple? exp1))
    ((cdr-exp ,exp1) (inp-exp-simple? exp1))
    ((cons-exp ,exp1 ,exp2)
     (and (inp-exp-simple? exp1) (inp-exp-simple? exp2)))
    ((null?-exp ,exp1) (inp-exp-simple? exp1))
    ((list-exp ,exps) (every inp-exp-simple? exps))
    (? #f)))

;; substitute-free : Var x Simple-exp x Tf-exp -> Tf-exp
(define (substitute-free old new exp)
  (letrec
   ((subst-tf
     (lambda (exp bvars)
       (pmatch exp
         ((simple-exp->exp ,simple)
          `(simple-exp->exp ,(subst-simple simple bvars)))
         ((cps-let-exp ,vars ,rhss ,body)
          `(cps-let-exp ,vars ,rhss ,(subst-tf body
                                               (append vars bvars))))
         ((cps-letrec-exp ,nms ,bvs ,pbs ,lr-body)
          `(cps-letrec-exp ,nms ,vs ,pbs
                           ,(subst-tf lr-body (append vs bvars))))
         ((cps-if-exp ,s1 ,exp2 ,exp3)
          `(cps-if-exp ,(subst-simple s1 bvars)
                       ,(subst-tf exp2 bvars)
                       ,(subst-tf exp3 bvars)))
         ((cps-call-exp ,rator ,rands)
          `(cps-call-exp ,(subst-simple rator bvars)
                         ,(map (lambda (s)
                                 (subst-simple s bvars))
                               rands))))))
    (subst-simple
     (lambda (exp bvars)
       (pmatch exp
         (cps-emptylist-exp exp)
         ((cps-const-exp ,n) exp)
         ((cps-var-exp ,v)
          (if (and (eqv? v old) (not (memv v bvars)))
              new
              exp))
         ((cps-diff-exp ,exp1 ,exp2)
          `(cps-diff-exp ,(subst-simple exp1 bvars)
                         ,(subst-simple exp2 bvars)))
         ((cps-zero?-exp ,exp1)
          `(cps-zero?-exp ,(subst-simple exp1 bvars)))
         ((cps-proc-exp ,vars ,body)
          `(cps-proc-exp ,vars ,(subst-tf body (append bvars vars))))
         ((cps-sum-exp ,exps)
          `(cps-sum-exp ,(map (lambda (e)
                                (subst-simple e bvars))
                              exps)))
         ((cps-cons-exp ,exp1 ,exp2)
          `(cps-cons-exp ,(subst-simple exp1 bvars)
                         ,(subst-simple exp2 bvars)))
         ((cps-car-exp ,exp1)
          `(cps-car-exp ,(subst-simple exp1 bvars)))
         ((cps-cdr-exp ,exp1)
          `(cps-cdr-exp ,(subst-simple exp1 bvars)))
         ((cps-null?-exp ,exp1)
          `(cps-null?-exp ,(subst-simple exp1 bvars)))
         ((cps-list-exp ,exps)
          `(cps-list-exp ,(map (lambda (e)
                                 (subst-simple e bvars))
                               exps)))
         (? (error 'substitute-free "invalid simple exp" exp))))))

    (subst-tf exp '())))

;; make-send-to-cont : Simple-exp x Simple-exp -> Simple-exp
(define (make-send-to-cont k-exp simple)
  (pmatch k-exp
    ((cps-proc-exp (,v) ,e)
     (substitute-free v simple e))
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
             (,k)
             (,k-exp)
             (cps-if-exp ,(car sms)
                         ,(cps-of-exp exp2 `(cps-var-exp ,k))
                         ,(cps-of-exp exp3 `(cps-var-exp ,k)))))))))

;; cps-of-let-exp : Var x Inp-exp x Inp-exp x Simple-exp -> Tf-exp
(define (cps-of-let-exp ids rhss body k-exp)
  (cps-of-exps
   rhss
   (lambda (sms)
     `(cps-let-exp ,ids ,sms ,(cps-of-exp body k-exp)))))

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
    (emptylist-exp 'cps-emptylist-exp)
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
    ((cons-exp ,exp1 ,exp2)
     `(cps-cons-exp ,(cps-of-simple-exp exp1)
                    ,(cps-of-simple-exp exp2)))
    ((car-exp ,exp1) `(cps-car-exp ,(cps-of-simple-exp exp1)))
    ((cdr-exp ,exp1) `(cps-cdr-exp ,(cps-of-simple-exp exp1)))
    ((null?-exp ,exp1) `(cps-null?-exp ,(cps-of-simple-exp exp1)))
    ((list-exp ,exps)
     `(cps-list-exp ,(map cps-of-simple-exp exps)))
    (? (error 'cps-of-simple-exp "invalid simple exp" exp))))

;; cps-of-call-exp : Inp-exp x List-of(Inp-exp) x Simple-exp -> Tf-exp
(define (cps-of-call-exp rator rands k-exp)
  (cps-of-exps
   (cons rator rands)
   (lambda (sms)
     `(cps-call-exp ,(car sms)
     		    ,(append (cdr sms) (list k-exp))))))

;; cps-of-cons-exp : Inp-exp x Inp-exp x Simple-exp -> Tf-exp
(define (cps-of-cons-exp exp1 exp2 k-exp)
  (cps-of-exps
   (list exp1 exp2)
   (lambda (sms)
     (pmatch sms
       ((,s1 ,s2)
        (make-send-to-cont k-exp
                           `(cps-cons-exp ,s1 ,s2)))))))

;; cps-of-unary : Sym x Inp-exp x Simple-exp -> Tf-exp
;;
;; Translate a unary form.
(define (cps-of-unary out-form exp1 k-exp)
  (cps-of-exps
   (list exp1)
   (lambda (sms)
     (make-send-to-cont k-exp
                        (list out-form (car sms))))))

;; cps-of-list-exp : List-of(Inp-exp) x Simple-exp -> Tf-exp
(define (cps-of-list-exp exps k-exp)
  (cps-of-exps
   exps
   (lambda (sms)
     (make-send-to-cont k-exp `(cps-list-exp ,sms)))))

;;; Main translator dispatch

;; cps-of-exp : Inp-exp x Simple-exp -> Tf-exp
(define (cps-of-exp exp k-exp)
  (pmatch exp
    (emptylist-exp (make-send-to-cont k-exp 'cps-emptylist-exp))
    ((const-exp ,num)
     (make-send-to-cont k-exp `(cps-const-exp ,num)))
    ((var-exp ,var)
     (make-send-to-cont k-exp `(cps-var-exp ,var)))
    ((proc-exp ,vars ,body)
     (make-send-to-cont
      k-exp
      `(cps-proc-exp (append vars (list 'k%00))
                     (cps-of-exp body '(cps-var-exp k%00)))))
    ((zero?-exp ,exp1) (cps-of-unary 'cps-zero?-exp exp1 k-exp))
    ((diff-exp ,exp1 ,exp2) (cps-of-diff-exp exp1 exp2 k-exp))
    ((sum-exp ,exps) (cps-of-sum-exp exps k-exp))
    ((if-exp ,exp1 ,exp2 ,exp3) (cps-of-if-exp exp1 exp2 exp3 k-exp))
    ((let-exp ,vars ,rhss ,body) (cps-of-let-exp vars rhss body k-exp))
    ((letrec-exp ,nms ,vars ,pbs ,lr-body)
     (cps-of-letrec-exp nms vars pbs lr-body k-exp))
    ((call-exp ,rator ,rands) (cps-of-call-exp rator rands k-exp))
    ((cons-exp ,exp1 ,exp2) (cps-of-cons-exp exp1 exp2 k-exp))
    ((car-exp ,exp1) (cps-of-unary 'cps-car-exp exp1 k-exp))
    ((cdr-exp ,exp1) (cps-of-unary 'cps-cdr-exp exp1 k-exp))
    ((null?-exp ,exp1) (cps-of-unary 'cps-null?-exp exp1 k-exp))
    ((list-exp ,exps) (cps-of-list-exp exps k-exp))
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
    (emptylist 'emptylist-exp)
    (,n (guard (number? n)) `(const-exp ,n))
    ((- ,s ,t) `(diff-exp ,(parse s) ,(parse t)))
    ((+ . ,es) `(sum-exp ,(map parse es)))
    ((zero? ,s) `(zero?-exp ,(parse s)))
    ((if ,t ,c ,a) `(if-exp ,(parse t) ,(parse c) ,(parse a)))
    (,v (guard (symbol? v)) `(var-exp ,v))
    ((let ,bs in ,b) (parse-let-exp bs b))
    ((proc ,vs ,body) (guard (every symbol? vs))
     `(proc-exp ,vs ,(parse body)))
    ((letrec ,bs in ,body) (parse-letrec-exp bs body))
    ((cons ,e1 ,e2) `(cons-exp ,(parse e1) ,(parse e2)))
    ((car ,e) `(car-exp ,(parse e)))
    ((cdr ,e) `(cdr-exp ,(parse e)))
    ((null? ,e) `(null?-exp ,(parse e)))
    ((list . ,es) `(list-exp ,(map parse es)))
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

;; parse-let-exp : List x List -> Exp
(define (parse-let-exp binds body)
  (letrec
    ((collect
      (lambda (bs vars vals)
        (pmatch bs
          (() (values vars vals))
          (((,v = ,e) . ,bs*) (guard (symbol? v))
           (collect bs* (cons v vars) (cons (parse e) vals)))))))

    (let-values (((vars vals) (collect binds '() '())))
      `(let-exp ,vars ,vals ,(parse body)))))

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

  (define (eval-to-num-list lis)
    (map expval->num
         (expval->list (value-of-program (translate lis)))))

  (test 5 (eval-to-num '5))
  (test 5 (eval-to-num 'v))
  (test 0 (eval-to-num '(if (zero? 2) 1 0)))
  (test 1 (eval-to-num '(if (zero? 0) 1 0)))
  (test 1 (eval-to-num '(- 3 2)))
  (test 4 (eval-to-num '(let ((a = (- v i))) in a)))
  (test 6 (eval-to-num
           '(let ((add1 = (proc (a) (- a (- 0 1))))) in (add1 v))))
  (test 5 (eval-to-num
           '(let ((add1 = (proc (b) (- b (- 0 1))))) in
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
           '(let ((add = (proc (x y) (- x (- 0 y))))) in
              (add (add 1 1) (add 1 (add 1 1))))))
  (test 5 (eval-to-num
           '(letrec ((f (x y z) = (- x (- y z)))) in
              (f 8 5 2))))
  (test 5 (eval-to-num '(let ((t = (proc () 5))) in (t))))

  ;;; Calls with non-simple operands.

  (test 9 (eval-to-num
           '((proc (x y) (+ x y))
             (let ((a = 7)) in a)
             (let ((b = 2)) in b))))
  (test 5 (eval-to-num
           '(+ ((proc (a) (- a 2)) 3)
               ((proc (b) (if (zero? b) 4 6)) 0))))

  ;;; Lists

  ;; Lots of extra lets & calls to ensure that the non-simple
  ;; branches get tested.
  (test '() (eval-to-num-list 'emptylist))
  (test '() (eval-to-num-list
             '(let ((x = emptylist)) in
                ((proc (y) y) x))))
  (test '(1) (eval-to-num-list '(cons 1 emptylist)))
  (test '(2 3) (eval-to-num-list
                '(let ((id = (proc (y) y))) in
                   (cons (id 2) (cons 3 (id emptylist))))))
  (test 2 (eval-to-num '(car (cons 2 emptylist))))
  (test 2 (eval-to-num
           '(let ((id = (proc (y) y))) in
              (car (id (cons 2 (cons (id 3) emptylist)))))))
  (test '() (eval-to-num-list '(cdr (cons 2 emptylist))))
  (test '(3) (eval-to-num-list
              '(let ((id = (proc (y) y))) in
                 (cdr (id (cons (id 2) (cons 3 emptylist)))))))
  (test 1 (eval-to-num '(if (null? emptylist) 1 0)))
  (test 0 (eval-to-num '(if (null? (cons 1 emptylist)) 1 0)))
  (test 1 (eval-to-num
           '(if (null? (let ((xs = emptylist)) in xs))
                1
                0)))
  (test '() (eval-to-num-list '(list)))
  (test '(2 3) (eval-to-num-list '(list 2 3)))
  (test '(2 4 5) (eval-to-num-list
                  '(let ((xs = (list 2 3))) in
                     (let ((ys = (list 4 5))) in
                       (cons (car xs) ys)))))
  (test '(2 3) (eval-to-num-list
                '(list (let ((x = 2)) in x)
                       (let ((y = 0)) in
                         (if (zero? y)
                             (let ((v = 3)) in v)
                             0)))))
  )
