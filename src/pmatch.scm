;; This is a new version of pmatch (August 8, 2012).
;; It has two important new features:
;; 1.  It allows for a name to be given to the pmatch if an error ensues.
;; 2.  A line from the specification has been removed. (see below).  Without
;; that line removed, it was impossible for a pattern to be (quote ,x),
;; which might be worth having especially when we write an interpreter
;; for Scheme, which includes quote as a language form.

;;; Code written by Oleg Kiselyov
;; (http://pobox.com/~oleg/ftp/)
;;;
;;; Taken from leanTAP.scm
;;; http://kanren.cvs.sourceforge.net/kanren/kanren/mini/leanTAP.scm?view=log

; A simple linear pattern matcher
; It is efficient (generates code at macro-expansion time) and simple:
; it should work on any R5RS (and R6RS) Scheme system.

; (pmatch exp <clause> ...[<else-clause>])
; <clause> ::= (<pattern> <guard> exp ...)
; <else-clause> ::= (else exp ...)
; <guard> ::= boolean exp | ()
; <pattern> :: =
;        ,var  -- matches always and binds the var
;                 pattern must be linear! No check is done
;         _    -- matches always
;        'exp  -- comparison with exp (using equal?)    REMOVED (August 8, 2012)
;        exp   -- comparison with exp (using equal?)
;        (<pattern1> <pattern2> ...) -- matches the list of patterns
;        (<pattern1> . <pattern2>)  -- ditto
;        ()    -- matches the empty list

(define-syntax pmatch
  (syntax-rules (else guard)
    ((pmatch v (e ...) ...)
     (pmatch-aux #f v (e ...) ...))
    ((pmatch v name (e ...) ...)
     (pmatch-aux name v (e ...) ...))))

(define-syntax pmatch-aux
  (syntax-rules (else guard)
    ((pmatch-aux name (rator rand ...) cs ...)
     (let ((v (rator rand ...)))     ; avoid multiple evals
       (pmatch-aux name v cs ...)))
    ((pmatch-aux name v)  ; no more clauses
     (if 'name
         (error 'pmatch "pmatch failed" 'name v)
         (error 'pmatch "pmatch failed" v)))
    ((pmatch-aux _ _ (else e0 e ...)) (begin e0 e ...))
    ((pmatch-aux name v (pat (guard g ...) e0 e ...) cs ...)
     (let ((fk (lambda () (pmatch-aux name v cs ...))))
       (ppat v pat (if (and g ...) (begin e0 e ...) (fk)) (fk))))
    ((pmatch-aux name v (pat e0 e ...) cs ...)
     (let ((fk (lambda () (pmatch-aux name v cs ...))))
       (ppat v pat (begin e0 e ...) (fk))))))

(define-syntax ppat
  (syntax-rules (? unquote)
    ((ppat _ ? kt _) kt)  ; the ? wildcard always matches
    ((ppat v () kt kf) (if (null? v) kt kf))
;   ((ppat v (quote lit) kt kf) (if (equal? v (quote lit)) kt kf))
    ((ppat v (unquote var) kt _) (let ((var v)) kt))
    ((ppat v (x . y) kt kf)
     (if (pair? v)
       (let ((vx (car v)) (vy (cdr v)))
	 (ppat vx x (ppat vy y kt kf) kf))
       kf))
    ((ppat v lit kt kf) (if (equal? v (quote lit)) kt kf))))
