;; Diff-tree ::= (one) | (diff Diff-tree Diff-tree)

(define (one) '(one))

(define (node m n) (list 'diff m n))

(define (one? t) (equal? t '(one)))

;; 2 = 1 - (-1)
(define dt-two '(diff (one) (diff (diff (one) (one)) (one))))

(define (dtl t) (cadr t))

(define (dtr t) (caddr t))

(define (dt=? s t) (equal? s t))

(define (zero) '(diff (one) (one)))

;; [[(one)]]      = 1
;; [[(diff l r)]] = [[l]] - [[r]]
(define (from-rep n)
  (if (one? n)
      1
      (- (from-rep (dtl n)) (from-rep (dtr n)))))
