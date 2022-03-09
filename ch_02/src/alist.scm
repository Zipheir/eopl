;; Env = () | ((Var . SchemeVal) . Env)
;; Var = Sym

;; empty-env : () → Env
(define (empty-env) '())

;; extend-env : Var × SchemeVal × Env → Env
(define (extend-env var val env)
  (cons (cons var val) env))

;; apply-env : Env × Var → SchemeVal
(define (apply-env env search-var)
  (cond ((assv search-var env) => cdr)
        (else (report-no-binding-found search-var))))

(define (report-no-binding-found var)
  (error 'apply-env "no binding found" var))
