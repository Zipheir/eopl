;;;; Object-oriented language from Ch. 5 (2e)

(import (rnrs base (6))
        (rename (rnrs lists (6)) (for-all every))
        )

(include "../../../src/pmatch.scm")

;;;; Utility

(define (pair-or-null? obj)
  (or (pair? obj) (null? obj)))

(define (unfold p f g seed)
  (if (p seed)
      '()
      (cons (f seed) (unfold p f g (g seed)))))

(define (drop-while p xs)
  (cond ((null? xs) '())
        ((p (car xs)) (drop-while p (cdr xs)))
        (else xs)))

(define (concatenate xss)
  (fold-right append '() xss))

;;;; References

(define (deref ref)
  (pmatch ref
    ((a-ref ,k ,vec) (vector-ref vec k))
    (? (error 'deref "not a reference" ref))))

(define (setref! ref val)
  (pmatch ref
    ((a-ref ,k ,vec) (vector-set! vec k val))
    (? (error 'setref! "not a reference" ref))))

;;;; Expressed values

;; expval->bool : Exp-val -> Bool
(define (expval->bool val)
  (pmatch val
    ((bool-val ,b) b)
    (? (report-expval-extractor-error 'bool val))))

;; expval->num : Exp-val -> Int
(define (expval->num val)
  (pmatch val
    ((num-val ,n) n)
    (? (report-expval-extractor-error 'num val))))

;; expval->proc : Exp-val -> Proc
(define (expval->proc val)
  (pmatch val
    ((proc-val ,p) p)
    (? (report-expval-extractor-error 'proc val))))

(define (report-expval-extractor-error variant value)
  (error 'expval-extractors
         "unexpected type found"
         variant value))

(define the-unspecified-value '(num-val 27))

;;;; Procedures

(define (procedure b-var body saved-env)
  (list 'proc b-var body saved-env))

;;;; Environments

;; empty-env : () -> Env
(define (empty-env) '())

;; extend-env : List-of(Var) x List-of(Exp-val) x Env -> Env
(define (extend-env vars vals env)
  (extend-env-refs vars (list->vector vals) env))

;; extend-env-refs : List-of(Var) x Vector-of(Exp-val) x Env -> Env
(define (extend-env-refs vars refs env)
  (cons (list 'ext vars refs) env))

;; extend-env-rec : List-of(Var) x List-of(List-of(Var)) x
;;                    List-of(Exp-val) x Env -> Env
(define (extend-env-rec p-names b-varss p-bodies old-env)
  (cons (list 'ext-rec p-names b-varss p-bodies) old-env))

;; apply-env : Env x Var -> Scheme-val
(define (apply-env env search-var)
  (deref (apply-env-ref env search-var)))

;; apply-env-ref : Env x Var -> Ref
(define (apply-env-ref env search-var)
  (pmatch env
    (() (report-no-binding-found search-var))
    (((ext ,vars ,vals) . ,env*)
     (cond ((rib-find-position search-var vars) =>
            (lambda (pos) `(a-ref ,pos ,vals)))
           (else (apply-env-ref env* search-var))))
    (? (error 'apply-env-ref "invalid environment" env))))

(define (report-no-binding-found var)
  (error 'apply-env "no binding found" var))

;; rib-find-position : Var x List-of(Var) -> Int-or-false
;; Return the position of the last occurrence of var in lis,
;; or #f if var isn't found.
(define (rib-find-position var lis)
  (let loop ((last #f) (i 0) (lis lis))
    (cond ((null? lis) last)
          ((eqv? var (car lis))
           (loop i (+ i 1) (cdr lis)))
          (else (loop last (+ i 1) (cdr lis))))))

;; alist->env : List-of(Var x Scheme-val) -> Env
;; No recursive bindings.
(define (alist->env as)
  (fold-right (lambda (p env)
                (extend-env (car p) (cdr p) env))
              (empty-env)
              as))

;;;; Primitives

(define (primitive-name? sym)
  (and (memv sym '(+ - *)) #t))

;; All of these are numeric, so rands is assumed to be a
;; list of num-vals.
(define (apply-primitive sym rands)
  (let ((proc (case sym
                ((zero?) zero?)
                ((+) +)
                ((-) -)
                ((*) *))))
     (apply proc (map expval->num rands))))

;;;; Class accessors

(define (class-name->field-ids name)
  (pmatch (lookup-class name)
    ((a-class-decl ? ? ,fs ?) fs)
    (x (error 'class-name->field-ids
              "invalid class declaration"
              x))))

(define (class-name->method-decls name)
  (pmatch (lookup-class name)
    ((a-class-decl ? ? ? ,ms) ms)
    (x (error 'class-name->method-decls
              "invalid class declaration"
              x))))

(define (class-name->super-name name)
  (pmatch (lookup-class name)
    ((a-class-decl ? ,s ? ?) s)
    (x (error 'class-name->super-name
              "invalid class declaration"
              x))))

;;;; Interpreter

(define the-class-env '())

;; elaborate-class-decls! : List-of(Decl) -> ()
(define (elaborate-class-decls! c-decls)
  (set! the-class-env c-decls))

(define (lookup-class name)
  (or (find (lambda (c-decl) (eqv? name (cadr c-decl)))
            the-class-env)
      (error 'lookup-class "undeclared class" name)))

;;; Obj = Sym x Vector

;; new-object : Sym -> Obj
(define (new-object class-name)
  `(an-object ,class-name
              ,(make-vector (roll-up-field-length class-name))))

;; object-fields : Obj -> Vector
(define (object-fields obj)
  (pmatch obj
    ((an-object ? ,fs) fs)
    (? (error 'object-fields "invalid object" obj))))

;; roll-up-field-length : Sym -> Int
;; Return the total number of fields of the given class.
(define (roll-up-field-length class-name)
  (fold-left +
             0
             (unfold (lambda (c) (eqv? c 'object))
                     (lambda (c) (length (class-name->field-ids c)))
                     class-name->super-name
                     class-name)))

;; roll-up-field-ids : Sym -> List-of(Sym)
;; Accumulate a list of all of the given class's fields.
(define (roll-up-field-ids class-name)
  (concatenate
   (unfold (lambda (c) (eqv? c 'object))
           class-name->field-ids
           class-name->super-name
           class-name)))

;; object->class-name : Obj -> Sym
;; (Returns the name of the class of the first part of obj.)
(define (object->class-name obj)
  (pmatch obj
    ((an-object ,name ?) name)
    (? (error 'object->class-name "invalid object" obj))))

;; class-decl-super-name : Class-decl -> Sym
(define (class-decl-super-name c-decl)
  (pmatch c-decl
    ((a-class-decl ? ,super ? ?) super)
    (? (error 'class-decl-super-name
              "invalid class declaration"
              c-decl))))

;; find-method-and-apply : Sym x Sym x Obj x List-of(Exp) -> Exp-val
(define (find-method-and-apply m-name host-name self args)
  (letrec
   ((search
     (lambda (host)
       (cond ((eqv? host 'object)
              (error 'find-method-and-apply
                     "class object has no callable methods"
                     m-name))
             ((lookup-method-decl m-name
                                  (class-name->method-decls host)) =>
              (lambda (m-decl)
                (apply-method m-decl host-name self args)))
             (else (search (class-name->super-name host)))))))

    (search host-name)))

;; lookup-method-decl : Sym x List-of(M-decl) -> M-decl + false
(define (lookup-method-decl name method-decls)
  (find (lambda (d) (eqv? name (cadr d))) method-decls))

;; apply-method : Method-decl x Sym x Obj x List-of(Exp) -> Exp-val
(define (apply-method m-decl host-name self args)
  (pmatch m-decl
    ((a-method-decl ? ,ids ,body)
     (let* ((super-name (class-name->super-name host-name))
            (field-ids (roll-up-field-ids host-name))
            (fields (object-fields self))
            (env (extend-env
                  `(%super self . ,ids)
                  (cons* super-name self args)
                  (extend-env-refs field-ids fields (empty-env)))))
       (eval-expression body env)))
    (? (error 'apply-method "invalid method declaration" m-decl))))

;; eval-program : Program -> Exp-val
(define (eval-program pgm)
  (pmatch pgm
    ((a-program ,c-decls ,exp)
     (elaborate-class-decls! c-decls)
     (eval-expression exp (empty-env)))))

;; eval-expression : Exp x Env -> Exp-val
(define (eval-expression exp env)
  (pmatch exp
    (true-exp '(bool-val #t))
    (false-exp '(bool-val #f))
    ((const-exp ,n) (list 'num-val n))
    ((var-exp ,v) (apply-env env v))
    ((primapp-exp ,prim ,rands)
     (apply-primitive prim (eval-rands rands env)))
    ((if-exp ,test ,con ,alt)
     (if (expval->bool (eval-expression test env))
         (eval-expression con env)
         (eval-expression alt env)))
    ((let-exp ,ids ,rands ,body)
     (let ((args (eval-rands rands env)))
       (eval-expression body (extend-env ids args env))))
    ((assign-exp ,id ,rhs)
     (setref! (apply-env-ref env id) (eval-expression rhs env))
     the-unspecified-value)
    ((method-app-exp ,obj-exp ,name ,rands)
     (let ((args (eval-rands rands env))
           (obj (eval-expression obj-exp env)))
       (find-method-and-apply name (object->class-name obj) obj args)))
    ((super-call-exp ,name ,rands)
     (let ((args (eval-rands rands env))
           (obj (apply-env env 'self))
           (host (apply-env env '%super)))
       (apply-method name host obj args)))
    ((new-object-exp ,c-name ,rands)
     (let ((args (eval-rands rands env))
           (obj (new-object c-name)))
       (find-method-and-apply 'initialize c-name obj args)
       obj))
    ((begin-exp ,exps)
     (for-each (lambda (e) (eval-expression e env)) exps))
    (? (error 'eval-expression "invalid expression" exp))))

(define (eval-rands rands env)
  (map (lambda (e) (eval-expression e env)) rands))

;;;; Parser

(define (parse-program c-sexp e-sexp)
  (list 'a-program (map parse-class-decl c-sexp) (parse e-sexp)))

(define (parse-class-decl sexp)
  (pmatch sexp
    ((class ,c-name extends ,super ,fields ,methods)
     (guard (symbol? c-name)
            (symbol? super)
            (every symbol? fields))
     `(a-class-decl ,c-name
                    ,super
                    ,fields
                    ,(map parse-method methods)))
    (? (error 'parse-class-decl "invalid class declaration" sexp))))

(define (parse-method sexp)
  (pmatch sexp
    ((method ,name ,ids ,body)
     (guard (symbol? name) (every symbol? ids))
     `(a-method-decl ,name ,ids ,(parse body)))
    (? (error 'parse-method
              "invalid method declaration"
              sexp))))

(define (parse sexp)
  (pmatch sexp
    (true 'true-exp)
    (false 'false-exp)
    (,n (guard (integer? n)) `(const-exp ,n))
    (,v (guard (symbol? v)) `(var-exp ,v))
    ((if ,t ,c ,a)
     `(if-exp ,(parse t) ,(parse c) ,(parse a)))
    ((let ,binds in ,b) (parse-let-exp binds b))
    ((set ,v := ,e) (guard (symbol? v))
     `(assign-exp ,v ,(parse e)))
    ((send ,o ,m ,rs)
     (guard (symbol? m) (pair-or-null? rs))
     `(method-app-exp ,(parse o) ,m ,(map parse rs)))
    ((super ,m ,rs) (guard (symbol? m))
     `(super-call-exp ,m ,(map parse rs)))
    ((new ,c ,rs) (guard (symbol? c))
     `(new-object-exp ,c ,(map parse rs)))
    ((begin . ,exps) (guard (pair? exps))
     `(begin-exp ,(map parse exps)))
    ((,prim . ,rs)
     (guard (symbol? prim) (primitive-name? prim))
     `(primapp-exp ,prim ,(map parse rs)))
    (? (error 'parse "syntax error: invalid expression" sexp))))

;; parse-let-exp : List-of(S-exp x Sym) x S-exp -> Exp
(define (parse-let-exp binds body)
  (letrec
   ((collect
     (lambda (bs ids exps)
       (pmatch bs
         (() (values ids exps))
         (((,v = ,e) . ,bs*) (guard (symbol? v))
          (collect bs* (cons v ids) (cons (parse e) exps)))
         (? (error 'parse "syntax error" bs))))))

    (let-values (((ids exps) (collect binds '() '())))
      `(let-exp ,ids ,exps ,(parse body)))))
