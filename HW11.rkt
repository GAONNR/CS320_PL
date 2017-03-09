#lang plai-typed

(define-type EXPR
  [num (n : number)]
  [bool (b : boolean)]
  [add (lhs : EXPR)
       (rhs : EXPR)]
  [sub (lhs : EXPR)
       (rhs : EXPR)]
  [equ (lhs : EXPR)
       (rhs : EXPR)]
  [id (name : symbol)]
  [fun (param : (listof symbol))
       (paramty : (listof TE))
       (body : EXPR)]
  [app (fun-expr : EXPR)
       (arg-expr : (listof EXPR))]
  [ifthenelse (test-expr : EXPR)
              (then-expr : EXPR)
              (else-expr : EXPR)]
  [rec (name : symbol)
       (ty : TE)
       (named-expr : EXPR)
       (body : EXPR)]
  [with-type (name : symbol)
             (var1-name : symbol) (var1-ty : TE)
             (var2-name : symbol) (var2-ty : TE)
             (body-expr : EXPR)]
  [cases (name : symbol)
         (dispatch-expr : EXPR)
         (var1-expr : symbol) (bind1-name : symbol) (rhs1-expr : EXPR)
         (var2-name : symbol) (bind2-name : symbol) (rhs2-expr : EXPR)])

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (params : (listof TE)) (result : TE)]
  [idTE (name : symbol)])

(define-type Type
  [numT]
  [boolT]
  [arrowT (params : (listof Type)) (result : Type)]
  [idT (name : symbol)])

(define-type EXPR-Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closureV (param : (listof symbol)) (body : EXPR) (ds : DefrdSub)]
  [variantV (right? : boolean) (val : EXPR-Value)]
  [constructorV (right? : boolean)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)]
  [tBind (name : symbol)
         (var1-name : symbol) (var1-type : Type)
         (var2-name : symbol) (var2-type : Type)
         (rest : TypeEnv)])

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol)
        (value : EXPR-Value)
        (rest : DefrdSub)]
  [aRecSub (name : symbol)
           (value-box : (boxof EXPR-Value))
           (ds : DefrdSub)])

;; ----------------------------------------

(define (makeaSubs params vals ds)
  (cond
    [(empty? params) ds]
    [else (makeaSubs (rest params) (rest vals)
                     (aSub (first params) (first vals) ds))]))

;; interp : EXPRDefrdSub -> EXPR-Value
(define (interp expr ds)
  (type-case EXPR expr
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (name) (lookup name ds)]
    [fun (params param-te body-expr)
         (closureV params body-expr ds)]
    [app (fun-expr arg-exprs)
         (local [(define fun-val (interp fun-expr ds))
                 (define arg-vals (map (lambda (arg-expr) (interp arg-expr ds)) arg-exprs))]
           (type-case EXPR-Value fun-val
             [closureV (param body ds)
                       (interp body (makeaSubs
                                     param arg-vals ds))]
             [constructorV (right?)
                           (variantV right? (first arg-vals))]
             [else (error 'interp "not applicable")]))]
    [cases (ty dispatch-expr
               var1-name var1-id var1-rhs
               var2-name var2-id var2-rhs)
      (type-case EXPR-Value (interp dispatch-expr ds)
        [variantV (right? val)
                  (if (not right?)
                      (interp var1-rhs (aSub var1-id val ds))
                      (interp var2-rhs (aSub var2-id val ds)))]
        [else (error 'interp "not a variant result")])]
    [bool (t) (boolV t)]
    [equ (l r) (if (equal? (interp l ds) (interp r ds))
                  (boolV true)
                  (boolV false))]
    [ifthenelse (t f s) (if (equal? (interp t ds) (boolV true))
                            (interp f ds)
                            (interp s ds))]
   ;[with (names nametys inits body)
   ;      (interp body
   ;              (makeaSubs names inits ds handler) handler)]
    [rec (bound-id type named-expr body-expr)
         (local [(define value-holder (box (numV 42)))
                 (define new-ds
                         (aRecSub bound-id value-holder ds))]
           (begin
             (set-box! value-holder (interp named-expr new-ds))
             (interp body-expr new-ds)))]
    [with-type (type-name var1-name var1-te
                          var2-name var2-te
                          body-expr)
               (interp body-expr
                       (aSub var1-name
                             (constructorV false)
                             (aSub var2-name
                                   (constructorV true)
                                   ds)))]
    ))

;; num-op : (number number -> number) -> (EXPR-Value EXPR-Value -> EXPR-Value)
(define (num-op op x y)
  (numV (op (numV-n x) (numV-n y))))

(define (num+ x y) (num-op + x y))
(define (num- x y) (num-op - x y))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-ds)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-ds))]
    [aRecSub (sub-name num-box rest-ds)
             (if (symbol=? sub-name name)
                 (unbox num-box)
                 (lookup name rest-ds))]))

;; ----------------------------------------

(define (get-type name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable, so no type")]
    [aBind (name ty rest)
           (if (symbol=? name-to-find name)
               ty
               (get-type name-to-find rest))]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (get-type name-to-find rest)]))

;; ----------------------------------------

(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [arrowTE (a b) (arrowT (map (lambda (arg) (parse-type arg)) a)
                           (parse-type b))]
    [idTE (s) (idT s)]))

(define (type-error EXPR msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string EXPR)
                      (string-append " not "
                                     msg)))))

(define (makeaBinds names params-type env)
  (cond
    [(empty? names) env]
    [else
     (makeaBinds (rest names) (rest params-type)
      (aBind (first names) (first params-type) env))]))

(define (typelistcheck param-types arg-types)
  (cond
    [(empty? param-types) #t]
    [else
     (if (equal? (first param-types) (first arg-types))
         (typelistcheck (rest param-types) (rest arg-types))
         #f)]))

(define (decidetype f s env)
  (local
    [(define first-type (typecheck f env))
     (define second-type (typecheck s env))]
    (cond
      [(equal? first-type second-type) first-type]
      [else
       (type-case Type first-type
         [arrowT (flist ftype)
                 (type-case Type second-type
                   [arrowT (slist stype)
                           (whenArrowPair first-type second-type)]
                   [else (type-error f "same type")])]
         [else (type-error f "same type")])])))

(define (whenArrowPair f s)
  (local [(define flist (arrowT-params f))
          (define ftype (arrowT-result f))
          (define slist (arrowT-params s))
          (define stype (arrowT-result s))]
    (arrowT (makenewlist flist slist) ftype)))

(define (makenewlist flist slist)
  (cond
    [(empty? flist) empty]
    [else
     (cons (first flist) (makenewlist (rest flist) (rest slist)))]))

(define typecheck : (EXPR TypeEnv -> Type)
  (lambda (expr env)
    (type-case EXPR expr
      [num (n) (numT)]
      [add (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [else (type-error r "num")])]
                   [else (type-error l "num")])]
      [sub (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [else (type-error r "num")])]
                   [else (type-error l "num")])]
      [id (name) (get-type name env)]
      [fun (names tes body)
           (local [(define param-types (map (lambda (te) (parse-type te)) tes))]
             (begin
               (validtype-list param-types env)
               (arrowT param-types
                       (typecheck body (makeaBinds names
                                                   param-types
                                                   env)))))]
      [app (fn args)
           (type-case Type (typecheck fn env)
             [arrowT (param-types result-type)
                     (if (typelistcheck param-types
                                        (map (lambda (arg) (typecheck arg env)) args))
                         result-type
                         (type-error args
                                     (to-string param-types)))]
             [else (type-error fn "function")])]
      [bool (f) (boolT)]
      [equ (l r) (type-case Type (typecheck l env)
                  [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (boolT)]
                           [else (type-error r "num")])]
                  [else (type-error l "num")])]
      [ifthenelse (t f s)
                  (local [(define exp1-type (typecheck t env))]
                    (type-case Type exp1-type
                      [boolT () (decidetype f s env)]
                      [else (type-error t "boolean")]))]
      [rec (name ty rhs-expr body-expr)
           (local [(define rhs-ty (parse-type ty))
                   (define new-env (aBind name rhs-ty env))]
             (if (equal? rhs-ty (typecheck rhs-expr new-env))
                 (typecheck body-expr new-env)
                 (type-error rhs-expr (to-string rhs-ty))))]
      [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
                 (local [(define var1-ty (parse-type var1-te))
                         (define var2-ty (parse-type var2-te))
                         (define new-env (tBind type-name
                                                var1-name var1-ty
                                                var2-name var2-ty env))]
                   (begin
                     (validtype var1-ty new-env)
                     (validtype var2-ty new-env)
                     (typecheck body-expr
                                (aBind var1-name
                                       (arrowT (cons var1-ty empty)
                                               (idT type-name))
                                       (aBind var2-name
                                              (arrowT (cons var2-ty empty)
                                                      (idT type-name))
                                              new-env)))))]
      [cases (type-name dispatch-expr var1-name var1-id var1-rhs
                        var2-name var2-id var2-rhs)
        (local [(define bind (find-type-id type-name env))]
          (if (and (equal? var1-name (tBind-var1-name bind))
                   (equal? var2-name (tBind-var2-name bind)))
              (type-case Type (typecheck dispatch-expr env)
                [idT (name)
                     (if (equal? name type-name)
                         (local [(define rhs1-ty
                                   (typecheck var1-rhs
                                              (aBind var1-id (tBind-var1-type bind) env)))
                                 (define rhs2-ty
                                   (typecheck var2-rhs
                                              (aBind var2-id (tBind-var2-type bind) env)))]
                           (if (equal? rhs1-ty rhs2-ty)
                               rhs1-ty
                               (type-error var2-rhs (to-string rhs1-ty))))
                         (type-error dispatch-expr (to-string type-name)))]
                [else (type-error dispatch-expr (to-string type-name))])
              (type-error expr "matching variant names")))]
      )))

(define (validtype ty env)
  (type-case Type ty
    [boolT () (mtEnv)]
    [numT () (mtEnv)]
    [arrowT (a b) (begin (validtype-list a env)
                         (validtype b env))]
    [idT (id) (find-type-id id env)]))

(define (validtype-list tys env)
  (cond
    [(empty? tys) (mtEnv)]
    [else (begin
            (validtype (first tys) env)
            (validtype-list (rest tys) env))]))

(define (find-type-id name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free type name, so no type")]
    [aBind (name ty rest)
           (find-type-id name-to-find rest)]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (if (symbol=? name-to-find name)
               env
               (find-type-id name-to-find rest))]))

;; ----------------------------------------
(define run : (EXPR -> EXPR-Value)
  (lambda (expr)
    (interp expr (mtSub))))

(define eval : (EXPR -> EXPR-Value)
  (lambda (expr)
    (begin
      (try (typecheck expr (mtEnv))
           (lambda () (error 'type-error "typecheck")))
      (run expr))))

;; ----------------------------------------

(test (interp (rec 'fib (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
                   (fun (list 'n 'a 'b) (list (numTE) (numTE) (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (id 'a)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (id 'b)
                                  (app (id 'fib) (list (sub (id 'n) (num 1)) (id 'b) (add (id 'a) (id 'b)))))))
                   (app (id 'fib) (list (num 6) (num 1) (num 1))))
                 (mtSub)) (numV 13))

(test (interp (rec 'onlyzero (arrowTE (list (numTE)) (numTE))
                (fun (list 'n) (list (numTE))
                     (ifthenelse (equ (num 0) (id 'n))
                                 (id 'n)
                                 (app (id 'onlyzero) (list (sub (id 'n) (num 1))))))
                (app (id 'onlyzero) (list (num 6)))) (mtSub)) (numV 0))

(test (typecheck (rec 'onlyzero (arrowTE (list (numTE)) (numTE))
                (fun (list 'n) (list (numTE))
                     (ifthenelse (equ (num 0) (id 'n))
                                 (id 'n)
                                 (app (id 'onlyzero) (list (sub (id 'n) (num 1))))))
                (app (id 'onlyzero) (list (num 8)))) (mtEnv)) (numT))

(test (interp
  (with-type 'ops
    'adder (numTE)
    'subber (numTE)
    (app
       (fun (list 'f 'a) (list (idTE 'ops) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (id 'x) (id 'a))
            'ifer 'x (sub (id 'x) (id 'a))))
       (list (app (id 'adder) (list (num 4))) (num 5))))
  (mtSub)) (numV 9))

(test (interp
  (with-type 'ops
    'adder (numTE)
    'subber (numTE)
    (app
       (fun (list 'f 'a) (list (idTE 'ops) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (id 'x) (id 'a))
            'ifer 'x (sub (id 'x) (id 'a))))
       (list (app (id 'subber) (list (num 3))) (num 5))))
  (mtSub)) (numV -2))
;; ----------------------------------------
(test (typecheck (rec 'fib (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
                   (fun (list 'n 'a 'b) (list (numTE) (numTE) (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (id 'a)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (id 'b)
                                  (app (id 'fib) (list (sub (id 'n) (num 1)) (id 'b) (add (id 'a) (id 'b)))))))
                   (app (id 'fib) (list (num 7) (num 0) (num 1))))
                 (mtEnv)) (numT))
(test (interp (rec 'sum (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 0)
                             (add (id 'n) (app (id 'sum) (list (sub (id 'n) (num 1)))))))
                   (app (id 'sum) (list (num 5))))
                 (mtSub))
      (numV 15))
(test (interp (rec 'sum (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 0)
                             (add (id 'n) (app (id 'sum) (list (sub (id 'n) (num 1)))))))
                   (app (id 'sum) (list (num 10))))
                 (mtSub))
      (numV 55))



(test (interp (rec 'fib (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 1)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (num 1)
                                  (add (app (id 'fib) (list (sub (id 'n) (num 1))))
                                       (app (id 'fib) (list (sub (id 'n) (num 2))))))))
                   (app (id 'fib) (list (num 5))))
                 (mtSub)) (numV 8))
(test (interp (rec 'fib (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 1)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (num 1)
                                  (add (app (id 'fib) (list (sub (id 'n) (num 1))))
                                       (app (id 'fib) (list (sub (id 'n) (num 2))))))))
                   (app (id 'fib) (list (num 6))))
                 (mtSub)) (numV 13))
(test (typecheck (rec 'sum (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 0)
                             (add (id 'n) (app (id 'sum) (list (sub (id 'n) (num 1)))))))
                   (app (id 'sum) (list (num 10))))
                 (mtEnv))
      (numT))

(test (typecheck (rec 'fib (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 1)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (num 1)
                                  (add (app (id 'fib) (list (sub (id 'n) (num 1))))
                                       (app (id 'fib) (list (sub (id 'n) (num 2))))))))
                   (app (id 'fib) (list (num 5))))
                 (mtEnv)) (numT))
(test (typecheck (rec 'sum (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 0)
                             (add (id 'n) (app (id 'sum) (list (sub (id 'n) (num 1)))))))
                   (app (id 'sum) (list (num 10))))
                 (mtEnv))
      (numT))

(test (interp (rec 'sum (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 0)
                             (add (id 'n) (app (id 'sum) (list (sub (id 'n) (num 1)))))))
                   (app (id 'sum) (list (num 5))))
                 (mtSub))
      (numV 15))
(test (interp (rec 'sum (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 0)
                             (add (id 'n) (app (id 'sum) (list (sub (id 'n) (num 1)))))))
                   (app (id 'sum) (list (num 10))))
                 (mtSub))
      (numV 55))



(test (typecheck (rec 'fib (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 1)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (num 1)
                                  (add (app (id 'fib) (list (sub (id 'n) (num 1))))
                                       (app (id 'fib) (list (sub (id 'n) (num 2))))))))
                   (app (id 'fib) (list (num 5))))
                 (mtEnv)) (numT))

(test (interp (rec 'fib (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 1)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (num 1)
                                  (add (app (id 'fib) (list (sub (id 'n) (num 1))))
                                       (app (id 'fib) (list (sub (id 'n) (num 2))))))))
                   (app (id 'fib) (list (num 5))))
                 (mtSub)) (numV 8))
(test (interp (rec 'fib (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 1)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (num 1)
                                  (add (app (id 'fib) (list (sub (id 'n) (num 1))))
                                       (app (id 'fib) (list (sub (id 'n) (num 2))))))))
                   (app (id 'fib) (list (num 6))))
                 (mtSub)) (numV 13))



(test (interp (rec 'fib (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
                   (fun (list 'n 'a 'b) (list (numTE) (numTE) (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (id 'a)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (id 'b)
                                  (app (id 'fib) (list (sub (id 'n) (num 1)) (id 'b) (add (id 'a) (id 'b)))))))
                   (app (id 'fib) (list (num 5) (num 0) (num 1))))
                 (mtSub)) (numV 5))
(test (interp (rec 'fib (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
                   (fun (list 'n 'a 'b) (list (numTE) (numTE) (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (id 'a)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (id 'b)
                                  (app (id 'fib) (list (sub (id 'n) (num 1)) (id 'b) (add (id 'a) (id 'b)))))))
                   (app (id 'fib) (list (num 7) (num 0) (num 1))))
                 (mtSub)) (numV 13))


(test (typecheck (rec 'fib (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
                   (fun (list 'n 'a 'b) (list (numTE) (numTE) (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (id 'a)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (id 'b)
                                  (app (id 'fib) (list (sub (id 'n) (num 1)) (id 'b) (add (id 'a) (id 'b)))))))
                   (app (id 'fib) (list (num 7) (num 0) (num 1))))
                 (mtEnv)) (numT))

(test (typecheck
  (with-type 'outer
    'outerA (numTE)
    'outerB (numTE)
    (with-type 'inner
      'innerA (numTE)
        'innerB (arrowTE (list (numTE)) (numTE))
	    (app
		  (fun (list 'o 'i) (list (idTE 'outer) (idTE 'inner))
	           (cases 'outer (id 'o)
	   	  	   'outerA 'x
			    (cases 'inner (id 'i)
	    	   	        'innerA 'y (id 'x)
			         'innerB 'y (app (id 'y) (list (id 'x)))
	 	        )
			   'outerB 'x (id 'x)))
	   	     (list (app (id 'outerA) (list (num 5))) (app (id 'innerA) (list (num 10))))
     	   )))
  (mtEnv)) (numT))

(test (interp
  (with-type 'outer
    'outerA (numTE)
    'outerB (numTE)
    (with-type 'inner
      'innerA (numTE)
        'innerB (arrowTE (list (numTE)) (numTE))
	    (app
		  (fun (list 'o 'i) (list (idTE 'outer) (idTE 'inner))
	           (cases 'outer (id 'o)
	   	  	   'outerA 'x
			    (cases 'inner (id 'i)
	    	   	        'innerA 'y (id 'x)
			         'innerB 'y (app (id 'y) (list (id 'x)))
	 	        )
		   'outerB 'x (id 'x)))
   	     (list (app (id 'outerA) (list (num 5))) (app (id 'innerA) (list (num 10))))
     	   )))
  (mtSub)) (numV 5))

(test (interp
  (with-type 'outer
    'outerA (numTE)
    'outerB (numTE)
    (with-type 'inner
      'innerA (numTE)
        'innerB (arrowTE (list (numTE)) (numTE))
	    (app
		  (fun (list 'o 'i) (list (idTE 'outer) (idTE 'inner))
	           (cases 'outer (id 'o)
	   	  	   'outerA 'x
			    (cases 'inner (id 'i)
	    	   	        'innerA 'y (id 'x)
			         'innerB 'y (app (id 'y) (list (id 'x)))
	 	        )
	   'outerB 'x (id 'x)))
     (list (app (id 'outerA) (list (num 5))) (app (id 'innerB) (list (fun (list 'a) (list (numTE)) (sub (num 0) (id 'a))))))
   )))
  (mtSub)) (numV -5))

(test (typecheck
  (with-type 'outer
    'outerA (numTE)
    'outerB (numTE)
    (with-type 'inner
      'innerA (numTE)
        'innerB (arrowTE (list (numTE)) (numTE))
	    (app
		  (fun (list 'o 'i) (list (idTE 'outer) (idTE 'inner))
	           (cases 'outer (id 'o)
	   	  	   'outerA 'x
			    (cases 'inner (id 'i)
	    	   	        'innerA 'y (id 'x)
			         'innerB 'y (app (id 'y) (list (id 'x)))
		 	        )
	   'outerB 'x (id 'x)))
    (list (app (id 'outerA) (list (num 5))) (app (id 'innerA) (list (num 10))))
  )))
  (mtEnv)) (numT))

(test (interp
  (with-type 'outer
    'outerA (numTE)
    'outerB (numTE)
    (with-type 'inner
      'innerA (numTE)
        'innerB (arrowTE (list (numTE)) (numTE))
	    (app
		  (fun (list 'o 'i) (list (idTE 'outer) (idTE 'inner))
	           (cases 'outer (id 'o)
	   	  	   'outerA 'x
			    (cases 'inner (id 'i)
	    	   	        'innerA 'y (id 'x)
			         'innerB 'y (app (id 'y) (list (id 'x)))
		 	        )
	   'outerB 'x (id 'x)))
     (list (app (id 'outerA) (list (num 5))) (app (id 'innerA) (list (num 10))))
  )))
  (mtSub)) (numV 5))

(test (interp
  (with-type 'outer
    'outerA (numTE)
    'outerB (numTE)
    (with-type 'inner
      'innerA (numTE)
        'innerB (arrowTE (list (numTE)) (numTE))
	    (app
		  (fun (list 'o 'i) (list (idTE 'outer) (idTE 'inner))
	           (cases 'outer (id 'o)
	   	  	   'outerA 'x
			    (cases 'inner (id 'i)
	    	   	        'innerA 'y (id 'x)
			         'innerB 'y (app (id 'y) (list (id 'x)))
 	        )
	   'outerB 'x (id 'x)))
    (list (app (id 'outerA) (list (num 5))) (app (id 'innerB) (list (fun (list 'a) (list (numTE)) (sub (num 0) (id 'a))))))
  )))
  (mtSub)) (numV -5))

(test (typecheck
  (with-type 'ops
    'adder (arrowTE (list (numTE) (numTE)) (numTE))
    'ifer (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
    (app
       (fun (list 'f 'a 'b 'c) (list (idTE 'ops) (numTE) (numTE) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (app (id 'x) (list (id 'a) (id 'b))) (id 'c))
            'ifer 'x (app (id 'x) (list (id 'a) (id 'b) (id 'c)))))
       (list (app (id 'adder) (list (fun (list 'a 'b) (list (numTE) (numTE)) (add (id 'a) (id 'b))))) (num 4) (num 5) (num 6))))
  (mtEnv)) (numT))

(test (typecheck
  (with-type 'ops
    'adder (arrowTE (list (numTE) (numTE)) (numTE))
    'ifer (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
    (app
       (fun (list 'f 'a 'b 'c) (list (idTE 'ops) (numTE) (numTE) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (app (id 'x) (list (id 'a) (id 'b))) (id 'c))
            'ifer 'x (app (id 'x) (list (id 'a) (id 'b) (id 'c)))))
       (list (app (id 'ifer) (list (fun (list 'a 'b 'c) (list (numTE) (numTE) (numTE))
        (ifthenelse (equ (num 0) (id 'a))
         (id 'b) (id 'c))))) (num 0) (num 2) (num 4))))
  (mtEnv)) (numT))


(test (interp
  (with-type 'ops
    'adder (arrowTE (list (numTE) (numTE)) (numTE))
    'ifer (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
    (app
       (fun (list 'f 'a 'b 'c) (list (idTE 'ops) (numTE) (numTE) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (app (id 'x) (list (id 'a) (id 'b))) (id 'c))
            'ifer 'x (app (id 'x) (list (id 'a) (id 'b) (id 'c)))))
       (list (app (id 'adder) (list (fun (list 'a 'b) (list (numTE) (numTE)) (add (id 'a) (id 'b))))) (num 4) (num 5) (num 6))))
  (mtSub)) (numV 15))

(test (interp
  (with-type 'ops
    'adder (arrowTE (list (numTE) (numTE)) (numTE))
    'ifer (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
    (app
       (fun (list 'f 'a 'b 'c) (list (idTE 'ops) (numTE) (numTE) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (app (id 'x) (list (id 'a) (id 'b))) (id 'c))
            'ifer 'x (app (id 'x) (list (id 'a) (id 'b) (id 'c)))))
       (list (app (id 'ifer) (list (fun (list 'a 'b 'c) (list (numTE) (numTE) (numTE))
       (ifthenelse (equ (num 0) (id 'a))
        (id 'b) (id 'c))))) (num 0) (num 2) (num 4))))
  (mtSub)) (numV 2))

(test (interp
  (with-type 'ops
    'adder (arrowTE (list (numTE) (numTE)) (numTE))
    'ifer (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
    (app
       (fun (list 'f 'a 'b 'c) (list (idTE 'ops) (numTE) (numTE) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (app (id 'x) (list (id 'a) (id 'b))) (id 'c))
            'ifer 'x (app (id 'x) (list (id 'a) (id 'b) (id 'c)))))
       (list (app (id 'ifer) (list (fun (list 'a 'b 'c) (list (numTE) (numTE) (numTE))
        (ifthenelse (equ (num 0) (id 'a)) (id 'b) (id 'c))))) (num 1) (num 3) (num 5))))
  (mtSub)) (numV 5))
(test (typecheck
  (with-type 'pet
    'cat (numTE)
    'dog (numTE)
    (app
      (fun (list 'a) (list (idTE 'pet))
        (cases 'pet (id 'a)
          'cat 'x (sub (num 0) (id 'x))
          'dog 'x (id 'x)))
      (list (app (id 'cat) (list(num 5))))))
  (mtEnv)) (numT))

(test (interp
  (with-type 'pet
    'cat (numTE)
    'dog (numTE)
    (app
      (fun (list 'a) (list (idTE 'pet))
        (cases 'pet (id 'a)
          'cat 'x (sub (num 0) (id 'x))
          'dog 'x (id 'x)))
      (list (app (id 'cat) (list(num 5))))))
  (mtSub)) (numV -5))

(test (typecheck
  (with-type 'ops
    'adder (arrowTE (list (numTE) (numTE)) (numTE))
    'ifer (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
    (app
       (fun (list 'f 'a 'b 'c) (list (idTE 'ops) (numTE) (numTE) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (app (id 'x) (list (id 'a) (id 'b))) (id 'c))
            'ifer 'x (app (id 'x) (list (id 'a) (id 'b) (id 'c)))))
       (list (app (id 'adder) (list (fun (list 'a 'b) (list (numTE) (numTE)) (add (id 'a) (id 'b))))) (num 4) (num 5) (num 6))))
  (mtEnv)) (numT))

(test (typecheck
  (with-type 'ops
    'adder (arrowTE (list (numTE) (numTE)) (numTE))
    'ifer (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
    (app
       (fun (list 'f 'a 'b 'c) (list (idTE 'ops) (numTE) (numTE) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (app (id 'x) (list (id 'a) (id 'b))) (id 'c))
            'ifer 'x (app (id 'x) (list (id 'a) (id 'b) (id 'c)))))
       (list (app (id 'ifer) (list (fun (list 'a 'b 'c) (list (numTE) (numTE) (numTE))
       (ifthenelse (equ (num 0) (id 'a)) (id 'b) (id 'c))))) (num 0) (num 2) (num 4))))
  (mtEnv)) (numT))

(test (interp
  (with-type 'ops
    'adder (arrowTE (list (numTE) (numTE)) (numTE))
    'ifer (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
    (app
       (fun (list 'f 'a 'b 'c) (list (idTE 'ops) (numTE) (numTE) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (app (id 'x) (list (id 'a) (id 'b))) (id 'c))
            'ifer 'x (app (id 'x) (list (id 'a) (id 'b) (id 'c)))))
       (list (app (id 'adder) (list (fun (list 'a 'b) (list (numTE) (numTE)) (add (id 'a) (id 'b))))) (num 4) (num 5) (num 6))))
  (mtSub)) (numV 15))

(test (interp
  (with-type 'ops
    'adder (arrowTE (list (numTE) (numTE)) (numTE))
    'ifer (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
    (app
       (fun (list 'f 'a 'b 'c) (list (idTE 'ops) (numTE) (numTE) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (app (id 'x) (list (id 'a) (id 'b))) (id 'c))
            'ifer 'x (app (id 'x) (list (id 'a) (id 'b) (id 'c)))))
       (list (app (id 'ifer) (list (fun (list 'a 'b 'c) (list (numTE) (numTE) (numTE))
       (ifthenelse (equ (num 0) (id 'a)) (id 'b) (id 'c))))) (num 0) (num 2) (num 4))))
  (mtSub)) (numV 2))

(test (interp
  (with-type 'ops
    'adder (arrowTE (list (numTE) (numTE)) (numTE))
    'ifer (arrowTE (list (numTE) (numTE) (numTE)) (numTE))
    (app
       (fun (list 'f 'a 'b 'c) (list (idTE 'ops) (numTE) (numTE) (numTE))
          (cases 'ops (id 'f)
            'adder 'x (add (app (id 'x) (list (id 'a) (id 'b))) (id 'c))
            'ifer 'x (app (id 'x) (list (id 'a) (id 'b) (id 'c)))))
       (list (app (id 'ifer) (list (fun (list 'a 'b 'c) (list (numTE) (numTE) (numTE))
       (ifthenelse (equ (num 0) (id 'a)) (id 'b) (id 'c))))) (num 1) (num 3) (num 5))))
  (mtSub)) (numV 5))
(test
 (interp
  (with-type 'fruit
             'apple (numTE)
             'banana (arrowTE (list (numTE)) (numTE))
             (rec 'len
               (arrowTE (list (numTE)) (numTE))
               (fun (list 'l)
                    (list (idTE 'fruit))
                    (cases 'fruit (id 'l)
                      'apple 'a (num 0)
                      'banana 'n (num 3)))
               (id 'banana)))
  (mtSub))
 (constructorV #t))



(test
 (interp
  (with-type 'fruit
             'apple (numTE)
             'banana (arrowTE (list (numTE)) (numTE))
             (rec 'len
               (arrowTE (list (numTE)) (numTE))
               (fun (list 'l)
                    (list (idTE 'fruit))
                    (cases 'fruit (id 'l)
                      'apple 'a (num 0)
                      'banana 'n (num 3)))
               (app (id 'apple) (list (num 2)))))
  (mtSub))
 (variantV #f (numV 2)))

(test
 (interp
  (rec 'a
    (arrowTE (list (numTE)) (numTE))
    (fun (list 'l)
         (list (numTE))
         (num 1))
    (rec 'b
      (arrowTE (list (numTE)) (numTE))
      (fun (list 'c)
           (list (numTE))
           (num 2))
      (app (id 'b) (list (num 10)))))
  (mtSub))
 (numV 2))




(test
 (interp
  (with-type 'fruit
             'apple (numTE)
             'banana (arrowTE (list (numTE)) (numTE))
             (rec 'len
               (arrowTE (list (numTE)) (numTE))
               (fun (list 'l)
                    (list (idTE 'fruit))
                    (cases 'fruit (id 'l)
                      'apple 'a (num 0)
                      'banana 'n (num 3)))
               (app (id 'banana) (list (num 2)))))
  (mtSub))
 (variantV #t (numV 2)))

(test (interp (with-type 'fruit 'apple (numTE)
                         'banana (arrowTE (list (numTE)) (numTE))
                         (app (id 'apple) (list (num 10))))
              (mtSub))
      (variantV false (numV 10)))

(test (interp (with-type 'fruit 'apple (numTE)
                         'banana (arrowTE (list (numTE)) (numTE))
                         (cases 'fruit (app (id 'apple) (list (num 10)))
                           'apple 'y (add (id 'y) (num 1))
                           'banana 'x (app (id 'x) (list (num 10)))))
              (mtSub))
      (numV 11))

(test (interp (with-type 'fruit 'apple (numTE)
                         'banana (arrowTE (list (numTE)) (numTE))
                         (cases 'fruit (app (id 'banana) (list (fun (list 'x) (list (numTE)) (num 3))))
                           'apple 'y (add (id 'y) (num 1))
                           'banana 'x (app (id 'x) (list (num 10)))))
              (mtSub))
      (numV 3))

(test (typecheck (with-type 'fruit 'apple (numTE)
                            'banana (arrowTE (list (numTE)) (numTE))
                            (app (id 'apple) (list (num 10))))
                 (mtEnv))
      (idT 'fruit))

(test (typecheck (with-type 'fruit 'apple (numTE)
                            'banana (arrowTE (list (numTE)) (numTE))
                            (fun (list 'x) (list (idTE 'fruit)) (num 10)))
                 (mtEnv))
      (arrowT (list (idT 'fruit)) (numT)))


(test (interp (ifthenelse (equ (num 0) (num 2)) (num 3) (num 1)) (mtSub)) (numV 1))
(test (interp (ifthenelse (equ (num 0) (num 0)) (num 3) (num 1)) (mtSub)) (numV 3))

(test (typecheck (ifthenelse (equ (num 0) (num 2)) (num 3) (num 1)) (mtEnv)) (numT))

(test (typecheck (with-type 'fruit 'apple (numTE)
                         'banana (arrowTE (list (numTE)) (numTE))
                         (cases 'fruit (app (id 'banana) (list (fun (list 'x) (list (numTE)) (num 3))))
                           'apple 'y (add (id 'y) (num 1))
                           'banana 'x (app (id 'x) (list (num 10)))))
              (mtEnv))
      (numT))

(test (interp (with-type 'fruit 'apple (numTE) 'banana (numTE)
                 (cases 'fruit (app (id 'apple) (list (num 42)))
                   'apple 'x (add (id 'x)(num 1))
                   'banana 'y (add (id 'y)(num 2)))) (mtSub)) (numV 43))
(test (interp (with-type 'fruit 'apple (numTE) 'banana (numTE)
                 (cases 'fruit (app (id 'banana) (list (num 42)))
                   'apple 'x (add (id 'x)(num 1))
                   'banana 'y (add (id 'y)(num 2)))) (mtSub)) (numV 44))
(test (typecheck (with-type 'fruit 'apple (numTE) 'banana (numTE)
                 (cases 'fruit (app (id 'apple) (list (num 42)))
                   'apple 'x (add (id 'x)(num 1))
                   'banana 'y (add (id 'y)(num 2)))) (mtEnv)) (numT))
(test (typecheck (with-type 'fruit 'apple (numTE) 'banana (numTE)
                 (cases 'fruit (app (id 'banana) (list (num 42)))
                   'apple 'x (add (id 'x)(num 1))
                   'banana 'y (add (id 'y)(num 2)))) (mtEnv)) (numT))
(test (parse-type (idTE 'x)) (idT 'x))

(test (interp (with-type 'fruit 'apple (numTE)
                         'banana (arrowTE (list (numTE)) (numTE))
                         (app (id 'apple) (list (num 10))))
              (mtSub))
      (variantV false (numV 10)))

(test (interp (with-type 'fruit 'apple (numTE)
                         'banana (arrowTE (list (numTE)) (numTE))
                         (cases 'fruit (app (id 'apple) (list (num 10)))
                           'apple 'y (add (id 'y) (num 1))
                           'banana 'x (app (id 'x) (list (num 10)))))
              (mtSub))
      (numV 11))

(test (typecheck (with-type 'fruit 'apple (numTE)
                            'banana (arrowTE (list (numTE)) (numTE))
                            (app (id 'apple) (list (num 10))))
                 (mtEnv))
      (idT 'fruit))

(test (typecheck (with-type 'fruit 'apple (numTE)
                            'banana (arrowTE (list (numTE)) (numTE))
                            (fun (list 'x) (list (idTE 'fruit)) (num 10)))
                 (mtEnv))
      (arrowT (list (idT 'fruit)) (numT)))

(test (typecheck (rec 'sum (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 0)
                             (add (id 'n) (app (id 'sum) (list (sub (id 'n) (num 1)))))))
                   (app (id 'sum) (list (num 10))))
                 (mtEnv))
      (numT))

(test (typecheck (rec 'fib (arrowTE (list (numTE)) (numTE))
                   (fun (list 'n) (list (numTE))
                        (ifthenelse (equ (num 0) (id 'n))
                             (num 1)
                             (ifthenelse (equ (num 0) (sub (id 'n) (num 1)))
                                  (num 1)
                                  (add (app (id 'fib) (list (sub (id 'n) (num 1))))
                                       (app (id 'fib) (list (sub (id 'n) (num 2))))))))
                   (app (id 'fib) (list (num 5))))
                 (mtEnv)) (numT))

