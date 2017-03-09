#lang plai-typed

(define-type TFAE
  [num (n : number)]
  [add (lhs : TFAE)
       (rhs : TFAE)]
  [sub (lhs : TFAE)
       (rhs : TFAE)]
  [id (name : symbol)]
  [fun (param : symbol)
       (paramty : TE)
       (body : TFAE)]
  [app (fun-expr : TFAE)
       (arg-expr : TFAE)]
  [bool (expr : boolean)]
  [eq (lhs : TFAE)
      (rhs : TFAE)]
  [ifthenelse (expr : TFAE)
              (first : TFAE)
              (second : TFAE)]
  [pair (lhs : TFAE)
        (rhs : TFAE)]
  [fst (exp : TFAE)]
  [snd (exp : TFAE)])

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (param : TE)
           (result : TE)]
  [crossTE (left : TE)
           (right : TE)])

(define-type TFAE-Value
  [numV (n : number)]
  [closureV (param : symbol)
            (body : TFAE)
            (ds : DefrdSub)]
  [boolV (t : boolean)]
  [crossV (left : TFAE-Value)
          (right : TFAE-Value)])

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol)
        (value : TFAE-Value)
        (rest : DefrdSub)])

(define-type Type
  [numT]
  [boolT]
  [arrowT (param : Type)
          (result : Type)]
  [crossT (left : Type)
          (right : Type)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

;; ----------------------------------------

;; interp : TFAE DefrdSub -> TFAE-Value
(define (interp tfae ds)
  (type-case TFAE tfae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (name) (lookup name ds)]
    [fun (param param-te body-expr)
         (closureV param body-expr ds)]
    [app (fun-expr arg-expr)
         (local [(define fun-val (interp fun-expr ds))
                 (define arg-val (interp arg-expr ds))]
           (interp (closureV-body fun-val)
                   (aSub (closureV-param fun-val)
                         arg-val
                         (closureV-ds fun-val))))]
    [bool (t) (boolV t)]
    [eq (l r) (if (equal? (interp l ds) (interp r ds))
                  (boolV true)
                  (boolV false))]
    [ifthenelse (t f s) (if (equal? (interp t ds) (boolV true))
                            (interp f ds)
                            (interp s ds))]
    [pair (l r) (crossV (interp l ds) (interp r ds))]
    [fst (p) (crossV-left (interp p ds))]
    [snd (p) (crossV-right (interp p ds))]))

;; num-op : (number number -> number) -> (TFAE-Value TFAE-Value -> TFAE-Value)
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
              (lookup name rest-ds))]))

;; ----------------------------------------

(define (get-type name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable, so no type")]
    [aBind (name ty rest)
           (if (symbol=? name-to-find name)
               ty
               (get-type name-to-find rest))]))

;; ----------------------------------------

(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [arrowTE (a b) (arrowT (parse-type a)
                           (parse-type b))]
    [crossTE (l r) (crossT (parse-type l)
                           (parse-type r))]))

(define (type-error tfae msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string tfae)
                      (string-append " not "
                                     msg)))))

(define typecheck : (TFAE TypeEnv -> Type)
  (lambda (tfae env)
    (type-case TFAE tfae
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
      [fun (name te body)
           (local [(define param-type (parse-type te))]
             (arrowT param-type
                     (typecheck body (aBind name
                                            param-type
                                            env))))]
      [app (fn arg)
           (type-case Type (typecheck fn env)
             [arrowT (param-type result-type)
                     (if (equal? param-type
                                 (typecheck arg env))
                         result-type
                         (type-error arg
                                     (to-string param-type)))]
             [else (type-error fn "function")])]
      [bool (f) (boolT)]
      [eq (l r) (type-case Type (typecheck l env)
                  [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (boolT)]
                           [else (type-error r "num")])]
                  [else (type-error l "num")])]
      [ifthenelse (t f s)
                  (local [(define exp1-type (typecheck t env))]
                    (type-case Type exp1-type
                      [boolT ()
                             (local [(define exp2-type (typecheck f env))]
                               (if (equal? exp2-type (typecheck s env))
                                   exp2-type
                                   (type-error f "not same type")))]
                      [else (type-error t "boolean")]))]
      [pair (l r)
            (crossT (typecheck l env) (typecheck r env))]
      [fst (p)
           (type-case Type (typecheck p env)
             [crossT (l r) l]
             [else (type-error p "no type")])]
      [snd (p)
           (type-case Type (typecheck p env)
             [crossT (l r) r]
             [else (type-error p "no type")])])))

;; ----------------------------------------

