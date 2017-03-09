#lang plai-typed

(define-type TMFAE
  [num (n : number)]
  [bool (expr : boolean)]
  [add (lhs : TMFAE)
       (rhs : TMFAE)]
  [sub (lhs : TMFAE)
       (rhs : TMFAE)]
  [eq (lhs : TMFAE)
      (rhs : TMFAE)]
  [id (name : symbol)]
  [ifthenelse (expr : TMFAE)
              (first : TMFAE)
              (second : TMFAE)]
  [fun (param : (listof symbol))
       (paramtys : (listof TE))
       (body : TMFAE)]
  [app (fun-expr : TMFAE)
       (arg-exprs : (listof TMFAE))]
  [with (names : (listof symbol))
        (nametys : (listof TE))
        (inits : (listof TMFAE))
        (body : TMFAE)]
  [try1 (try-expr : TMFAE)
        (catch-expr : TMFAE)]
  [throw]
  [pair (lhs : TMFAE)
        (rhs : TMFAE)]
  [fst (exp : TMFAE)]
  [snd (exp : TMFAE)])

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (args : (listof TE))
           (result : TE)]
  [crossTE (left : TE)
           (right : TE)])

(define-type TMFAE-Value
  [numV (n : number)]
  [closureV (params : (listof symbol))
            (body : TMFAE)
            (ds : DefrdSub)]
  [boolV (t : boolean)]
  [crossV (left : TMFAE-Value)
          (right : TMFAE-Value)])

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol)
        (value : TMFAE-Value)
        (rest : DefrdSub)])

(define-type Type
  [numT]
  [boolT]
  [arrowT (param : (listof Type))
          (result : Type)]
  [crossT (left : Type)
          (right : Type)]
  [anyT])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

;; ----------------------------------------

(define (makeaSubs params exprs ds handler)
  (cond
    [(empty? params) ds]
    [else
     (local [(define val (interp (first exprs) ds handler))
             (define param (first params))]
             (makeaSubs (rest params) (rest exprs)
              (aSub param val ds) handler))]))

;; interp : TMFAE DefrdSub -> TMFAE-Value
(define (interp tmfae ds handler)
  (type-case TMFAE tmfae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds handler) (interp r ds handler))]
    [sub (l r) (num- (interp l ds handler) (interp r ds handler))]
    [id (name) (lookup name ds)]
    [fun (params param-te body-expr)
         (closureV params body-expr ds)]
    [app (fun-expr arg-exprs)
         (local [(define fun-val (interp fun-expr ds handler))]
           (interp (closureV-body fun-val)
                   (makeaSubs (closureV-params fun-val)
                              arg-exprs
                              (closureV-ds fun-val) handler) handler))]
    [bool (t) (boolV t)]
    [eq (l r) (if (equal? (interp l ds handler) (interp r ds handler))
                  (boolV true)
                  (boolV false))]
    [ifthenelse (t f s) (if (equal? (interp t ds handler) (boolV true))
                            (interp f ds handler)
                            (interp s ds handler))]
    [pair (l r) (crossV (interp l ds handler) (interp r ds handler))]
    [fst (p) (crossV-left (interp p ds handler))]
    [snd (p) (crossV-right (interp p ds handler))]
    [with (names nametys inits body)
          (interp body
                  (makeaSubs names inits ds handler) handler)]
    [try1 (try catch)
          (interp try ds (cons catch handler))]
    [throw ()
           (cond
             [(empty? handler) (error 'throw "unhandled")]
             [else (interp (first handler) ds (rest handler))])]))

;; num-op : (number number -> number) -> (TMFAE-Value TMFAE-Value -> TMFAE-Value)
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
    [arrowTE (a b) (arrowT (map (lambda (arg) (parse-type arg)) a)
                           (parse-type b))]
    [crossTE (l r) (crossT (parse-type l)
                           (parse-type r))]))

(define (type-error tmfae msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string tmfae)
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
     (if (or (equal? (first param-types) (first arg-types))
             (or (equal? (first param-types) (anyT))
                 (equal? (first arg-types) (anyT))))
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
         [crossT (fltype frtype)
                 (type-case Type second-type
                   [crossT (sltype srtype)
                           (whenCrossPair fltype frtype sltype srtype)]
                   [else (type-error f "same type")])]
         [arrowT (flist ftype)
                 (type-case Type second-type
                   [arrowT (slist stype)
                           (whenArrowPair first-type second-type)]
                   [else (type-error f "same type")])]
         [anyT () second-type]
         [else (cond
                 [(equal? second-type (anyT)) first-type]
                 [else (type-error f "same type")])])])))

(define (whenCrossPair fltype frtype sltype srtype)
  (type-case Type fltype
    [anyT ()
          (type-case Type frtype
            [anyT () (crossT sltype srtype)]
            [else (crossT sltype frtype)])]
    [else
     (type-case Type frtype
       [anyT () (crossT fltype srtype)]
       [else (crossT fltype frtype)])]))

(define (whenArrowPair f s)
  (local [(define flist (arrowT-param f))
          (define ftype (arrowT-result f))
          (define slist (arrowT-param s))
          (define stype (arrowT-result s))]
    (cond
      [(equal? ftype (anyT)) (arrowT (makenewlist flist slist) stype)]
      [else (arrowT (makenewlist flist slist) ftype)])))

(define (makenewlist flist slist)
  (cond
    [(empty? flist) empty]
    [else
     (if (equal? (first flist) (anyT))
         (cons (first slist) (makenewlist (rest flist) (rest slist)))
         (cons (first flist) (makenewlist (rest flist) (rest slist))))]))

(define typecheck : (TMFAE TypeEnv -> Type)
  (lambda (tmfae env)
    (type-case TMFAE tmfae
      [num (n) (numT)]
      [add (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [anyT () (numT)]
                           [else (type-error r "num")])]
                   [anyT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [anyT () (numT)]
                           [else (type-error r "num")])]
                   [else (type-error l "num")])]
      [sub (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [anyT () (numT)]
                           [else (type-error r "num")])]
                   [anyT ()
                         (type-case Type (typecheck r env)
                           [numT () (numT)]
                           [anyT () (numT)]
                           [else (type-error r "num")])]
                   [else (type-error l "num")])]
      [id (name) (get-type name env)]
      [fun (names tes body)
           (local [(define param-types (map (lambda (te) (parse-type te)) tes))]
             (arrowT param-types
                     (typecheck body (makeaBinds names
                                            param-types
                                            env))))]
      [app (fn args)
           (type-case Type (typecheck fn env)
             [arrowT (param-types result-type)
                     (if (typelistcheck param-types
                                        (map (lambda (arg) (typecheck arg env)) args))
                         result-type
                         (type-error args
                                     (to-string param-types)))]
             [anyT () (begin
                        (map (lambda (arg) (typecheck arg env)) args)
                        (anyT))]
             [else (type-error fn "function")])]
      [bool (f) (boolT)]
      [eq (l r) (type-case Type (typecheck l env)
                  [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (boolT)]
                           [else (type-error r "num")])]
                  [anyT () (typecheck r env)]
                  [else (type-error l "num")])]
      [ifthenelse (t f s)
                  (local [(define exp1-type (typecheck t env))]
                    (type-case Type exp1-type
                      [boolT () (decidetype f s env)]
                      [anyT () (decidetype f s env)]
                      [else (type-error t "boolean")]))]
      [pair (l r)
            (crossT (typecheck l env) (typecheck r env))]
      [fst (p)
           (type-case Type (typecheck p env)
             [crossT (l r) l]
             [anyT () (anyT)]
             [else (type-error p "no type")])]
      [snd (p)
           (type-case Type (typecheck p env)
             [crossT (l r) r]
             [anyT () (anyT)]
             [else (type-error p "no type")])]
      [throw () (anyT)]
      [with (names nametys inits body)
            (local [(define parsed-nametys (map (lambda (name) (parse-type name)) nametys))]
              (if (typelistcheck parsed-nametys (map (lambda (init) (typecheck init env)) inits))
                  (typecheck body
                             (makeaBinds names parsed-nametys env))
                  (type-error 'with "same type")))]
      [try1 (try catch)
            (local [(define try-type (typecheck try env))]
              (type-case Type try-type
                [anyT () (typecheck catch env)]
                [else (cond
                        [(isthereAnyT try-type) (typecheck catch env)]
                        [(equal? try-type (typecheck catch env)) try-type]
                        [else (cond
                                [(equal? (typecheck catch env) (anyT)) try-type]
                                [else (type-error catch "no type")])])]))])))

(define (isthereAnyT type)
  (type-case Type type
    [anyT () #t]
    [arrowT (param result)
            (or (isAnyTinList param) (isthereAnyT result))]
    [crossT (left right)
            (or (isthereAnyT left) (isthereAnyT right))]
    [else #f]))

(define (isAnyTinList param)
  (cond
    [(empty? param) #f]
    [else
     (or (isthereAnyT (first param)) (isAnyTinList (rest param)))]))

;; ----------------------------------------
(define run : (TMFAE -> TMFAE-Value)
  (lambda (tmfae)
    (interp tmfae (mtSub) (list (throw)))))

(define eval : (TMFAE -> TMFAE-Value)
  (lambda (tmfae)
    (begin
      (try (typecheck tmfae (mtEnv))
           (lambda () (error 'type-error "typecheck")))
      (run tmfae))))

;; ----------------------------------------

(test (run (app (fun (list) (list) (num 10)) (list))) (numV 10))
(test (run (app (fun (list 'x 'y) (list (numTE) (numTE))
                        (sub (id 'x) (id 'y))) (list (num 10) (num 20))))
      (numV -10))
(test (typecheck (app (fun (list 'x 'y) (list (numTE) (boolTE))
                           (id 'y))
                      (list (num 10) (bool false)))
                 (mtEnv))
      (boolT))
(test/exn (typecheck (app (fun (list 'x 'y) (list (numTE) (boolTE))
                               (id 'y))
                          (list (num 10) (num 10)))
                     (mtEnv))
          "no type")

(test (typecheck (throw) (mtEnv)) (anyT))
(test (typecheck (try1 (num 8) (num 10)) (mtEnv)) (numT))
(test (typecheck (try1 (throw) (num 10)) (mtEnv)) (numT))
(test/exn (typecheck (try1 (num 8) (bool false)) (mtEnv)) "no type")
(test (typecheck (ifthenelse (throw) (num 1) (num 2)) (mtEnv)) (numT))
(test/exn (typecheck (app (throw) (list (ifthenelse (num 1) (num 2) (num 3)))) (mtEnv)) "no type")
(test/exn (typecheck (add (bool true) (throw)) (mtEnv)) "no type")
(test (typecheck (fst (throw)) (mtEnv)) (anyT))
(test (typecheck (ifthenelse (bool true) (pair (num 1) (throw)) (pair (throw) (bool false))) (mtEnv)) (crossT (numT) (boolT)))
(test (typecheck (bool true) (mtEnv)) (boolT))
(test (typecheck (ifthenelse (bool false) (num 2) (throw)) (mtEnv)) (numT))
(test (typecheck (ifthenelse (bool false) (throw) (num 2)) (mtEnv)) (numT))
(test (typecheck (ifthenelse (bool false) (throw) (throw)) (mtEnv)) (anyT))
(test (typecheck (pair (num 2) (bool false)) (mtEnv)) (crossT (numT) (boolT)))
(test (typecheck (pair (num 2) (throw)) (mtEnv)) (crossT (numT) (anyT)))
(test (typecheck (snd (throw)) (mtEnv)) (anyT))
(test (typecheck (fst (pair (num 2) (bool false))) (mtEnv)) (numT))
(test (typecheck (snd (pair (num 2) (bool false))) (mtEnv)) (boolT))
(test (typecheck (fun empty empty (num 2)) (mtEnv)) (arrowT empty (numT)))
(test (typecheck (fun (list 'x) (list (numTE)) (throw)) (mtEnv)) (arrowT (list (numT)) (anyT)))
(test (typecheck (app (fun empty empty (num 2)) empty) (mtEnv)) (numT))
(test (typecheck (app (throw) (list (num 2) (bool false))) (mtEnv)) (anyT))
(test (typecheck (app (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y))) (list (num 2) (num 3))) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (num 2)) (id 'x)) (mtEnv)) (numT))
(test (typecheck (with (list 'x 'y 'z) (list (boolTE) (numTE) (numTE)) (list (bool false) (num 2) (num 3)) (ifthenelse (id 'x) (id 'y) (id 'z))) (mtEnv)) (numT))
(test (typecheck (with empty empty empty (num 2)) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (throw)) (num 2)) (mtEnv)) (numT))
(test (run (eq (num 2) (num 3))) (boolV false))
(test (run (eq (num 2) (num 2))) (boolV true))
(test (run (ifthenelse (bool true) (num 2) (num 3))) (numV 2))
(test (run (ifthenelse (bool false) (num 2) (num 3))) (numV 3))
(test (run (with (list 'x 'y 'z) (list (numTE) (numTE) (numTE)) (list (num 2) (num 3) (num 4)) (add (id 'x) (id 'y)))) (numV 5))
(test (run (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y)))) (closureV (list 'x 'y) (add (id 'x) (id 'y)) (mtSub)))
(test (run (app (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y))) (list (num 2) (num 3)))) (numV 5))
(test (run (fst (pair (num 2) (num 3)))) (numV 2))
(test (typecheck (try1 (throw) (throw)) (mtEnv)) (anyT))
(test (typecheck (app (throw) (list (num 1))) (mtEnv)) (anyT))
(test (typecheck (fst (throw)) (mtEnv)) (anyT))
(test (typecheck (ifthenelse (bool true) (fun (list 'x 'y) (list (numTE) (numTE)) (throw)) (fun (list 'z 'a) (list (numTE) (numTE)) (add (id 'z) (id 'a)))) (mtEnv)) (arrowT (list (numT) (numT)) (numT)))
(test (typecheck (try1 (num 2) (throw)) (mtEnv)) (numT))
(test (typecheck (try1 (throw) (num 2)) (mtEnv)) (numT))
(test (typecheck (try1 (num 2) (num 2)) (mtEnv)) (numT))
(test (typecheck (app (fun (list 'a) (list (numTE)) (add (throw) (num 10))) (list (throw))) (mtEnv)) (numT))
(test (typecheck (try1 (with (list 'map 'foo) (list (arrowTE (list (arrowTE (list (numTE)) (boolTE)) (crossTE (numTE) (numTE))) (crossTE (boolTE) (boolTE))) (crossTE (numTE) (numTE)))          (list (fun (list 'f 'p) (list (arrowTE (list (numTE)) (boolTE)) (crossTE (numTE) (numTE))) (pair (app (id 'f) (list (fst (id 'p)))) (app (id 'f) (list (snd (id 'p)))))) (pair (num 10) (num 42))) (app (id 'map) (list (throw) (id 'foo)))) (pair (bool false) (bool false))) (mtEnv))     (crossT (boolT) (boolT)))
(test (typecheck (try1 (add (throw) (num 8)) (num 10)) (mtEnv)) (numT))
(test (typecheck (try1 (pair (num 8) (num 2)) (throw)) (mtEnv)) (crossT (numT) (numT)))
(test (typecheck (eq (num 42) (try1 (ifthenelse (bool true) (throw) (throw)) (num 10))) (mtEnv)) (boolT))
(test (typecheck (ifthenelse (throw) (pair (throw) (num 42)) (pair (bool false) (throw))) (mtEnv)) (crossT (boolT) (numT)))
(test (typecheck (with (list 'x 'y 'z) (list (boolTE) (numTE) (numTE)) (list (bool false) (num 2) (num 3)) (ifthenelse (id 'x) (id 'y) (id 'z))) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (num 2)) (id 'x)) (mtEnv)) (numT))
(test (typecheck (with (list 'dup) (list (arrowTE (list (numTE)) (crossTE (numTE) (numTE)))) (list (fun (list 'n) (list (numTE)) (pair (id 'n) (id 'n)))) (app (id 'dup) (list (throw)))) (mtEnv))   (crossT (numT) (numT)))
(test/exn (typecheck (app (throw) (list (add (bool true) (throw)))) (mtEnv)) "no type")
(test/exn (typecheck (app (throw) (list (ifthenelse (num 1) (num 2) (num 3)))) (mtEnv)) "no type")
(test/exn (typecheck (app (throw) (list (app (bool true) (list (throw))))) (mtEnv)) "no type")

;; mytest -----------------------------------------------

(test (run (eq (num 2) (add (num 1) (num 1)))) (boolV true))
(test (typecheck (ifthenelse (bool true) (pair (throw) (num 10)) (pair (pair (num 10) (num 8)) (throw))) (mtEnv)) (crossT (crossT (numT) (numT)) (numT)))
(test (typecheck (try1 (throw) (pair (throw) (num 10))) (mtEnv)) (crossT (anyT) (numT)))
(test (run (snd (pair (num 2) (add (num 1) (num 9))))) (numV 10))
(test (typecheck (snd (pair (num 2) (add (num 1) (num 9)))) (mtEnv)) (numT))
(test (typecheck (try1 (pair (throw) (num 10)) (pair (num 10) (num 10))) (mtEnv)) (crossT (numT) (numT)))