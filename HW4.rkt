#lang plai

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

(define-type FunDef
 [fundef (fname symbol?) (args list?) (body FnWAE?)])

(define-type FnWAE
 [num (n number?)]
 [add (lhs FnWAE?) (rhs FnWAE?)]
 [sub (lhs FnWAE?) (rhs FnWAE?)]
 [with (name symbol?) (named-expr FnWAE?) (body FnWAE?)]
 [id (name symbol?)]
 [app (ftn symbol?) (arg list?)]
 [rec (elem (listof (cons/c symbol? FnWAE?)))]
 [get (body FnWAE?) (name symbol?)])

; parse : sexp -> FnWAE
; convert s-expressions into FnWAE types
(define (parse sexp)
 (match sexp
  [(? number?) (num sexp)]
  [(list '+ l r) (add (parse l) (parse r))]
  [(list '- l r) (sub (parse l) (parse r))]
  [(list 'with (list x i) b) (with x (parse i) (parse b))]
  [(list 'rec li ...) (rec (map (lambda (a)
                                (cons (first a) (parse (second a)))) li))]
  [(list 'get b n) (get (parse b) n)]
  [(? symbol?) (id sexp)]
  [(list f a ...) (app f (map parse a))]
  [else (error 'parse "bad syntax: ~a" sexp)]))

; parse-defn : sexp -> FunDef
; convert s-expressions into FunDef types
(define (parse-defn sexp)
 (match sexp
  [(list 'deffun (list f x ...) body)
   (unless (uniq? x)
    (error 'parse-defn "bad syntax"))
   (fundef f x (parse body))]))

; uniq? : list-of-symbol -> bool
; if there are no duplicates in the list-of-symbol, return true (else false)
(define (uniq? x)
  (equal? x (remove-duplicates x)))

; list-of-fundef : list -> list
; receives input and makes list of fundefs
(define (list-of-fundef li)
  (cond
    [(empty? li) '()]
    [else (cons (first li) (list-of-fundef (rest li)))]))

; lookup-fundef : symbol list-of-FunDef -> FunDef
; find a symbol in the list of FunDefs, and return it
(define (lookup-fundef name fundefs)
  (cond
    [(empty? fundefs)
     (error 'lookup-fundef "unknown function")]
    [else
     (if (symbol=? name (fundef-fname (first fundefs)))
         (first fundefs)
         (lookup-fundef name (rest fundefs)))]))

; subst : FnWAE list-of-symbols list-of-FnWAE -> FnWAE
; substitute all the symbols in the exp and change them into vals
(define (subst exp args vals)
  (cond
    [(empty? args) exp]
    [else
     (local
       [(define arg (first args))]
       (define val (first vals))
       (define sub_exp (subst exp (rest args) (rest vals)))
       (type-case FnWAE sub_exp
         [num (n) sub_exp]
         [add (l r) (add (subst l (cons arg empty) (cons val empty)) (subst r (cons arg empty) (cons val empty)))]
         [sub (l r) (sub (subst l (cons arg empty) (cons val empty)) (subst r (cons arg empty) (cons val empty)))]
         [with (y i b) (with y
                             (subst i (cons arg empty) (cons val empty))
                             (if (symbol=? y arg) b
                                 (subst b (cons arg empty) (cons val empty))))]
         [id (name) (cond [(equal? name arg) val]
                       [else sub_exp])]
         [rec (li)
           (rec (map (lambda (x)
                  (cons (car x) (subst (cdr x) (cons arg empty) (cons val empty)))) li))]
         [get (b a) (get (subst b args vals) a)]
         [app (f a) (app f (map (lambda (a_a)
                               (subst a_a (cons arg empty) (cons val empty))) a))]))]))

; lookup-rec : list-of-records symbol -> FnWAE
; find a symbol in the records list and return it
(define (lookup-rec li a)
  (local
    [(define list-of-sym (map car li))]
    (cond
      [(equal? (remove-duplicates list-of-sym) list-of-sym)
       (cond
         [(empty? li) empty]
         [else
          (cond
            [(equal? (car (first li)) a) (cdr (first li))]
            [else
             (lookup-rec (rest li) a)])])]
      [else (error 'lookup-rec "duplicate fields")])))


; interp-get : FnWAE symbol list-of-fundef -> number or FnWAE
; interpretes get
(define (interp-get b a fundefs)
 (local
  [(define interp-b (interp b fundefs))]
  (unless (rec? interp-b)
   (error 'interp-get "not appropriate type"))
  (local
    [(define sth (lookup-rec (rec-elem (interp b fundefs)) a))]
    (cond
      [(empty? sth) (error 'interp-get "no such field")]
      [else (interp sth fundefs)]))))


; interp : FnWAE list-of-FunDef -> number or FnWAE
; interpretes FnWAE based on fundefs
(define (interp fnwae fundefs)
  (type-case FnWAE fnwae
    [num (n) n]
    [add (l r) (+ (interp l fundefs) (interp r fundefs))]
    [sub (l r) (- (interp l fundefs) (interp r fundefs))]
    [with (x i b) (interp (subst b (cons x empty) (cons 
                                                   (local
                                                     [(define sth (interp i fundefs))]
                                                     (cond
                                                       [(FnWAE? sth) sth]
                                                       [else (parse sth)])) empty)) fundefs)]
    [id (s) (error 'interp "free variable")]
    [rec (li) (rec (map (lambda (x)
                          (cons (car x) 
                                (local 
                                  [(define sth (interp (cdr x) fundefs))]
                                  (cond
                                    [(FnWAE? sth) sth]
                                    [else (parse sth)])))) li))]
    [get (b a)
         (interp-get b a fundefs)]
    [app (f a)
         (local
           [(define a-fundef (lookup-fundef f fundefs))]
           (cond
             [(equal? (length a) (length (fundef-args a-fundef)))
              (interp (subst (fundef-body a-fundef)
                             (fundef-args a-fundef)
                             a) fundefs)]
             [else (error 'interp "wrong arity")]))]))

; final-interp : FnWAE or number -> number or symbol
; checks the result of interp and return appropriate result
(define (final-interp whatisthis fundef)
  (cond
    [(number? whatisthis) whatisthis]
    [else 'record]))

; check-fun-dup : list-of-fundef -> boolean
; check if there is duplicate function name in the list of fundefs
(define (check-fun-dup fundef-list)
  (local
    [(define fname-list (map fundef-fname fundef-list))]
    (cond
      [(equal? fname-list (remove-duplicates fname-list)) #t]
      [else #f])))

; run : string list -> number or error or symbol
; run the input
(define (run str deffun)
  (local
    [(define fundef-list (list-of-fundef deffun))]
    (cond
      [(check-fun-dup fundef-list)
       (final-interp (interp (parse (string->sexpr str)) fundef-list) fundef-list)]
      [else (error 'run "duplicate function symbol")])))
  

; tests
(test (run "{f 1 2}" (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)
(test (run "{+ {f} {f}}" (list (parse-defn '{deffun {f} 5}))) 10)
(test/exn (run "{f 1}" (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")

(test (run "{rec {a 10} {b {+ 1 2}}}" empty)
      'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty)
      3)
(test/exn (run "{get {rec {b 10} {b {+ 1 2}}} b}" empty)
          "duplicate fields")
(test/exn (run "{get {rec {a 10}} b}" empty)
          "no such field")
(test (run "{g {rec {a 0} {c 12} {b 7}}}"
           (list (parse-defn '{deffun {g r} {get r c}})))
      12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty)
      'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty)
      0)
(test/exn (run "{rec {z {get {rec {z 0}} y}}}" empty)
          "no such field")
(test (run "{with {x {f 2 5}} {g x}}" (list (parse-defn '{deffun {f a b} {+ a b}}) (parse-defn '{deffun {g x} {- x 5}}))) 2)
(test (run "{f 1 2}" (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)
(test (run "{+ {f} {f}}" (list (parse-defn '{deffun {f} 5}))) 10)
(test (run "{h 1 4 5 6}" (list (parse-defn '{deffun {h x y z w} {+ x w}}) (parse-defn '{deffun {g x y z w} {+ y z}}))) 7)
(test (run "{with {x 10} {- {+ x {f}} {g 4}}}" (list (parse-defn '{deffun {f} 4}) (parse-defn '{deffun {g x} {+ x x}}))) 6)

(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{with {x 3} {with {y 5} {get {rec {a x} {b y}} a}}}" empty) 3)
(test (run "{with {x {f {rec {a 10} {b 5}} 2}} {g x}}" (list (parse-defn '{deffun {f a b} {+ {get a a} b}}) (parse-defn '{deffun {g x} {+ 5 x}}))) 17)
(test (run "{get {f 1 2 3 4 5} c}" (list (parse-defn '{deffun {f a b c d e} {rec {a a} {b b} {c c} {d d} {e e}}}))) 3)
(test (run "{get {f 1 2 3} b}" (list (parse-defn '{deffun {f a b c} {rec {a a} {b b} {c c}}}))) 2)
(test (run "{get {f 1 2 3} y}" (list (parse-defn '{deffun {f a b c} {rec {x a} {y b} {z c} {d 2} {e 3}}}))) 2)
(test (run "{get {f 1 2 3} d}" (list (parse-defn '{deffun {f a b c} {rec {x a} {y b} {z c} {d 2} {e 3}}}))) 2)
(test (run "{f {get {get {rec {a {rec {a 10} {b {- 5 2}}}} {b {get {rec {x 50}} x}}} a} b}}" (list (parse-defn '{deffun {f x} {+ 5 x}}))) 8)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{rec {a 10}}" empty) `record)
(test (run "{get {rec {a 10}} a}" empty) 10)
(test (run "{get {rec {a {+ 1 2}}} a}" empty) 3)
(test (run "{rec }" empty) `record)
(test (run "{get {rec {a {rec {b 10}}}} a}" empty) `record)
(test (run "{get {get {rec {a {rec {a 10}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} b}" empty) 20)
(test (run "{+ {get {rec {a 10}} a} {get {rec {a 20}} a}}" empty) 30)
(test (run "{+ {get {rec {a 10}} a} {get {rec {a 20}} a}}" empty) 30)
(test (run "{rec {a 10}}" empty) `record)
(test (run "{rec {a {- 2 1}}}" empty) `record)
(test (run "{get {rec {a 10}} a}" empty) 10)
(test (run "{get {rec {a {- 2 1}}} a}" empty) 1)
(test (run "{get {rec {a {rec {b 10}}}} a}" empty) `record)
(test (run "{get {get {rec {a {rec {a 10}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} b}" empty) 20)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{with {y {rec {x 1} {y 2} {z 3}}} {get y y}}" empty) 2)
(test (run "{with {y {rec {x 1} {y 2} {z 3}}} {get y z}}" empty) 3)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)

;
(test/exn (run "{get {+ 1 2} b}" empty) "not appropriate type")
(test/exn (run "{f 5 4 3}" (list (parse-defn '{deffun {f a b c} {+ a {- b c}}}) (parse-defn '{deffun {f x y z} {- x {- y z}}}))) "duplicate function symbol")
(test (run "{with {y 3} {rec {x 1} {y 3}}}" empty) 'record)
(test (run "{with {x 7} {get {rec {a {+ x 2}} {b 7}} a}}" empty) 9)
(test (run "{with {x 7} {get {rec {a {f x}} {b 7}} a}}" (list (parse-defn '{deffun {f x} {+ x 2}}) (parse-defn '{deffun {g x} {- x 2}}))) 9)
(test (run "{f {rec {x 5} {y 3}}}" (list (parse-defn '{deffun {f x} {get x y}}))) 3)
