#lang plai
;; aud->won: number -> number
;; consumes a number of Australian dollars and produces the won equivalent
(define (aud->won aud)
  (* aud 800))
(test (aud->won 5) 4000)

;; volume-cuboid: number number number -> number
;; consumes three integer numbers denoting lengths of three sides and produces the volume of the cuboid
(define (volume-cuboid x y z)
  (* x y z))
(test (volume-cuboid 2 3 4) 24)
(test (volume-cuboid 0 1 2) 0)


;; is-odd: number -> boolean
;; consumes an integer number and returns whether the number is odd
(define (is-odd? n)
  (= (modulo n 2) 1))
(test (is-odd? 5) #t)
(test (is-odd? 4) #f)
(test (is-odd? -3) #t)

;; gcd: number number -> number
;; consumes two integer numbers and returns the greatest common divisor of them
(define (gcd n1 n2)
  (cond
    [(= n2 0) n1]
    [(gcd n2 (modulo n1 n2))]))
(test (gcd 12 8) 4)
(test (gcd 6 27) 3)
(test (gcd 2 9) 1)
(test (gcd -4 -8) -4)

;; lcm: number number -> number
;; consumes two integer numbers and returns the least common multiple of them
(define (lcm n1 n2)
  (/ (* n1 n2) (gcd n1 n2)))
(test (lcm 9 81) 81)
(test (lcm 13 7) 91)


(define-type COURSE
  [CS320 (quiz number?)
         (homework number?)]
  [CS311 (homework number?)]
  [CS330 (projects number?)
         (homework number?)])
(define course_1 (CS320 5 4))
(test (CS320? course_1) #t)
(test (CS311? course_1) #f)
(test (CS320-homework course_1) 4)
(define course_2 (CS330 7 10))
(test (CS311? course_2) #f)
(test (CS330-projects course_2) 7)
(define course_6 (CS311 105))
(test (CS311? course_6) #t)


;; have-homework: COURSE -> num
;; consumes a course and produces the number of programming assignments for the given course
(define (have-homework course)
  (type-case COURSE course
    [CS320 (q h) h]
    [CS311 (h) h]
    [CS330 (p h) h]))

(define course_3 (CS320 7 15))
(test (have-homework course_3) 15)
(test (have-homework (CS311 107)) 107)
(test (have-homework (CS330 1 5)) 5)

;; have-projects: COURSE -> boolean
;; consumes a course and produces true only when the given course is CS330 with more than or equal to two projects, otherwise produces false
(define (have-projects course)
  (type-case COURSE course
    [CS320 (q h) #f]
    [CS311 (h) #f]
    [CS330 (p h) (>= p 2)]))
(define course_4 (CS330 12 5))
(test (have-projects course_4) #t)
(define course_5 (CS330 1 5))
(test (have-projects course_5) #f)
(test (have-projects (CS311 100)) #f)
(test (have-projects (CS320 1 1)) #f)

;; name-pets: list -> list
;; consumes a list of pets and produces a corresponding list of pets with names; it names all occurrences of 'dog with 'happy, 'cat with 'smart, 'pig with 'pinky, and keeps the other pets as unnamed
(define (name-pets pets)
  (cond
    [(empty? pets) empty]
    [(equal? (first pets) 'dog) (append (list 'happy)
                                        (name-pets (rest pets)))]
    [(equal? (first pets) 'cat) (append (list 'smart)
                                        (name-pets (rest pets)))]
    [(equal? (first pets) 'pig) (append (list 'pinky)
                                        (name-pets (rest pets)))]
    [else (append (list (first pets)) (name-pets (rest pets)))]))

(test (name-pets '(dog cat pig bird)) '(happy smart pinky bird))
(test (name-pets '(dragon pheonix cat)) '(dragon pheonix smart))

;; give-name: symbol symbol list -> list
;; consumes two symbols, called old and new, and a list of symbols. It produces a list of symbols by replacing all occurrences of old by new
(define (give-name old new pets)
  (cond
    [(empty? pets) empty]
    [(equal? (first pets) old) (append (list new)
                                       (give-name old new (rest pets)))]
    [else (append (list (first pets)) (give-name old new (rest pets)))]))

(test (give-name 'bear 'pooh (cons 'pig (cons 'cat (cons 'bear empty)))) '(pig cat pooh))
(test (give-name 'bird 'pooh (cons 'pig (cons 'cat (cons 'bear empty)))) '(pig cat bear))
