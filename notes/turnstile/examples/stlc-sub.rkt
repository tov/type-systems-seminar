#lang s-exp "../stlc-sub.rkt"

(define (+/Num [n Num] [m Num] -> Num)
  (-/Num n (-/Num 0 m)))

(define-type-alias Point (Record [x Num] [y Num]))
(define-type-alias ColorPoint (Record [x Num] [y Num] [color String]))

(define (manhattan-distance [p Point] -> Num)
  (+/Num (project p x) (project p y)))

(define red-3-4 ColorPoint
  (record [x 3] [y 4] [color "Red"]))

(define should-be-7 (manhattan-distance red-3-4))