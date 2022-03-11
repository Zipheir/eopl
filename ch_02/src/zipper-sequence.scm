;;;; Implementation from exercise 2.18

(include "test.scm")

;;; Constructors

;; number->sequence : Int → Seq
;; Usage: Returns a singleton sequence containing n as its
;; current element.
(define (number->sequence n) (list n '() '()))

;;; Auxilliary accessor procedures.

(define (sequence-left seq) (cadr seq))
(define (sequence-right seq) (caddr seq))

;; insert-to-left : Int × Seq → Seq
;; Usage: Inserts n before the current element in seq.
(define (insert-to-left n seq)
  (list (current-element seq)
        (cons n (sequence-left seq))
        (sequence-right seq)))

;; insert-to-right : Int × Seq → Seq
;; Usage: Inserts n after the current element in seq.
(define (insert-to-right n seq)
  (list (current-element seq)
        (sequence-left seq)
        (cons n (sequence-right seq))))

;;; Extractors

;; current-element : Seq → Int
;; Usage: Returns the focus of seq.
(define (current-element seq) (car seq))

;; move-to-left : Seq → Seq
;; Usage: Returns a sequence whose focus is the previous element
;; of the focus of seq.  Errors if seq is at its left end.
(define (move-to-left seq)
  (if (at-left-end? seq)
      (error 'move-to-left "sequence at left end" seq)
      (let ((left (sequence-left seq)))
        (list (car left)
              (cdr left)
              (cons (current-element seq) (sequence-right seq))))))

;; move-to-right : Seq → Seq
;; Usage: Returns a sequence whose focus is the previous element
;; of the focus of seq.  Errors if seq is at its right end.
(define (move-to-right seq)
  (if (at-right-end? seq)
      (error 'move-to-right "sequence at right end" seq)
      (let ((right (sequence-right seq)))
        (list (car right)
              (cons (current-element seq) (sequence-left seq))
              (cdr right)))))

;;; Position predicates

;; at-left-end? : Seq → Bool
;; Usage: True if the current element of seq is the first in the
;; sequence.
(define (at-left-end? seq)
  (null? (sequence-left seq)))

;; at-right-end? : Seq → Bool
;; Usage: True if the current element of seq is the last in the
;; sequence.
(define (at-right-end? seq)
  (null? (sequence-right seq)))

;;; Tests

(define (run-tests)
  (define test-seq
    (insert-to-right 3 (insert-to-left 1 (number->sequence 2))))

  (test 2 (current-element (number->sequence 2)))
  (test 2 (current-element (number->sequence 2)))
  (test #t (at-left-end? (number->sequence 2)))
  (test #f (at-left-end? (insert-to-left 1 (number->sequence 2))))
  (test #t (at-left-end? (insert-to-right 1 (number->sequence 2))))
  (test #t (at-right-end? (number->sequence 2)))
  (test #t (at-right-end? (insert-to-left 1 (number->sequence 2))))
  (test #f (at-right-end? (insert-to-right 1 (number->sequence 2))))

  (test 3 (current-element (move-to-right test-seq)))
  (test 1 (current-element (move-to-left test-seq)))
  (test 7 (current-element (move-to-left (insert-to-left 7 test-seq))))
  (test 7 (current-element (move-to-right (insert-to-right 7 test-seq))))
  )
