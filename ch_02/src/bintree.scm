;;;; Exercise 2.19

;;; The empty-leaf integer bintree grammar:
;;;
;;; Bintree ::= () | (Int Bintree Bintree)
;;;
;;; I believe the naming of the following procedures could be better.
;;; The use of at-, current-, and move-to- prefixes suggests that
;;; there's some kind of context. There isn't, at least not in this
;;; exercise.
;;;
;;; These trees correspond closely to non-empty sequences.

(include "test.scm")

;;; Constructors

;; number->bintree : Int → Bintree
;; Usage: Returns a bintree containing only n.
(define (number->bintree n)
  (list n '() '()))

;; insert-to-left : Int × Bintree → Bintree
;; Usage: Inserts n to the top of tree's left subtree. Errors if
;; tree is a leaf.
(define (insert-to-left n tree)
  (if (at-leaf? tree)
      (error 'insert-to-left "tree is a leaf" tree)
      (list (car tree)
            (list n (cadr tree) '())
            (caddr tree))))

;; insert-to-right : Int × Bintree → Bintree
;; Usage: Inserts n to the top of tree's right subtree. Errors if
;; tree is a leaf.
(define (insert-to-right n tree)
  (if (at-leaf? tree)
      (error 'insert-to-right "tree is a leaf" tree)
      (list (car tree)
            (cadr tree)
            (list n '() (caddr tree)))))

;;; Predicate

;; at-leaf? : Bintree → Bool
;; Usage: True if tree is a leaf and false otherwise.
(define (at-leaf? tree)
  (null? tree))

;;; Accessors

;; current-element : Bintree → Int
;; Usage: Returns the integer stored in the topmost node of tree.
;; Errors if tree is a leaf.
(define (current-element tree)
  (if (at-leaf? tree)
      (error 'current-element "tree is a leaf" tree)
      (car tree)))

;; move-to-left-child : Bintree → Bintree
;; Usage: Returns the left subtree of tree. Errors if tree is a leaf.
(define (move-to-left-child tree)
  (if (at-leaf? tree)
      (error 'move-to-left-child "tree is a leaf" tree)
      (cadr tree)))

;; move-to-right-child : Bintree → Bintree
;; Usage: Returns the right subtree of tree. Errors if tree is a leaf.
(define (move-to-right-child tree)
  (if (at-leaf? tree)
      (error 'move-to-right-child "tree is a leaf" tree)
      (caddr tree)))

;;;; Tests

(define (run-tests)
  (define test-tree
    (insert-to-right 14
                     (insert-to-left 12
                                     (number->bintree 13))))

  (test #f (at-leaf? test-tree))
  (test #t (at-leaf? (move-to-left-child (number->bintree 1))))
  (test #t (at-leaf? (move-to-right-child (number->bintree 1))))

  (test 2 (current-element (number->bintree 2)))
  (test 13 (current-element test-tree))
  (test 12 (current-element (move-to-left-child test-tree)))
  (test 14 (current-element (move-to-right-child test-tree)))

  (test 15 (current-element
            (move-to-left-child
             (insert-to-left 15 test-tree))))
  (test 15 (current-element
            (move-to-right-child
             (insert-to-right 15 test-tree))))
  )
