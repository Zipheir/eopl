;; leaf : Int → Bintree
;; Usage: leaf takes an integer n and returns a new leaf tree.
(define (leaf n) n)

;; interior-node : Sym × Bintree × Bintree → Bintree
;; Usage: interior-node constructs a branch tree from a symbol
;; s and two subtrees.
(define (interior-node s l r) (list s l r))

;; leaf? : Scheme-Val → Bool
;; Usage: leaf? is #t if its argument is a leaf tree, and #f otherwise.
(define (leaf? x) (integer? x))

;; lson : Bintree → Bintree
;; Usage: lson returns the left subtree of an interior node.
(define (lson t)
  (if (leaf? t)
      (error 'lson "tree is a leaf" t)
      (cadr t)))

;; rson : Bintree → Bintree
;; Usage: rson returns the right subtree of an interior node.
(define (rson t)
  (if (leaf? t)
      (error 'rson "tree is a leaf" t)
      (caddr t)))

;; contents-of : Bintree → Sym + Int
;; Usage: Returns the value contained in a node, which is either an
;; integer (for leaves) or a symbol (for interior nodes).
(define (contents-of t)
  (if (leaf? t) t (car t)))

;; double-tree : Bintree → Bintree
;; Usage: double-tree returns a tree with the same structure as t
;; but with each leaf integer doubled.
(define (double-tree t)
  (if (leaf? t)
      (leaf (* (contents-of t) 2))
      (interior-node
       (contents-of t)
       (double-tree (lson t))
       (double-tree (rson t)))))

;; mark-leaves-with-red-depth : Bintree → Bintree
;; Usage: Returns a tree with the same structure as t, except that
;; each leaf contains the number of nodes between it and the root
;; (which must be labelled with 'red).
(define (mark-leaves-with-red-depth t)
  (if (leaf? t)
      (error 'mark-leaves-with-red-depth "no root" t)
      (if (eqv? 'red (contents-of t))
          (interior-node
           'red
           (mark-leaves-from 0 (lson t))
           (mark-leaves-from 0 (rson t)))
          (error 'mark-leaves-with-red-depth "root is not red" t))))

;; mark-leaves-from : Int × Bintree → Bintree
;; Usage: Replaces each leaf in t with its depth, starting from n.
(define (mark-leaves-from n t)
  (if (leaf? t)
      (leaf n)
      (interior-node
       (contents-of t)
       (mark-leaves-from (+ n 1) (lson t))
       (mark-leaves-from (+ n 1) (rson t)))))
