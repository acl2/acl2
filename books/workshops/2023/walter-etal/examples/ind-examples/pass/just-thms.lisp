(in-package "ACL2S")

(definec <<= (x :all y :all) :bool
  (or (== x y)
      (<< x y)))

(definec insert (a :all x :tl) :tl
  (match x
    (() (list a))
    ((e . es) (if (<<= a e)
                  (cons a x)
                (cons e (insert a es))))))

(definec isort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (insert e (isort es)))))

(definec less (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<< e a)
                  (cons e (less a es))
                (less a es)))))

(definec notless (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<<= a e)
                  (cons e (notless a es))
                (notless a es)))))

(definec qsort (x :tl) :tl
  (match x 
    (() ())
    ((e . es) (app (qsort (less e es))
                   (list e)
                   (qsort (notless e es))))))

#|

Q4. Prove the following property.

This is not easy, so I strongly recommend that you come up with a
plan and use the professional method to sketch out a proof.

|#

;; we need to describe that elements in an isorted list are ordered
(definec orderedp (x :tl) :boolean
  (or (endp x)
      (endp (cdr x))
      (^ (<<= (first x) (second x))
         (orderedp (cdr x)))))

; We need the lemma that insert preserves order to avoid nested
; indution in lemma 4
(property insert-preserves-order (l :tl a :all)
          :h (orderedp l)
          :b (orderedp (insert a l)))

(property isort-ordered (l :tl)
          (orderedp (isort l)))


; Helper Lemma from checkpoint
(property less-insert-<<= (l :tl a :all b :all)
          :h (<<= a b)
          :b (== (less a (insert b l))
                 (less a l)))

;  We need the invariant that l is ordered!
(property less-insert-<< (l :tl a :all b :all)
          :h (^ (<< b a)
                (orderedp l))
          :b (== (less a (insert b l))
                 (insert b (less a l))))

; Lemma 1
(property isort-less (l :tl a :all)
          (== (isort (less a l))
              (less a (isort l))))

; Helper Lemmas for L2 (symmetric from L1)
(property notless-insert-<<= (l :tl a :all b :all)
          :h (<<= a b)
          :b (== (insert b (notless a l))
                 (notless a (insert b l))))

; Helper Lemma
(property notless-insert-<< (l :tl a :all b :all)
          :h (<< b a)
          :b (== (notless a (insert b l))
                 (notless a l)))

; Lemma 2 
(property isort-notless (l :tl a :all)
          (== (isort (notless a l))
              (notless a (isort l))))

; Helper Lemma
(property orderedp-<=-less (l :tl a :all)
          :h (^ (orderedp l) (<<= a (first l)))
          :b (== (less a l) nil))

; Lemma 3
(property app-less-not-less (l :tl a :all)
          :h (orderedp l)
          :b (== (append (less a l) (cons a (notless a l)))
                 (insert a l)))
