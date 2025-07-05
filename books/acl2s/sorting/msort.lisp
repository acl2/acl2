#|

 Author: Pete Manolios
 
 This is a book with merge sort and insertion sort for lists
 containing arbitrary objects.

 I use definec and all functions have their contracts checked, so
 guards are verified.

 The book includes a proof of equivalence between merge sort and
 insertion sort.

|#

(in-package "ACL2S")
(include-book "acl2s/definec" :dir :system :ttags :all)

(definec <<= (x y :all) :bool
  (lexorder x y))

(definec orderedp (x :tl) :bool
  (match x
    ((:or nil (&)) t)
    ((a b . &) (^ (<<= a b) (orderedp (cdr x))))))

(definec del (e :all x :tl) :tl
  (match x
    (() ())
    ((!e . r) r)
    ((f . r) (cons f (del e r)))))

(definec permp (x y :tl) :bool
  (match x
    (() (endp y))
    ((f . r) (^ (in f y) (permp r (del f y))))))

(definec insert (a :all x :tl) :tl
  (match x
    (() (list a))
    ((f . r) (if (<<= a f)
                 (cons a x)
               (cons f (insert a r))))))

(definec isort (x :tl) :tl
  (match x
    (() ())
    ((f . r) (insert f (isort r)))))

(property orderedp-insert (x :all l :tl)
  :hyps (orderedp l)
  (orderedp (insert x l))
  :hints (("goal" :induct (insert x l))))

(property isort-ordered (x :tl)
  (orderedp (isort x))
  :hints (("goal" :induct (isort x))))

(property permp-cons (e :all x y :tl)
  :h (permp x y)
  :b (permp (insert e x) (cons e y))
  :hints (("goal" :induct (permp x y))))

(property isort-permp (x :tl)
  (permp (isort x) x)
  :hints (("goal" :induct (isort x))))

(property ordered-isort (x :tl)
  :h (orderedp x)
  :b (== (isort x) x)
  :hints (("goal" :induct (tlp x))))

(property isort-idempotent (x :tl)
  (== (isort (isort x))
      (isort x)))

; Merge sort

(definec mrge (x y :tl) :tl
  (match (list x y)
    ((nil &) y)
    ((& nil) x)
    (((fx . rx) (fy . ry))
     (if (<<= fx fy)
         (cons fx (mrge rx y))
       (cons fy (mrge x ry))))))

(definec even-els (l :tl) :tl
  (match l
    (() ())
    ((f . &) (cons f (even-els (cddr l))))))

(property even-els-size (l :tl)
  (<= (acl2s-size (even-els l))
      (acl2s-size l))
  :hints (("goal" :induct (even-els l)))
  :rule-classes :linear)

(definec odd-els (l :tl) :tl
  (even-els (cdr l)))

(set-induction-depth-limit 1)
(definec mrge-sort (x :tl) :tl
  (match x
    ((:or () (&)) x)
    (& (mrge (mrge-sort (even-els x))
             (mrge-sort (odd-els x))))))
(set-induction-depth-limit 0)

(property mrge-ordered (x y :tl)
  :h (^ (orderedp x) (orderedp y))
  :b (orderedp (mrge x y))
  :hints (("goal" :induct (mrge x y))))

(property mrge-sort-ordered (x :tl)
  (orderedp (mrge-sort x))
  :hints (("goal" :induct (mrge-sort x))))

#|

Proof Sketch Using the Professional Method 
           
(M x)
= { Def M }
(Mg (M (E x) (O x)))
= { IH }
(Mg (I (E x)) (I (O x)))
= { mrge-isort }
(I (A (E x) (O x)))
= { isort-ap-even }
(I x)

mrge-isort

(Mg (I x) (I y))
= { Def I }
(Mg (In (F x) (I (R x))) (I y))
= { mrge-insert }
(In (F x) (Mg (I (R x)) (I y)))
= { IH }
(In (F x) (I (A (R x) y)))
= { Def I }
(I (cons (F x) (A (R x) y)))
= { Def ap }
(I (A x y))

mrge-insert
Leave to theorem prover

isort-ap-even
(I (A (E x) (E (R x))))
= { Def E, A }
(I (cons (F x) (A (E (R (R x))) (E (R x)))))
= { Def I }
(In (F x) (I (A (E (R (R x))) (E (R x)))))
= { Def E }
(In (F x) (I (A (E (R (R x))) (cons (F (R x)) (E (R (R (R x))))))))
= { isort-ap }
(In (F x) (In (F (R x)) (I (A (E (R (R x))) (E (R (R (R x))))))))
= { IH }
(In (F x) (In (F (R x)) (I (R (R x)))))
= { Def I }
(In (F x) (I (R x)))
= { Def I }
(I x)

|#

(property mrge-insert-list (e :all x :tl)
  (== (mrge (list e) x) (insert e x))
  :hints (("goal" :induct (tlp x))))

(property mrge-insert (e :all x y :tl)
  (== (mrge (insert e x) y)
      (insert e (mrge x y)))
  :hints (("goal" :induct (mrge x y))))

(property mrge-isort (x y :tl)
  (== (mrge (isort x) (isort y))
      (isort (app x y)))
  :hints (("goal" :induct (tlp x))))

(property insert-insert (a b :all x :tl)
  (== (insert a (insert b x))
      (insert b (insert a x)))
  :hints (("goal" :induct (tlp x))))

(property isort-ap (x y :tl e :all)
  (== (isort (app x (cons e y)))
      (insert e (isort (app x y))))
  :hints (("goal" :induct (tlp x))))

(property isort-ap-even (x :tl)
  (== (isort (app (even-els x) (even-els (cdr x))))
      (isort x))
  :hints (("goal" :induct (even-els x))))

(property mrge-sort=isort (x :tl)
  (== (mrge-sort x) (isort x))
  :hints (("goal" :induct (mrge-sort x))))

(property mrge-sort-perm (x :tl)
  (permp (mrge-sort x) x))
