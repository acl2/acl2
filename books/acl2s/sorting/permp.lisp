(in-package "ACL2S")

; Started with sorting/perm.lisp, but modified by: (1) using ACL2s
; syntax (2) adding rule classes for efficient reasoning and (3)
; keeping all rules enabled (4) added some rules.

(definec del (e :all l :tl) :tl
  (match l
    (nil nil)
    ((!e . r) r)
    ((f . r) (cons f (del e r)))))

(sig del (all (listof :a)) => (listof :a))

(definec permp (x y :tl) :bool
  (match x
    (nil (endp y))
    ((f . r) (and (in f y) (permp r (del f y))))))

(property permp-cons (e :all x y :tl)
  :h (in e x)
  :b (== (permp (del e x) y)
         (permp x (cons e y)))
  :hints (("Goal" :induct (permp x y)))
  :rule-classes ((:forward-chaining :trigger-terms ((permp (del e x) y)))))

(property permp-symmetric (x y :tl)
  :h (permp x y)
  :b (permp y x))

(property in-del (a b :all x :tl)
  :h (in a (del b x))
  :b (in a x)
  :rule-classes :forward-chaining)

(property permp-in (e :all x y :tl)
  :h (and (permp x y)
          (in e x))
  :b (in e y)
  :rule-classes ((:forward-chaining :match-free :all)))

(property del-del (a b :all x :tl)
  (== (del b (del a x))
      (del a (del b x))))

(property in-del2 (a b :all x :tl)
  :h (and (!= a b) (in a x))
  :b (in a (del b x)))
      
(property permp-del (e :all x y :tl)
  :h (permp x y)
  :b (permp (del e x) (del e y)))

(property permp-reflexive (x :tl)
  (permp x x))

; So now permp is an equivalence relation
(property permp-transitive (x y z :tl)
  :h (and (permp x y) (permp y z))
  :b (permp x z)
  :rule-classes ((:forward-chaining :match-free :all)))
  
