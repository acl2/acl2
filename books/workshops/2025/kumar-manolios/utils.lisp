(in-package "ACL2S")

(definec <<= (x :all y :all) :bool
  (v (== x y)
     (<< x y)))

(definec insert-unique (a :all x :tl) :tl
  (match x
    (() (list a))
    ((!a . &) x)
    ((e . es) (if (<< a e)
                  (cons a x)
                (cons e (insert-unique a es))))))

(definec isort-set (x :tl) :tl
  (match x
    (() ())
    ((e . es) (insert-unique e (isort-set es)))))

(property insert-unique-commute (a :all b :all x :tl)
  (== (insert-unique a (insert-unique b x))
      (insert-unique b (insert-unique a x))))

(property insert-unique-insert-unique (a :all x :tl)
  (== (insert-unique a (insert-unique a x))
      (insert-unique a x)))

(property isort-set-insert-unique-commute (x :tl a :all)
  (== (isort-set (insert-unique a x))
      (insert-unique a (isort-set x))))

(property isort-set-isort-set-eq (x :tl)
  (== (isort-set (isort-set x))
      (isort-set x)))

(property isort-set-app-mid (x y :tl a :all)
  (== (isort-set (append y (cons a x)))
      (insert-unique a (isort-set (append y x)))))

(property isort-set-nil (x :tl)
  (== (not (isort-set x))
      (not x)))

(property in-isort-set (x :tl m :all)
  (== (in m (isort-set x))
      (in m x)))

(property insert-unique-in-isort-set (x :tl m :all)
  :h (in m (isort-set x))
  (== (insert-unique m (isort-set x))
      (isort-set x)))

(definec union-set (x y :tl) :tl
  (match x
    (() (isort-set y))
    ((r . rs) (insert-unique r (union-set rs y)))))

(property union-set-mid (x y :tl a :all)
  (== (union-set x (cons a y))
      (insert-unique a (union-set x y))))

(property union-set-mid2 (x y :tl a :all)
  (== (union-set (cons a x) y)
      (insert-unique a (union-set x y))))

(property union-set-mid3 (x y :tl a :all)
  (== (union-set x (insert-unique a y))
      (insert-unique a (union-set x y))))

(property isort-set-union-set (x y :tl)
  (== (isort-set (union-set x y))
      (union-set x y)))

(property prop=union-set-nil (x :tl)
  (== (union-set x nil)
      (isort-set x)))

(property prop=union-set-nil2 (x :tl)
  (== (union-set nil x)
      (isort-set x)))

(propertyd union-set-symm (x y :tl)
  (== (union-set x y)
      (union-set y x)))

(property union-set-eq-x (x y :tl)
  (=> (not (union-set x y))
      (^ (endp x)
         (endp y))))

(property union-set-isort-set (x y :tl)
  (== (union-set x (isort-set x))
      (isort-set x)))

(property member-insert-unique (x :tl m n :all)
  (=> (member-equal m x)
      (member-equal m (insert-unique n x))))

(property not-member-insert-unique (x :tl m n :all)
  (=> (^ (! (member-equal m x))
         (!= m n))
      (! (member-equal m (insert-unique n x)))))

(property insert-unique-diff (x y :tl m :all)
  (=> (not (member-equal m x))
      (== (set-difference-equal x (insert-unique m y))
          (set-difference-equal x y))))

(property in-insert-unique (m :all x :tl)
  (in m (insert-unique m x)))

(propertyd insert-member-isort (x :tl m :all)
  (=> (member-equal m x)
      (== (insert-unique m (isort-set x))
          (isort-set x))))

(property set-diff-insert-unique (x y :tl m :all)
  :h (member-equal m y)
  (== (set-difference-equal (insert-unique m x) y)
      (set-difference-equal x y)))

(encapsulate ()
  (local
   (property prop=in-member (x :tl m :all)
     (iff (in m x)
          (member-equal m x))))
  
  (property set-diff-insert-unique2 (x y :tl m :all)
    :h (in m y)
    (== (set-difference-equal (insert-unique m x) y)
        (set-difference-equal x y)))

  (property insert-unique-diff-in (x y :tl m :all)
    :h (not (in m x))
    (== (set-difference-equal x (insert-unique m y))
        (set-difference-equal x y))
    :hints (("Goal" :use ((:instance
                           insert-unique-diff))))))

(property diff-nil (x :tl)
  (== (set-difference-equal x '())
      x))

(property in-union (x y :tl m :all)
  (=> (in m x)
      (in m (union-set x y))))

(property not-in-union (x y :tl m :all)
  (== (^ (! (in m x))
         (! (in m y)))
      (! (in m (union-set x y)))))

(property in-union2 (x y :tl m :all)
  (=> (in m (union-set x y))
      (v (in m x) (in m y))))

(propertyd in-union3 (x y :tl m :all)
  :h (^ (! (in m y))
        (in m (union-set x y)))
  (in m x))

(property not-in-diff (x y :tl m :all)
  :h (! (in m x))
  (! (in m (set-difference-equal x y))))

(property not-in-insert-diff (x y :tl m a :all)
  :h (! (in m (set-difference-equal x y)))
  (! (in m (set-difference-equal x (insert-unique a y)))))

(property prop=member-set-difference-union (x y z :tl m :all)
  :h (! (member-equal m (set-difference-equal x y)))
  (! (member-equal m (set-difference-equal x (union-set y z)))))

(property rearrange-insert (x y :tl m :all)
  (== (union-set (insert-unique m x)
                 y)
      (insert-unique m (union-set x y))))

(propertyd in-diff1 (x y :tl m :all)
  :h (^ (! (in m (set-difference-equal x y)))
        (in m x))
  (in m y))

(propertyd not-in-diff2 (x y :tl m :all)
  :h (in m y)
  (not (in m (set-difference-equal x y))))

(propertyd insert-unique-union-set (x y :tl m :all)
  :h (in m (union-set x y))
  (== (insert-unique m (union-set x y))
      (union-set x y))
  :instructions
  (:pro
   (:claim (== (union-set x y)
               (isort-set (union-set x y))))
   (:claim (in m (isort-set (union-set x y))))
   (:claim (== (insert-unique m (isort-set (union-set x y)))
               (isort-set (isort-set (union-set x y))))
           :hints (("Goal" :use ((:instance insert-unique-in-isort-set
                                            (x (union-set x y)))))))
   :prove
   ))

(encapsulate ()
  (local 
   (property prop=in-member (x :tl m :all)
     (iff (in m x)
          (member-equal m x))))
  (propertyd prop=in-set-difference-union2 (x y z :tl m :all)
    :h (! (in m x))
    (== (in m (set-difference-equal z (union-set x y)))
        (in m (set-difference-equal z y)))))


(definec orderedp (x :tl) :boolean
  (match x
    (() t)
    ((&) t)
    ((a . (b . &)) (^ (<< a b)
                      (orderedp (cdr x))))))

(property isort-ordered (x :tl)
  (orderedp (isort-set x)))

(property insert-unique-ordered (x :tl m :all)
  :h (orderedp x)
  (orderedp (insert-unique m x)))

(property union-set-ordered (x y :tl)
  (orderedp (union-set x y)))

(property orderedp-cdr (x :tl)
  :h (orderedp x)
  (orderedp (cdr x)))

(property not-in-rem (x :tl m :all)
  (! (in m (remove-equal m x))))

(property insert-unique-remove-ordered (r a :all x :tl)
  :h (^ (!= r a)
        (orderedp x))
  (equal (insert-unique a (remove-equal r x))
         (remove-equal r (insert-unique a x))))

(property insert-unique-remove-ordered2 (r :all x :tl)
  :h (orderedp x)
  (equal (remove-equal r (insert-unique r x))
         (remove-equal r x)))

(property insert-unique-remove-ordered3 (r :all x :tl)
  :h (^ (orderedp x)
        (in r x))
  (== (insert-unique r (remove-equal r x))
      x))

(property insert-unique-union (x y :tl m :all)
  :h (in m (union-set x y))
  (== (insert-unique m (union-set x y))
      (union-set x y))
  :instructions
  (:pro
   (:claim (== (union-set x y) (isort-set (union-set x y))))
   (= (union-set x y) (isort-set (union-set x y)))
   (:claim (in m (isort-set (union-set x y))))
   (:prove :hints (("Goal"
                    :use ((:instance insert-unique-in-isort-set
                                     (x (union-set x y)))))))
   ))


(propertyd in-m-remove-union-set (x y :tl m :all)
  :h (in m (union-set (remove-equal m x) y))
  (== (union-set (remove-equal m x) y)
      (union-set x y))
  :instructions
  (:pro
   :induct :pro
   (:claim (in m (union-set (remove-equal m (cdr x)) y)))
   (:claim (equal (union-set (remove-equal m (cdr x)) y)
                  (union-set (cdr x) y)))
   (= (remove-equal m x) (cons (car x) (remove-equal m (cdr x))))
   (= (union-set (cons (car x) (remove-equal m (cdr x))) y)
      (insert-unique (car x) (union-set (remove-equal m (cdr x)) y)))
   (= (union-set (remove-equal m (cdr x)) y) (union-set (cdr x) y))
   :bash :pro
   (:claim (equal (union-set (remove-equal m (cdr x)) y)
                  (union-set (cdr x) y)))
   (= (remove-equal m x)
      (remove-equal m (cdr x)))
   :bash
   :bash))


(propertyd not-in-m-remove-union-set (x y :tl m :all)
  :h (! (in m (union-set (remove-equal m x) y)))
  (== (union-set (remove-equal m x) y)
      (remove-equal m (union-set x y)))
  :instructions
  (:pro 

   (:claim (^ (! (in m (remove-equal m x))) (! (in m y)))
           :hints (("Goal" :use ((:instance not-in-union
                                            (x (remove-equal m x)))))))
   :induct :pro
   (:claim (not (in m (remove-equal m (cdr x)))))
   (:claim (not (in m (union-set (remove-equal m (cdr x)) y)))
           :hints (("Goal" :use ((:instance not-in-union
                                            (x (remove-equal m (cdr
                                                                x))))))))
   (:claim (equal (union-set (remove-equal m (cdr x)) y)
                  (remove-equal m (union-set (cdr x) y))))

   (= (remove-equal m x) (cons (car x) (remove-equal m (cdr x))))
   (= (union-set (cons (car x) (remove-equal m (cdr x))) y)
      (insert-unique (car x) (union-set (remove-equal m (cdr x)) y)))
   (= (union-set (remove-equal m (cdr x)) y)
      (remove-equal m (union-set (cdr x) y)))
   (= (union-set x y)
      (insert-unique (car x) (union-set (cdr x) y)))
   (= (union-set (cdr x) y)
      (isort-set (union-set (cdr x) y)))
   (:claim (orderedp (isort-set (union-set (cdr x) y))))
   (:claim (equal (insert-unique (car x)
                                 (remove-equal m (isort-set (union-set (cdr x) y))))
                  (remove-equal m
                                (insert-unique (car x)
                                               (isort-set (union-set (cdr x)
                                                                     y)))))
           :hints (("Goal" :use ((:instance insert-unique-remove-ordered
                                            (r m)
                                            (a (car x))
                                            (x (isort-set (union-set (cdr x)
                                                                     y))))))))
   :s :pro
   (:claim (not (in m (remove-equal m (cdr x)))))
   (:claim (not (in m (union-set (remove-equal m (cdr x)) y)))
           :hints (("Goal" :use ((:instance not-in-union
                                            (x (remove-equal m (cdr
                                                                x))))))))
   (:claim (equal (union-set (remove-equal m (cdr x)) y)
                  (remove-equal m (union-set (cdr x) y))))
   (= (remove-equal m x)
      (remove-equal m (cdr x)))
   (= (union-set (remove-equal m (cdr x)) y)
      (remove-equal m (union-set (cdr x) y)))
   (= (union-set x y)
      (insert-unique (car x) (union-set (cdr x) y)))
   (= m (car x))
   (:claim (orderedp (union-set (cdr x) y)))
   
   (= (remove-equal (car x)
                    (insert-unique (car x)
                                   (union-set (cdr x) y)))
      (remove-equal (car x)
                    (union-set (cdr x) y))
      :hints (("Goal" :use ((:instance insert-unique-remove-ordered2
                                       (r (car x))
                                       (x (union-set (cdr x) y)))))))
   :s :bash
   (:claim (! (in m (isort-set y))))
   (= (remove-equal m (isort-set y))
      (isort-set y))))


(property remove-union-set-options (x y :tl m :all)
  (v (== (union-set (remove-equal m x) y)
         (remove-equal m (union-set x y)))
     (== (union-set (remove-equal m x) y)
         (union-set x y)))
  :hints (("Goal" :use (in-m-remove-union-set
                        not-in-m-remove-union-set))))

(property prop=union-set-order (x y z :tl)
  :h (== (isort-set z) z)
  (== (union-set x (union-set y z))
      (union-set y (union-set x z))))


(property prop=subsetp-equal-insert-unique (x y :tl)
  :h (^ x
        (subsetp-equal x y)
        (== (isort-set y) y))
  (== (insert-unique (car x) y) y)
  :hints (("Goal" :use ((:instance insert-member-isort
                                   (m (car x))
                                   (x y))))))

(property prop=subsetp-equal-isort-set (x y :tl)
  :h (^ (subsetp-equal x y)
        (== (isort-set y) y))
  (== (union-set x y) y))

(property prop=set-diff-nil-subset (xs ys :tl)
  :h (== (set-difference-equal xs ys) nil)
  (subsetp-equal xs ys))

(property insert-in-ordered (m :all x :tl)
  :h (^ (in m x)
        (orderedp x))
  (== (insert-unique m x)
      x))

;;------------- DATA DEFINITIONS ------------------------

(defdata-alias peer nat)
(defdata-alias lop nat-list)
(defdata-alias topic var)

;; Peers are identified by natural numbers
;; Topics are identified by variables
;; A message contains payload, topic and originating peer
(defdata mssg (record
               (pld . string)
               (tp . topic)
               (or . peer)))

(property mssg-check-prop (x :mssg)
  (^ (stringp (mget :pld x))
     (topicp (mget :tp x))
     (peerp (mget :or x)))
  :hints (("Goal" :in-theory (enable mssgp)))
  :rule-classes :forward-chaining)

(sig isort-set ((listof :a)) => (listof :a))
(sig insert-unique (:a (listof :a)) => (listof :a))

(defdata lom (listof mssg))
(defdata lot (listof topic))
(defdata topic-lop-map (map topic lop))
