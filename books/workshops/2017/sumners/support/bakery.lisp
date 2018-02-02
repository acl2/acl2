; Copyright (C) 2017, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "trans-theory")

#|

Bakery algorithm example for reducing the fair stuttering refinement proof to
properties relating transaction states or task states or t-states.

The final form in the book is:

  (prove-tr-refinement bake-impl bake-spec)

Which proves the properties required of bake-impl and showing that it is a
refinement of bake-spec. See the book "trans-theory.lisp" for the generated
lemmas from this macro ("proven" to ensure fair stuttering refinement via
the proofs in trans-theory.lisp and general-theory.lisp).

The pertinent defintions in this file supporting the required lemmas for this
tr-refinement proof are the following:

SYSTEM DEFINITION functions for specification system bake-spec:

(bake-spec-t-init a k)     -- init predicate checking that t-state "a" is a valid state for the given key "k".
(bake-spec-t-next a b k x) -- next-state relation checking that t-state "a" can transition to t-state "b" for given key "k" in system state "x".
(bake-spec-t-blok a b)     -- blocking relation which returns T iff the t-state "b" can block the t-state "a" from transitioning.

SYSTEM DEFINITION functions for implementation system bake-impl:

(bake-impl-t-init a k)     -- init predicate checking that t-state "a" is a valid state for the given key "k".
(bake-impl-t-next a b k x) -- next-state relation checking that t-state "a" can transition to t-state "b" for given key "k" in system state "x".
(bake-impl-t-blok a b)     -- blocking relation which returns T iff the t-state "b" can block the t-state "a" from transitioning.

SYSTEM STATE PROPERTY functions for implementation system bake-impl:

(bake-impl-iinv x)         -- predicate on system states "x" which is an inductive invariant -- provably true across system steps.

SYSTEM VALID PROGRESS functions for implementation system bake-impl:

(bake-impl-t-nlock k x)    -- function mapping key "k" and system state "x" to an ordinal ensuring no blocking cycles exist in "x".
(bake-impl-t-noblk a b)    -- relation on t-states "a" and "b" ensuring that "b" will invariantly no longer block "a" until "a" steps.
(bake-impl-t-nstrv a b)    -- function mapping t-states "a" and "b" to nat. list (see bounded-ords.lisp) which decreases until noblk reached.
(bake-impl-nst-bnd)        -- function returning natural providing a bound on the length of the (bake-impl-t-nstrv a b).

SYSTEM MAPPING PROPERTY functions for implementation system bake-impl:

(bake-impl-t-map a)        -- function mapping an implementation t-state "a" to a specification t-state which should match behavior.
(bake-impl-t-rank a)       -- function mapping a t-state "a" to an ordinal which should strictly decrease on unmatched transitions.

Most of the required lemmas go through automatically and most of the work
reduces to defining and proving an inductive invariant which ensures the
conditions sufficient to prove the remaining properties. 

|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; bakery specification defintion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (enable o-p o<))

(defun != (x y) (not (equal x y)))

(defthm s-not-equal
  (implies (not (equal a b))
           (not (equal (s k a x) (s k b y))))
  :hints (("Goal" 
           :in-theory (disable g-of-s-redux g-same-s)
           :use ((:instance g-of-s-redux 
                            (a k)
                            (b k)
                            (v a)
                            (r x))
                 (:instance g-of-s-redux 
                            (a k)
                            (b k)
                            (v b)
                            (r y))))))


(defmacro upd (x &rest upds)
  (cond ((atom upds) x)
        ((atom (rest upds)) x)
        (t `(s ,(first upds) ,(second upds)
               (upd ,x ,@(cddr upds))))))

(defun max-pos* (x s)
  (declare (xargs :measure (card s)))
  (if (null s) 0
    (nfix (max (g :pos (g (scar s) x))
               (max-pos* x (scdr s))))))

(defun max-pos (x) (max-pos* x (keys)))

(defun max-load* (x s)
  (declare (xargs :measure (card s)))
  (if (null s) 0
    (nfix (max (g :load (g (scar s) x))
               (max-load* x (scdr s))))))

(defun max-load (x) (max-load* x (keys)))

(defun bake-spec-t-init (a k)
  (declare (ignore k))
  (and (= (g :loc a)  'idle)
       (= (g :pos a)  1)
       (= (g :load a) 1)))

(defun bake-spec-t-next (a b k x)
  (declare (ignore k))
  (case (g :loc a)
    (idle       (and (=  (g :loc b)  'loaded)
                     (=  (g :pos b)  (g :pos a))
                     (natp (g :load b))
                     (>  (g :load b) (max-pos x))
                     (>= (g :load b) (max-load x))))
    (loaded     (= b (upd a :loc 'interested
                             :pos (g :load a))))
    (interested (= b (upd a :loc 'go)))
    (go         (= b (upd a :loc 'idle)))))

(defun bake-spec-t-blok (a b)
  (and (= (g :loc a) 'interested)
       (or (= (g :loc b) 'go)
           (and (= (g :loc b) 'interested)
                (< (g :pos b) (g :pos a))))))

(def-tr-system-defs bake-spec)

;;;; bakery implementation defintion

(defun lex< (p q r s)
  (or (< p r) (and (equal p r) (< q s))))

(defun curr-sh-max* (x s)
  (declare (xargs :measure (card s)))
  (if (null s) 0
    (nfix (max (g :sh-max (g (scar s) x))
               (curr-sh-max* x (scdr s))))))

(defun curr-sh-max (x) (curr-sh-max* x (keys)))

(defun ndx* (k s)
  (declare (xargs :measure (card s)))
  (cond ((null s) 0)
        ((= (scar s) k) 1)
        (t (1+ (ndx* k (scdr s))))))

(defun ndx (k) (ndx* k (keys)))

;;;; bakery intermediate definition

(defun bake-impl-t-init (a k)
  (= a (upd nil :loc 0 :key k :pos 1 :old-pos 0 :temp 0 :sh-max 1)))

(defun bake-impl-t-next (a b k x)
  (declare (ignore k))
  (case (g :loc a)
        (0 (= b (upd a :loc 1 :choosing t)))
        (1 (= b (upd a :loc 2 :temp (curr-sh-max x))))
        (2 (= b (upd a :loc 3 :pos (1+ (g :temp a))
                              :old-pos (g :pos a)
                              :pos-valid t)))
        (3 (= b (upd a :loc 4 :sh-max (if (> (curr-sh-max x) (g :temp a))
                                           (curr-sh-max x)
                                         (g :pos a)))))
        (4 (= b (upd a :loc 5 :choosing nil)))
        (5 (= b (upd a :loc 6)))
        (6 (= b (upd a :loc 7))) ;; we are potentially blocked here
        (t (= b (upd a :loc 0 :pos-valid nil)))))

(defun bake-impl-t-blok (a b)
  (or (and (= (g :loc a) 5)
           (g :choosing b))
      (and (= (g :loc a) 6)
           (and (g :pos-valid b)
                (lex< (g :pos b) (ndx (g :key b))
                      (g :pos a) (ndx (g :key a)))))))

(def-tr-system-defs bake-impl)

;;; we need the mapping def.s earlier to have them to define properties
;;; of the invariant:

(defun bake-impl-t-map (a)
  (upd nil
       :loc  (case (g :loc a)
                   ((0 1) 'idle)
                   ((2 3) 'loaded)
                   ((4 5 6) 'interested)
                   (t 'go))
       :pos  (case (g :loc a)
                   (3 (g :old-pos a))
                   (t (g :pos a)))
       :load (case (g :loc a)
                   (2 (1+ (g :temp a)))
                   (t (g :pos a)))))

(defun bake-impl-t-rank (a)
  (case (g :loc a)
        (0 1)       (1 0)
        (2 1)       (3 0)
        (4 2) (5 1) (6 0)
        (t 0)))

(def-tr-mapping-defs bake-impl)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; inductive invariant definition
;; 
;; there are 3 parts to the inductive invariant:
;;
;; 1. (t-iinv a k) which is simply the "local" invariant for each task and is
;;    pretty easily proven over any transition.
;;
;; 2. (m-iinv a x) which relates each task state to the (curr-sh-max x) and
;;    related properties (relies on the t-iinv).
;;
;; 3. (x-iinv a b) which relates amy invariants about a pair of t-states a,b
;;    and builds from the t-iinv and m-iinv to get the properties about which
;;    pair states cannot be reached.
;;
;; this is the bulk of the "work" in this book and i would contend represents
;; the work necessary to do even a basic refinement proof of the bakery algorithm..
;; (basically this amounts to an argument that the fair progress in this case
;; is substantially less work but that is an unproven claim for sure and only
;; applicable in this case to the bakery algorithm .. YMMV).

(defun t-iinv (a k)
  (and (natp (g :pos a))
       (natp (g :old-pos a))
       (natp (g :temp a))
       (natp (g :loc a))
       (natp (g :sh-max a))
       (equal (g :key a) k)
       (<= (g :loc a) 7)
       (= (g :choosing a)
          (and (>= (g :loc a) 1)
               (<= (g :loc a) 4)))
       (= (g :pos-valid a)
          (and (>= (g :loc a) 3)
               (<= (g :loc a) 7)))
       (implies (not (= (g :loc a) 2))
                (= (1+ (g :temp a)) (g :pos a)))))

(defun t-iinv* (x s)
  (declare (xargs :measure (card s)))
  (or (null s)
      (and (t-iinv (g (scar s) x) (scar s))
           (t-iinv* x (scdr s)))))

(defthm t-iinv-t-next
  (implies (and (t-iinv a k)
                (bake-impl-t-next a b k x))
           (t-iinv b k)))

;; now we provide rules to t-iinv and t-iinv* cause we are going to disable them by default:

(defthm t-iinv-sh-max
  (implies (t-iinv (g k x) k) (natp (g :sh-max (g k x))))
  :rule-classes ((:type-prescription :typed-term (g :sh-max (g k x)))))

(defthm t-iinv-temp
  (implies (t-iinv (g k x) k) (natp (g :temp (g k x))))
  :rule-classes :type-prescription)

(defthm t-iinv-pos
  (implies (t-iinv (g k x) k) (natp (g :pos (g k x))))
  :rule-classes :type-prescription)

(defthm t-iinv-old-pos
  (implies (t-iinv (g k x) k) (natp (g :old-pos (g k x))))
  :rule-classes :type-prescription)

(defthm t-iinv-loc
  (implies (t-iinv (g k x) k) (natp (g :loc (g k x))))
  :rule-classes :type-prescription)

(defthm t-iinv-loc2
  (implies (t-iinv (g k x) k) (<= (g :loc (g k x)) 7))
  :rule-classes :forward-chaining)

(defthm t-iinv-key
  (implies (t-iinv (g k x) k) (equal (g :key (g k x)) k)))

(defthm t-iinv-choosing
  (implies (t-iinv (g k x) k)
           (equal (g :choosing (g k x))
                  (and (>= (g :loc (g k x)) 1)
                       (<= (g :loc (g k x)) 4)))))

(defthm t-iinv-pos-valid
  (implies (t-iinv (g k x) k)
           (equal (g :pos-valid (g k x))
                  (and (>= (g :loc (g k x)) 3)
                       (<= (g :loc (g k x)) 7)))))

(defthm t-iinv-temp+1
  (implies (and (t-iinv (g k x) k) 
                (not (equal (g :loc (g k x)) 2)))
           (equal (1+ (g :temp (g k x))) 
                  (g :pos (g k x))))
  :rule-classes (:linear :rewrite))

(in-theory (disable t-iinv))

(defthm t-iinv*-g-k
  (implies (and (t-iinv* x s) (in k s))
           (t-iinv (g k x) k))
  :rule-classes ((:forward-chaining :trigger-terms ((t-iinv* x s)))))

(defthm t-iinv*-g-scar
  (implies (and (t-iinv* x s) s)
           (t-iinv (g (scar s) x) (scar s)))
  :rule-classes ((:forward-chaining :trigger-terms ((t-iinv* x s)))))

(defthm curr-sh-max-p1
  (implies (and (in k s) (t-iinv* x s))
           (<= (g :sh-max (g k x))
               (curr-sh-max* x s)))
  :rule-classes (:linear :rewrite))

(defthm curr-sh-max-p2.1
  (implies (and (==-but x y k s)
                (not (in k s)))
           (equal (curr-sh-max* y s)
                  (curr-sh-max* x s))))

(defthm curr-sh-max-p2
  (implies (and (==-but x y k s)
                (in k s)
                (t-iinv* x s)
                (t-iinv* y s)
                (>= (g :sh-max (g k y))
                    (g :sh-max (g k x))))
           (equal (curr-sh-max* y s)
                  (nfix (max (g :sh-max (g k y))
                             (curr-sh-max* x s))))))

(defthm curr-sh-max-p2*
  (implies (and (==-but x y k (keys))
                (in k (keys))
                (t-iinv* x (keys))
                (t-iinv* y (keys))
                (>= (g :sh-max (g k y))
                    (g :sh-max (g k x))))
           (equal (curr-sh-max y)
                  (nfix (max (g :sh-max (g k y))
                             (curr-sh-max x))))))

(in-theory (disable curr-sh-max))

(defthm g-k-y-junk
  (implies (equal (g k y) a)
           (equal (g f (g k y)) (g f a)))
  :rule-classes nil)

(defun m-iinv (a x)
  (and (<= (g :temp a)   (curr-sh-max x))
       (<= (g :sh-max a) (curr-sh-max x))
       (if (= (g :loc a) 3)
           (<= (g :pos a) (1+ (curr-sh-max x)))
         (<= (g :pos a) (curr-sh-max x)))
       (implies (= (g :loc a) 2)
                (>= (g :temp a) (g :pos a)))
       (< (g :old-pos a) (g :pos a))))

(defthm m-iinv-t-next
  (implies (and (t-iinv* x (keys))
                (t-iinv* y (keys))
                (key-p k)
                (==-but x y k (keys))
                (bake-impl-t-next (g k x) (g k y) k x)
                (m-iinv (g k x) x))
           (m-iinv (g k y) y))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable curr-sh-max-p2*)
           :use ((:instance curr-sh-max-p2*)))
          ("Subgoal 74" :cases ((equal (g :pos (g k x)) (g :pos (g k y))))
           :use ((:instance g-k-y-junk
                            (f :pos)
                            (a (S :LOC 4 (S :SH-MAX (CURR-SH-MAX X) (G K X)))))
                 (:instance t-iinv-temp+1)))))

(defthm m-iinv-t-next-o
  (implies (and (t-iinv* x (keys))
                (t-iinv* y (keys))
                (key-p k)
                (key-p l)
                (not (equal k l))
                (==-but x y k (keys))
                (bake-impl-t-next (g k x) (g k y) k x)
                (m-iinv (g l x) x)
                (m-iinv (g k x) x))
           (m-iinv (g l y) y))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable curr-sh-max-p2*)
           :use ((:instance curr-sh-max-p2*)))))

(defthm m-iinv-temp
  (implies (m-iinv a x) (<= (g :temp a) (curr-sh-max x)))
  :rule-classes (:linear :rewrite))

(defthm m-iinv-sh-max
  (implies (m-iinv a x) (<= (g :sh-max a) (curr-sh-max x)))
  :rule-classes (:linear :rewrite))

(defthm m-iinv-pos-3
  (implies (and (m-iinv a x) (equal (g :loc a) 3))
           (<= (g :pos a) (1+ (curr-sh-max x))))
  :rule-classes (:linear :rewrite))

(defthm m-iinv-pos-n3
  (implies (and (m-iinv a x) (not (equal (g :loc a) 3)))
           (<= (g :pos a) (curr-sh-max x)))
  :rule-classes (:linear :rewrite))

(defthm m-iinv-temp-pos
  (implies (and (m-iinv a x) (equal (g :loc a) 2))
           (>= (g :temp a) (g :pos a)))
  :rule-classes (:linear :rewrite))

(defthm m-iinv-old-pos
  (implies (m-iinv a x)
           (< (g :old-pos a) (g :pos a)))
  :rule-classes (:linear :rewrite))

(in-theory (disable m-iinv))

(defthm ndx->-0-if-in
  (implies (in k s)
           (> (ndx* k s) 0))
  :rule-classes (:linear :rewrite))

(defthm ndx-unique
  (implies (and (in k s) (in l s))
           (equal (equal (ndx* k s) (ndx* l s))
                  (equal k l))))
                              
(defun x-iinv (a b)
  (and (implies (and (= (g :loc a) 2)
                     (or (not (g :pos-valid b))
                         (= (g :loc b) 6)
                         (= (g :loc b) 7)))
                (<= (g :pos b) (g :temp a)))
       (implies (and (= (g :loc b) 7)
                     (g :pos-valid a))
                (if (= (g :pos a) (g :pos b))
                    (< (ndx (g :key b)) (ndx (g :key a)))
                  (< (g :pos b) (g :pos a))))
       (implies (and (g :pos-valid a)
                     (not (g :pos-valid b)))
                (<= (g :pos b) (g :pos a)))))

;; the next two theorems take a little while but eventually get through..

(defthm x-iinv-t-next1
  (implies (and (x-iinv (g k x) (g l x))
                (x-iinv (g l x) (g k x))
                (m-iinv (g l x) x)
                (m-iinv (g k x) x)
                (key-p k)
                (key-p l)
                (not (equal k l))
                (t-iinv (g k x) k)
                (t-iinv (g l x) l)
                (==-but x y k (keys))
                (not (bake-impl-t-blok (g k x) (g l x)))
                (bake-impl-t-next (g k x) (g k y) k x))
           (x-iinv (g k y) (g l y))))

(defthm x-iinv-t-next2
  (implies (and (x-iinv (g k x) (g l x))
                (x-iinv (g l x) (g k x))
                (m-iinv (g l x) x)
                (m-iinv (g k x) x)
                (key-p k)
                (key-p l)
                (not (equal k l))
                (t-iinv (g k x) k)
                (t-iinv (g l x) l)
                (t-iinv (g k y) k)
                (==-but x y k (keys))
                (not (bake-impl-t-blok (g k x) (g l x)))
                (bake-impl-t-next (g k x) (g k y) k x))
           (x-iinv (g l y) (g k y))))

(defthm x-iinv-prop1
  (implies (and (x-iinv a b)
                (equal (g :loc a) 2)
                (or (not (g :pos-valid b))
                    (equal (g :loc b) 6)
                    (equal (g :loc b) 7)))
           (<= (g :pos b) (g :temp a)))
  :rule-classes (:linear :rewrite))

(defthm x-iinv-prop2-1
  (implies (and (x-iinv a b)
                (equal (g :loc b) 7)
                (g :pos-valid a)
                (equal (g :pos a) (g :pos b)))
           (< (ndx (g :key b)) (ndx (g :key a))))
  :rule-classes (:linear :rewrite))

(defthm x-iinv-prop2-2
  (implies (and (x-iinv a b)
                (equal (g :loc b) 7)
                (g :pos-valid a)
                (not (equal (g :pos a) (g :pos b))))
           (< (g :pos b) (g :pos a)))
  :rule-classes (:linear :rewrite))

(defthm x-iinv-prop3
  (implies (and (x-iinv a b)
                (g :pos-valid a)
                (not (g :pos-valid b)))
           (<= (g :pos b) (g :pos a)))
  :rule-classes (:linear :rewrite))

(in-theory (disable x-iinv))

(defun m-iinv* (x s)
  (declare (xargs :measure (card s)))
  (or (null s)
      (and (m-iinv (g (scar s) x) x)
           (m-iinv* x (scdr s)))))

(defun x-iinv** (x k s)
  (declare (xargs :measure (card s)))
  (or (null s)
      (and (or (equal k (scar s))
               (and (x-iinv (g k x) (g (scar s) x))
                    (x-iinv (g (scar s) x) (g k x))))
           (x-iinv** x k (scdr s)))))

(defun x-iinv* (x s)
  (declare (xargs :measure (card s)))
  (or (null s)
      (and (x-iinv** x (scar s) (keys))
           (x-iinv* x (scdr s)))))

(defun bake-impl-iinv (x)
  (and (t-iinv* x (keys))
       (m-iinv* x (keys))
       (x-iinv* x (keys))))

;; prove all of the invariant components (can assume local invariants to prove cross):

(defthm bake-impl-init*-g-k
  (implies (and (bake-impl-init* x s)
                (in k s))
           (bake-impl-t-init (g k x) k)))

(defthm bake-impl-init-g-k
  (implies (and (bake-impl-init x)
                (key-p k))
           (bake-impl-t-init (g k x) k))
  :hints (("Goal" :in-theory (disable bake-impl-t-init))))

(defthm t-iinv-t-init
  (implies (bake-impl-t-init a k)
           (t-iinv a k))
  :hints (("Goal" :in-theory (enable t-iinv))))

(defthm x-iinv-t-init
  (implies (and (bake-impl-t-init a k)
                (bake-impl-t-init b l))
           (x-iinv a b))
  :hints (("Goal" :in-theory (enable x-iinv))))

(defthm curr-sh-max-init*
  (implies (and s (bake-impl-init* x s))
           (equal (curr-sh-max* x s) 1)))

(defthm curr-sh-max-init
  (implies (bake-impl-init x)
           (equal (curr-sh-max x) 1))
  :hints (("Goal" :in-theory (enable curr-sh-max))))

(defthm m-iinv-t-init
  (implies (and (bake-impl-t-init a k)
                (equal (curr-sh-max x) 1))
           (m-iinv a x))
  :hints (("Goal" :in-theory (enable m-iinv))))

(defthm t-iinv*-init
  (implies (bake-impl-init* x s)
           (t-iinv* x s)))

;; we shouldn't need to open these definitions until we are done with the invariant:
(in-theory (disable bake-impl-t-init 
                    bake-impl-t-next 
                    bake-impl-t-blok))

(defthm m-iinv*-init
  (implies (and (bake-impl-init x)
                (bake-impl-init* x s)
                (subset s (keys)))
           (m-iinv* x s))
  :hints (("Subgoal *1/5" :in-theory (disable m-iinv-t-init)
           :use ((:instance m-iinv-t-init
                            (a (g (scar s) x))
                            (k (scar s)))))))

(defthm x-iinv**-init*
  (implies (and (bake-impl-init x)
                (bake-impl-init* x s)
                (subset s (keys))
                (key-p k))
           (x-iinv** x k s))
  :hints (("Subgoal *1/5" :in-theory (disable x-iinv-t-init)
           :use ((:instance x-iinv-t-init
                            (a (g k x))
                            (b (g (scar s) x))
                            (l (scar s)))
                 (:instance x-iinv-t-init
                            (b (g k x))
                            (a (g (scar s) x))
                            (k (scar s))
                            (l k))))))

(defthm x-iinv*-init
  (implies (and (bake-impl-init x)
                (subset s (keys)))
           (x-iinv* x s)))

(DEFTHM BAKE-IMPL-S-IINV-INIT
  (IMPLIES (BAKE-IMPL-INIT X)
           (BAKE-IMPL-IINV X)))

;; now prove the invariant next step..

(defthm t-iinv*-key
  (implies (and (t-iinv* x (keys))
                (key-p k))
           (t-iinv (g k x) k)))

(defthm m-iinv*-g-k
  (implies (and (m-iinv* x s)
                (in k s))
           (m-iinv (g k x) x)))

(defthm m-iinv*-key
  (implies (and (m-iinv* x (keys))
                (key-p k))
           (m-iinv (g k x) x)))

(defthm x-iinv**-g-k
  (implies (and (x-iinv** x k s)
                (in l s)
                (not (equal k l)))
           (and (x-iinv (g k x) (g l x))
                (x-iinv (g l x) (g k x))))
  :rule-classes nil)

(defthm x-iinv*-g-k
  (implies (and (x-iinv* x s)
                (key-p k)
                (key-p l)
                (subset s (keys))
                (in k s)
                (in l s)
                (not (equal k l)))
           (and (x-iinv (g k x) (g l x))
                (x-iinv (g l x) (g k x))))
  :hints (("Subgoal *1/2"
           :use ((:instance x-iinv**-g-k
                            (k (scar s))
                            (l k)
                            (s (keys)))
                 (:instance x-iinv**-g-k
                            (k (scar s))
                            (s (keys))))))
  :rule-classes nil)

(defthm x-iinv*-key
  (implies (and (x-iinv* x (keys))
                (key-p k)
                (key-p l)
                (not (equal k l)))
           (and (x-iinv (g k x) (g l x))
                (x-iinv (g l x) (g k x))))
  :hints (("Goal" :use ((:instance x-iinv*-g-k (s (keys)))))))

(defthm t-iinv*-next
  (implies (and (t-iinv* x s)
                (subset s (keys))
                (key-p k)
                (==-but x y k (keys))
                (bake-impl-t-next (g k x) (g k y) k x))
           (t-iinv* y s))
  :hints (("Subgoal *1/5" :cases ((equal k (scar s)))
           :use ((:instance ==-but-g-k
                            (k (scar s))
                            (l k)
                            (s (keys))))))
  :rule-classes nil)

(defthm m-iinv*-next
  (implies (and (t-iinv* x (keys))
                (subset s (keys))
                (key-p k)
                (==-but x y k (keys))
                (bake-impl-t-next (g k x) (g k y) k x)
                (m-iinv* x (keys)))
           (m-iinv* y s))
  :hints (("Subgoal *1/4" 
           :cases ((equal (scar s) k))
           :in-theory (disable m-iinv-t-next
                               m-iinv-t-next-o)
           :use ((:instance t-iinv*-next
                            (s (keys)))
                 (:instance m-iinv-t-next
                            (k (scar s)))
                 (:instance m-iinv-t-next-o
                            (l (scar s))))))
  :rule-classes nil)

(defthm x-iinv**-next-=
  (implies (and (t-iinv* x (keys))
                (m-iinv* x (keys))
                (x-iinv* x (keys))
                (subset s (keys))
                (key-p k)
                (==-but x y k (keys))
                (bake-impl-t-next (g k x) (g k y) k x)
                (not (bake-impl-blok* x k (keys))))
           (x-iinv** y k s))
  :hints (("Subgoal *1/4"
           :cases ((equal k l))
           :use ((:instance bake-impl-blok*-prop1 (l (scar s)) (s (keys)))
                 (:instance x-iinv-t-next1 (l (scar s)))
                 (:instance x-iinv-t-next2 (l (scar s)))
                 (:instance t-iinv*-next (s (keys))))))
  :rule-classes nil)

(defthm x-iinv**-next!=
  (implies (and (t-iinv* x (keys))
                (m-iinv* x (keys))
                (x-iinv* x (keys))
                (subset s (keys))
                (key-p k)
                (key-p l)
                (not (equal k l))
                (==-but x y k (keys))
                (bake-impl-t-next (g k x) (g k y) k x)
                (not (bake-impl-blok* x k (keys))))
           (x-iinv** y l s))
  :rule-classes nil
  :hints (("Subgoal *1/4"
           :cases ((equal k (scar s)))
           :use ((:instance ==-but-g-k (l k) (k (scar s)) (s (keys)))
                 (:instance bake-impl-blok*-prop1 (l (scar s)) (s (keys)))
                 (:instance x-iinv-t-next1 (k (scar s)))
                 (:instance x-iinv-t-next2 (k (scar s)))
                 (:instance t-iinv*-next (s (keys)))))))

(defthm x-iinv*-next
  (implies (and (t-iinv* x (keys))
                (m-iinv* x (keys))
                (x-iinv* x (keys))
                (subset s (keys))
                (key-p k)
                (==-but x y k (keys))
                (bake-impl-t-next (g k x) (g k y) k x)
                (not (bake-impl-blok* x k (keys))))
           (x-iinv* y s))
  :hints (("Subgoal *1/4"
           :cases ((equal k (scar s)))
           :use ((:instance x-iinv**-next-= (k (scar s)) (s (keys)))
                 (:instance x-iinv**-next!= (l (scar s)) (s (keys))))))
  :rule-classes nil)

(DEFTHM BAKE-IMPL-S-IINV-NEXT
  (IMPLIES (AND (BAKE-IMPL-IINV X)
                (KEY-P K)
                (NOT (BAKE-IMPL-BLOK X K))
                (BAKE-IMPL-NEXT X Y K))
           (BAKE-IMPL-IINV Y))
  :hints (("Goal" :use ((:instance x-iinv*-next (s (keys)))
                        (:instance m-iinv*-next (s (keys)))
                        (:instance t-iinv*-next (s (keys))))))
  :RULE-CLASSES NIL)

(DEFTHM BAKE-IMPL-T-NEXT-MUST-CHANGE
  (EQUAL (BAKE-IMPL-T-NEXT A A K X) NIL)
  :hints (("Goal" :in-theory (enable bake-impl-t-next))))

(def-tr-system-props bake-impl)

;;;;; We now prove some sufficient conditions and then turn off the invariant
;;;;; definition.. these sufficient conditions are all that we needed from
;;;;; the invariant to prove the remaining properties:

(defthm suff1
  (implies (and (bake-impl-iinv x) (in k (keys)))
           (natp (g :pos (g k x))))
  :rule-classes (:type-prescription :rewrite))

(defthm suff2
  (implies (and (bake-impl-iinv x) (in k (keys)))
           (natp (g :old-pos (g k x))))
  :rule-classes (:type-prescription :rewrite))

(defthm suff3
  (implies (and (bake-impl-iinv x) (in k (keys)))
           (natp (g :temp (g k x))))
  :rule-classes (:type-prescription :rewrite))
  
(defthm suff4
  (implies (and (bake-impl-iinv x) (in k (keys)))
           (natp (g :loc (g k x))))
  :rule-classes (:type-prescription :rewrite))

(defthm suff5
  (implies (and (bake-impl-iinv x) (in k (keys)))
           (>= (g :loc (g k x)) 0))
  :rule-classes (:linear :rewrite))

(defthm suff6
  (implies (and (bake-impl-iinv x) (in k (keys)))
           (<= (g :loc (g k x)) 7))
  :rule-classes (:linear :rewrite))

(defthm suff7
  (implies (and (bake-impl-iinv x) (in k (keys)))
           (equal (g :choosing (g k x))
                  (and (>= (g :loc (g k x)) 1)
                       (<= (g :loc (g k x)) 4)))))

(defthm suff8
  (implies (and (bake-impl-iinv x) (in k (keys)))
           (equal (g :pos-valid (g k x))
                  (and (>= (g :loc (g k x)) 3)
                       (<= (g :loc (g k x)) 7)))))

(defthm suff9
  (implies (and (bake-impl-iinv x) (in k (keys))
                (not (equal (g :loc (g k x)) 2)))
           (equal (1+ (g :temp (g k x))) (g :pos (g k x)))))

;;;;;; need non-local x-iinv:

(defthm suff10
  (implies (and (bake-impl-iinv x) (in k (keys)))
           (< (g :old-pos (g k x)) (g :pos (g k x))))
  :hints (("Goal" :use ((:instance m-iinv-old-pos (a (g k x))))))
  :rule-classes (:rewrite :linear))

(defthm suff11
  (implies (and (bake-impl-iinv x) (in k (keys))
                (not (equal (g :loc (g k x)) 3)))
           (<= (g :pos (g k x)) (curr-sh-max x)))
  :rule-classes (:linear :rewrite))

(defthm bake-impl-map*-redx
  (implies (in k s)
           (equal (g k (bake-impl-map* x s))
                  (bake-impl-t-map (g k x))))
  :hints (("Goal" :in-theory (disable bake-impl-t-map))
          ("Subgoal *1/3" :cases ((equal (scar s) k)))))

(defthm suff12*
  (implies (and (bake-impl-iinv x)
                (subset s (keys)))
           (<= (max-load* (bake-impl-map* x (keys)) s)
               (+ 1 (curr-sh-max x))))
  :rule-classes (:rewrite :linear)
  :hints (("Subgoal *1/3"
           :in-theory (disable m-iinv-temp
                               m-iinv-pos-3
                               m-iinv-pos-n3)
           :use ((:instance m-iinv-temp
                            (a (g (scar s) x)))
                 (:instance m-iinv-pos-3
                            (a (g (scar s) x)))
                 (:instance m-iinv-pos-n3
                            (a (g (scar s) x)))))))

(defthm suff12
  (implies (bake-impl-iinv x)
           (<= (max-load* (bake-impl-map* x (keys)) (keys))
               (+ 1 (curr-sh-max x))))
  :rule-classes (:rewrite :linear))

(defthm suff13*
  (implies (and (bake-impl-iinv x)
                (subset s (keys)))
           (< (max-pos* (bake-impl-map* x (keys)) s)
              (+ 1 (curr-sh-max x))))
  :rule-classes (:rewrite :linear)
  :hints (("Subgoal *1/3"
           :in-theory (disable m-iinv-temp
                               m-iinv-pos-3
                               m-iinv-pos-n3)
           :use ((:instance m-iinv-old-pos
                            (a (g (scar s) x)))
                 (:instance m-iinv-pos-3
                            (a (g (scar s) x)))
                 (:instance m-iinv-pos-n3
                            (a (g (scar s) x)))))))

(defthm suff13
  (implies (bake-impl-iinv x)
           (< (max-pos* (bake-impl-map* x (keys)) (keys))
              (+ 1 (curr-sh-max x))))
  :rule-classes (:rewrite :linear))

(defthm suff14
  (implies (and (bake-impl-iinv x)
                (in k (keys))
                (in l (keys))
                (>= (g :loc (g k x)) 3)
                (< (g :loc (g l x)) 3))
           (<= (g :pos (g l x)) (g :pos (g k x))))
  :hints (("Goal" :cases ((equal k l))))
  :rule-classes (:rewrite :linear))

(defthm suff15
  (implies (and (bake-impl-iinv x)
                (in k (keys))
                (in l (keys))
                (equal (g :loc (g l x)) 7)
                (equal (g :loc (g k x)) 6)
                (<= (g :pos (g k x)) (g :pos (g l x))))
           (< (ndx* (g :key (g l x)) (keys))
              (ndx* (g :key (g k x)) (keys))))
  :rule-classes (:linear :rewrite)
  :hints (("Goal"
           :cases ((equal k l))
           :in-theory (disable x-iinv-prop2-2
                               x-iinv-prop2-1)
           :use ((:instance x-iinv-prop2-2
                            (a (g k x))
                            (b (g l x)))
                 (:instance x-iinv-prop2-1
                            (a (g k x))
                            (b (g l x)))))))

(defthm suff16
  (implies (and (bake-impl-iinv x)
                (in k (keys))
                (in l (keys))
                (equal (g :loc (g l x)) 7)
                (equal (g :loc (g k x)) 6)
                (<= (g :pos (g k x)) (g :pos (g l x))))
           (equal (g :pos (g k x)) (g :pos (g l x))))
  :hints (("Goal"
           :cases ((equal k l))
           :in-theory (disable x-iinv-prop2-2
                               x-iinv-prop2-1)
           :use ((:instance x-iinv-prop2-2
                            (a (g k x))
                            (b (g l x)))
                 (:instance x-iinv-prop2-1
                            (a (g k x))
                            (b (g l x)))))))

(defthm suff17
  (implies (and (bake-impl-iinv x)
                (in k (keys))
                (in l (keys))
                (equal (g :loc (g l x)) 7)
                (equal (g :loc (g k x)) 6))
           (<= (g :pos (g l x)) (g :pos (g k x))))
  :rule-classes (:linear :rewrite)
  :hints (("Goal"
           :cases ((equal k l))
           :in-theory (disable suff16 x-iinv-prop2-2)
           :use ((:instance x-iinv-prop2-2
                            (a (g k x))
                            (b (g l x)))))))

;; ok, now we reenable the step, blok, and init functions:
(in-theory (enable bake-impl-t-next 
                   bake-impl-t-blok
                   bake-impl-t-init))

(in-theory (disable bake-impl-iinv))

;;;; definitions ensuring valid runs:

(defun bake-impl-t-nlock (k x)
  (let ((a (g k x)))
    (make-ord 2 (if (g :choosing a) 1 2)
    (make-ord 1 (1+ (nfix (g :pos a)))
                (ndx (g :key a))))))

(defun bake-impl-t-noblk (a b)
  (or (and (!= (g :loc a) 5)
           (!= (g :loc a) 6))
      (and (not (g :choosing b))
           (> (g :pos b) (g :pos a)))))

(defun pos-fix (x) (if (posp x) x 1))

(defun bake-impl-t-nstrv (a b)
  (pos-fix
   (cond ((or (and (=  (g :loc b) 2)
                   (<  (g :temp b) (g :pos a)))
              (and (>  (g :loc b) 2)
                   (<= (g :pos b) (g :pos a))))
          (+ 8 (- 8 (g :loc b))))
         ((>= (g :loc b) 5) 
          (+ 5 (- 8 (g :loc b))))
         (t
          (+ 0 (- 5 (g :loc b)))))))

(defun bake-impl-nst-bnd () 0)

(def-valid-tr-system bake-impl)

;;;; definitions ensuring correct mapping: (repeated from before)

(defun bake-impl-t-map (a)
  (upd nil
       :loc  (case (g :loc a)
                   ((0 1) 'idle)
                   ((2 3) 'loaded)
                   ((4 5 6) 'interested)
                   (t 'go))
       :pos  (case (g :loc a)
                   (3 (g :old-pos a))
                   (t (g :pos a)))
       :load (case (g :loc a)
                   (2 (1+ (g :temp a)))
                   (t (g :pos a)))))

(defun bake-impl-t-rank (a)
  (case (g :loc a)
        (0 1)       (1 0)
        (2 1)       (3 0)
        (4 2) (5 1) (6 0)
        (t 0)))

(def-match-tr-systems bake-impl bake-spec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(prove-tr-refinement bake-impl bake-spec)

