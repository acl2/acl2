; Copyright (C) 2017, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(local (include-book "arithmetic/top-with-meta" :dir :system))
(include-book "general-theory")
;; We use the records/maps throughout for IMPL and SPEC state definition:
(include-book "misc/records" :dir :system)

;; for the transaction-based systems, we will also now have a finite set of
;; keys and we will need several definitions and properties about sets to work
;; on these keys:
(include-book "sets")

;; we also will need a book defining operations and logic on "bounded ordinals"
(include-book "bounded-ords")

#|

Our goal now is to simply assume the properties of tr-based system definitions
and show they apply for the more general system.. in particular, similar to the
previous section.. we will define an encapsulate which will include the
following assumptions:

(def-valid-keys) ;; defines (keys) as a finite set of keys and key-p membership test..
(def-tr-system-defs   tr-impl)
(def-tr-system-defs   tr-spec t)
(def-tr-system-props  tr-impl)
(def-valid-tr-systems tr-impl)
(def-match-tr-systems tr-impl tr-spec)

The def-tr-system-defs will introduce definitions for the system-level
definitions for tr-impl and tr-spec based on the assumed transaction-level
defintions. We will prove that the system-level properties hold for the derived
system-level functions based on the transaction-level properties for tr-impl
and tr-spec:

(def-system-props  tr-impl key-p)
(def-valid-system  tr-impl key-p)
(def-match-systems tr-impl tr-spec key-p)

|#

;; needed this rule, probably should add it to sets book:
(defthm non-empty-card>0
  (implies x (> (card x) 0))
  :hints (("Goal" :use (:instance card-of-empty-set)))
  :rule-classes :linear)

(defun ==-but (x y k s)
  (declare (xargs :measure (card s)))
  (or (null s)
      (and (or (equal k (scar s))
               (equal (g (scar s) x)
                      (g (scar s) y)))
           (==-but x y k (scdr s)))))

(defmacro def-valid-keys ()
  `(progn (local (defun key-p (k)   (in k (keys))))
          (defthm key-p-open        (equal (key-p k) (in k (keys))))
          (defthm t-is-a-key        (key-p t))
          (defthm keys-is-not-empty (iff (keys) t)
            :rule-classes (:type-prescription :rewrite))
          (defthm nil-is-not-a-key  (not (key-p nil))
            :rule-classes (:type-prescription :rewrite))))

(defmacro def-tr-system-defs (name)
  (declare (xargs :guard (symbolp name)))
  (let ((t-next  (snap name '-t-next))
        (t-blok  (snap name '-t-blok))
        (t-init  (snap name '-t-init)))
    (let ((next     (snap name '-next))
          (init*    (snap name '-init*))
          (init     (snap name '-init))
          (blok*    (snap name '-blok*))
          (blok     (snap name '-blok))
          (blocker* (snap name '-blocker*))
          (blocker  (snap name '-blocker)))
      (let ((blok*-prop1   (snap name '-blok*-prop1))
            (blok*-prop2   (snap name '-blok*-prop2))
            (impl-blok     (snap name '-impl-blok))
            (blok-impl     (snap name '-blok-impl))
            (blocker*-open (snap name '-blocker*-open))
            (blocker*-key  (snap name '-blocker*-key))
            (blocker-key   (snap name '-blocker-key)))
        `(progn
           (defun ,next (x y k)
             (and (==-but x y k (keys))
                  (,t-next (g k x) (g k y) k x)))
           (defun ,init* (x s)
             (declare (xargs :measure (card s)))
             (or (null s)
                 (and (,t-init (g (scar s) x) (scar s))
                      (,init* x (scdr s)))))
           (defun ,init (x) (,init* x (keys)))
           (defun ,blok* (x k s)
             (declare (xargs :measure (card s)))
             (and s
                  (or (,t-blok (g k x) (g (scar s) x))
                      (,blok* x k (scdr s)))))
           (local (defthm ,blok*-prop1
                    (implies (and (in l s)
                                  (,t-blok (g k x) (g l x)))
                             (,blok* x k s))))
           (defun ,blok (x k) (,blok* x k (keys)))
           (defun ,blocker* (k x s)
             (declare (xargs :measure (card s)))
             (cond ((null s) (scar (keys)))
                   ((,t-blok (g k x) (g (scar s) x))
                    (scar s))
                   ((c1 s) (scar s))
                   (t (,blocker* k x (scdr s)))))
           (defun ,blocker (k x) (,blocker* k x (keys)))
           (local (defthm ,blok*-prop2
                    (implies (,blok* x k s)
                             (,t-blok (g k x)
                                      (g (,blocker* k x s) x)))
                    :hints (("Goal" :in-theory (disable ,t-blok)))))
           (defthm ,impl-blok
             (implies (and (key-p k)
                           (key-p l)
                           (,t-blok (g k x) (g l x)))
                      (,blok x k)))
           (defthm ,blok-impl
             (implies (,blok x k)
                      (,t-blok (g k x)
                               (g (,blocker k x) x)))
             :hints (("Goal" :in-theory (disable ,t-blok))))
           (local (defthm ,blocker*-open
                    (implies (c1 s)
                             (equal (,blocker* k x s)
                                    (scar s)))))
           (local (defun yuck-3 (k x s)
                    (declare (xargs :measure (card s)))
                    (if (null s) (+ k x)
                      (1+ (yuck-3 k x (scdr s))))))
           (local (defthm ,blocker*-key
                    (implies s
                             (in (,blocker* k x s) s))
                    :hints (("Goal" :induct (yuck-3 k x s)))))
           (defthm ,blocker-key
             (key-p (,blocker k x))))))))

(defmacro def-tr-mapping-defs (name)
  (declare (xargs :guard (symbolp name)))
  (let ((t-map   (snap name '-t-map)))
    (let ((map*        (snap name '-map*))
          (map         (snap name '-map)))
      `(progn
         (defun ,map* (x s)
           (declare (xargs :measure (card s)))
           (if (null s) ()
             (let ((k (scar s)))
               (s k (,t-map (g k x)) (,map* x (scdr s))))))
         (defun ,map (x) (,map* x (keys)))
         (local (defthm map*-open
                  (implies (c1 s)
                           (equal (,map* x s)
                                  (s (scar s) (,t-map (g (scar s) x)) ())))))))))

(defmacro def-tr-mapping-props (name)
  (declare (xargs :guard (symbolp name)))
  (let ((t-map   (snap name '-t-map)))
    (let ((map*        (snap name '-map*))
          (map         (snap name '-map)))
      (let ((map*-redux  (snap name '-map*-redux))
            (map-redux   (snap name '-map-redux)))
        `(progn
           (local (defthm ,map*-redux
                    (implies (and (in k s)
                                  (subset s (keys)))
                             (equal (g k (,map* x s))
                                    (,t-map (g k x))))
                    :hints (("Subgoal *1/4" :cases ((equal k (scar s))))
                            ("Subgoal *1/3" :in-theory (disable subset-is-transitive)
                             :use ((:instance subset-is-transitive
                                              (x (sdiff s (s1 (scar s))))
                                              (y s)
                                              (z (keys))))))))
           (defthm ,map-redux
             (implies (key-p k)
                      (equal (g k (,map x))
                             (,t-map (g k x))))))))))

(defmacro def-tr-system-props (name)
  (declare (xargs :guard (symbolp name)))
  (let ((t-next  (snap name '-t-next))
        (init    (snap name '-init))
        (next    (snap name '-next))
        (blok    (snap name '-blok))
        (iinv    (snap name '-iinv)))
    (let ((t-next-must-change (snap name '-t-next-must-change))
          (s-iinv-init-thm    (snap name '-s-iinv-init))
          (s-iinv-next-thm    (snap name '-s-iinv-next)))
      `(progn
         (defthm ,t-next-must-change
           (equal (,t-next a a k x) nil))
         (defthm ,s-iinv-init-thm
           (implies (,init x) (,iinv x)))
         (defthm ,s-iinv-next-thm
           (implies (and (,iinv x)
                         (key-p k)
                         (not (,blok x k))
                         (,next x y k))
                    (,iinv y))
           :rule-classes nil)))));; free variables x and k
                        
(defmacro def-match-tr-systems (impl spec)
  (declare (xargs :guard (and (symbolp impl) (symbolp spec))))
  (let ((i-t-next (snap impl '-t-next))
        (i-t-blok (snap impl '-t-blok))
        (i-t-init (snap impl '-t-init))
        (i-t-map  (snap impl '-t-map))
        (i-t-rank (snap impl '-t-rank))
        (s-t-init (snap spec '-t-init))
        (s-t-next (snap spec '-t-next))
        (s-t-blok (snap spec '-t-blok))
        (i-iinv   (snap impl '-iinv))
        (i-map    (snap impl '-map)))
    (let ((t-map-init-to-init   (snap impl '-t-map-init-to-init))
          (t-rank-is-ord        (snap impl '-t-rank-is-ord))
          (t-map-match-next     (snap impl '-t-map-match-next))
          (t-map-match-blok     (snap impl '-t-map-match-blok))
          (t-map-finite-stutter (snap impl '-t-map-finite-stutter)))
      `(progn
         (defthm ,t-map-init-to-init
           (implies (and (key-p k) (,i-t-init a k)) (,s-t-init (,i-t-map a) k)))
         (defthm ,t-rank-is-ord
           (o-p (,i-t-rank a)))
         (defthm ,t-map-match-next
           (implies (and (,i-iinv x)
                         (key-p k)
                         (,i-t-next (g k x) b k x)
                         (not (equal (,i-t-map (g k x)) (,i-t-map b))))
                    (,s-t-next (,i-t-map (g k x)) (,i-t-map b) k (,i-map x))))
         (defthm ,t-map-match-blok
           (implies (and (,i-iinv x)
                         (key-p k)
                         (key-p l)
                         (,i-t-next (g k x) b k x)
                         (not (,i-t-blok (g k x) (g l x)))
                         (not (equal (,i-t-map (g k x)) (,i-t-map b))))
                    (not (,s-t-blok (,i-t-map (g k x)) (,i-t-map (g l x))))))
         (defthm ,t-map-finite-stutter
           (implies (and (,i-iinv x)
                         (key-p k)
                         (,i-t-next (g k x) b k x)
                         (equal (,i-t-map (g k x)) (,i-t-map b)))
                    (o< (,i-t-rank b) (,i-t-rank (g k x)))))))))

(defmacro def-valid-tr-system (name)
  (declare (xargs :guard (symbolp name)))
  (let ((t-next    (snap name '-t-next))
        (t-blok    (snap name '-t-blok))
        (iinv      (snap name '-iinv))
        (t-nlock   (snap name '-t-nlock))
        (t-noblk   (snap name '-t-noblk))
        (nst-bnd   (snap name '-nst-bnd))
        (t-nstrv   (snap name '-t-nstrv)))
    (let ((t-nlock-is-ord     (snap name '-t-nlock-is-ord))
          (t-nst-bnd-is-natp  (snap name '-t-nst-bnd-is-natp))
          (t-nlock-decreases  (snap name '-t-nlock-decreases))
          (t-nstrv-is-bplp    (snap name '-t-nstrv-is-bplp))
          (t-noblk-blk-thm    (snap name '-t-noblk-blk-thm))
          (t-noblk-inv-thm    (snap name '-t-noblk-inv-thm))
          (t-nstrv-decreases  (snap name '-t-nstrv-decreases)))
      `(progn
         (defthm ,t-nlock-is-ord
           (o-p (,t-nlock k x)))
         (defthm ,t-nlock-decreases
           (implies (and (,iinv x)
                         (key-p k)
                         (key-p l)
                         (,t-blok (g k x) (g l x)))
                    (o< (,t-nlock l x)
                        (,t-nlock k x))))
         (defthm ,t-noblk-blk-thm
           (implies (and (,iinv x)
                         (key-p k)
                         (key-p l)
                         (,t-noblk (g k x) (g l x)))
                    (not (,t-blok (g k x) (g l x)))))
         (defthm ,t-noblk-inv-thm
           (implies (and (,iinv x)
                         (key-p k)
                         (key-p l)
                         (,t-noblk (g k x) (g l x))
                         (,t-next (g l x) c l x))
                    (,t-noblk (g k x) c)))
         (defthm ,t-nst-bnd-is-natp
           (natp (,nst-bnd))
           :rule-classes (:rewrite :type-prescription))
         (defthm ,t-nstrv-is-bplp
           (bplp (,t-nstrv a b) (,nst-bnd))
           :rule-classes (:rewrite :type-prescription))
         (defthm ,t-nstrv-decreases
           (implies (and (,iinv x)
                         (key-p k)
                         (key-p l)
                         (not (,t-noblk (g k x) (g l x)))
                         (not (,t-noblk (g k x) c))
                         (,t-next (g l x) c l x))
                    (bnl< (,t-nstrv (g k x) c)
                          (,t-nstrv (g k x) (g l x))
                          (,nst-bnd))))))))

(defmacro prove-tr-refinement (tr-impl tr-spec)
  (declare (xargs :guard (and (symbolp tr-impl) (symbolp tr-spec))))
  `(progn (def-tr-system-defs   ,tr-impl) ;; define next and blok for system..
          (def-tr-system-defs   ,tr-spec)
          (def-tr-mapping-defs  ,tr-impl) ;; also need iinv and map defined..
          (def-tr-system-props  ,tr-impl)
          (def-valid-tr-system  ,tr-impl)
          (def-match-tr-systems ,tr-impl ,tr-spec)))

(ec-sets t)  ;; turn on executable counterparts for set operations for processing encapsulate..

(encapsulate
 (;; TR-IMPL/TR-SPEC shared definition
  (keys ()                   t) ;; a finite set of unqiue "keys" which will define selection
  (key-p (k)                 t) ;; a predicate detecting a key..
  ;; TR-IMPL definition --
  (tr-impl-t-init (a k)      t) ;; initial state predicate for tr-state a
  (tr-impl-t-next (a b k x)  t) ;; tr-state a transitions to tr-state b in impl state x
  (tr-impl-t-blok (a b)      t) ;; tr-state a is blocked from stepping by tr-state b
  ;; TR-SPEC definition --
  (tr-spec-t-init (a k)      t) ;; initial state predicate for tr-state a
  (tr-spec-t-next (a b k x)  t) ;; tr-state a transitions to tr-state b in impl state x
  (tr-spec-t-blok (a b)      t) ;; tr-state a is blocked from stepping by tr-state b
  ;; TR-IMPL to TR-SPEC refinement -- 
  (tr-impl-t-map  (a)        t) ;; maps impl states to corresponding spec states
  (tr-impl-t-rank (a)        t) ;; ordinal decreases until spec matches transition for k
  ;; TR-IMPL state properties --
  (tr-impl-iinv (x)          t) ;; system-level inductive invariant for impl states
  (tr-impl-t-noblk (a b)     t) ;; is tr-state invariably unblocked by tr-state b
  (tr-impl-t-nstrv (a b)     t) ;; nat list decreases on b transitions until noblk on a
  (tr-impl-t-nlock (k x)     t) ;; ordinal decreases on blok's ensuring some tr can go
  (tr-impl-nst-bnd ()        t) ;; bound on the length of the nstrv nat list
  )

 ;; Local witness functions for the exported signatures:
 ;; TR-IMPL/TR-SPEC shared definition
 (local (defun keys            ()        (s1 t)))
 ;; TR-IMPL definition --

 (local (defun tr-impl-t-init  (a k)     (declare (ignore k))   (not a)))
 (local (defun tr-impl-t-next  (a b k x) (declare (ignore k x)) (equal (not a) b)))
 (local (defun tr-impl-t-blok  (a b)     (declare (ignore a b)) nil))
 ;; TR-SPEC definition --
 (local (defun tr-spec-t-init  (a k)     (declare (ignore k))   (not a)))
 (local (defun tr-spec-t-next  (a b k x) (declare (ignore k x)) (equal (not a) b)))
 (local (defun tr-spec-t-blok  (a b)     (declare (ignore a b)) nil))
 ;; TR-IMPL to TR-SPEC refinement -- 
 (local (defun tr-impl-t-map   (a)       a))
 (local (defun tr-impl-t-rank  (a)       (declare (ignore a)) 0))
 ;; TR-IMPL state properties --
 (local (defun tr-impl-iinv    (x)       (declare (ignore x)) t))
 (local (defun tr-impl-t-noblk (a b)     (declare (ignore a b)) t))
 (local (defun tr-impl-t-nstrv (a b)     (declare (ignore a b)) 1))
 (local (defun tr-impl-t-nlock (k x)     (declare (ignore k x)) 0))
 (local (defun tr-impl-nst-bnd ()                               0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; P0::: IMPORTANT NOTE:
;;  As we mentioned before, exported properties from this encapsulation are the following macros which
;;  expand as we presented before and represent the assumptions we make moving forward:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 (def-valid-keys) ;; ensures (keys) is a finite set of keys with key-p membership test..
 (prove-tr-refinement tr-impl tr-spec)
)

(ec-sets nil) ;; turn off executable counterparts for set operations for rest of book

(in-theory (disable tr-impl-blocker tr-impl-blocker*))
(in-theory (disable tr-spec-blocker tr-spec-blocker*))

(def-tr-mapping-props tr-impl)

;; we now define the following functions for impl needed to prove the
;; properties on impl (relative to spec) that we need.
;;
;; tr-impl-noblk
;; tr-impl-nstrv
;; tr-impl-starver
;; tr-impl-rank

(defun ti-noblk* (k x s)
  (declare (xargs :measure (card s)))
  (or (null s)
      (and (tr-impl-t-noblk (g k x) (g (scar s) x))
           (ti-noblk* k x (scdr s)))))

(defun tr-impl-noblk (k x) (ti-noblk* k x (keys)))

(defun pikblk* (s k x)
  (declare (xargs :measure (card s)))
  (cond ((null s) nil)
        ((tr-impl-t-blok (g k x) (g (scar s) x))
         (scar s))
        (t (pikblk* (scdr s) k x))))

(defun pikblk (k x) (pikblk* (keys) k x))

(defthm blok-implies-pikblk*
  (implies (tr-impl-blok* x k s)
           (tr-impl-t-blok (g k x) (g (pikblk* s k x) x))))

(defthm subset-scdr-transfer
  (implies (subset x y) (subset (scdr x) y))
  :hints (("Goal" :in-theory (disable subset-is-transitive)
           :use ((:instance subset-is-transitive
                            (x (scdr x))
                            (y x)
                            (z y))))))

(defthm subset-and-s-implies-scar
  (implies (and s (subset s x))
           (in (scar s) x))
  :hints (("Goal" :in-theory (disable in-subset-transits)
           :use ((:instance in-subset-transits
                            (e (scar s))
                            (x s)
                            (y x))))))

(defthm pikblk*-in-keys
  (implies (tr-impl-blok* x k s)
           (in (pikblk* s k x) s)))

(defun tr-impl-starver (k x)
  (declare (xargs :measure (tr-impl-t-nlock k x)))
  (if (and (tr-impl-iinv x) (key-p k) (tr-impl-blok x k))
      (tr-impl-starver (pikblk k x) x)
    k))

(defmacro nstb () `(tr-impl-nst-bnd))

(defun sum-nsts* (k x s)
  (declare (xargs :measure (card s)))
  (if (null s) (bnl1 (nstb))
    (bnl+ (if (tr-impl-t-noblk (g k x) (g (scar s) x))
              (bnl0 (nstb))
            (tr-impl-t-nstrv (g k x) (g (scar s) x)))
          (sum-nsts* k x (scdr s))
          (nstb))))

(defun sum-nsts (k x) (sum-nsts* k x (keys)))

(defun nstrvs* (k x)
  (declare (xargs :measure (tr-impl-t-nlock k x)))
  (if (and (tr-impl-iinv x) (key-p k) (tr-impl-blok x k))
      (cons (sum-nsts k x) (nstrvs* (pikblk k x) x))
    (list (sum-nsts k x))))

(defun tr-impl-nstrv (k x)
  (bnll->o (card (keys)) (nstrvs* k x) (nstb)))

(defun tr-impl-rank (k x) 
  (tr-impl-t-rank (g k x)))

;; system props proof attempts:

(DEFTHM TR-IMPL-IINV-NEXT
  (IMPLIES (AND (TR-IMPL-IINV X)
                (KEY-P K)
                (NOT (TR-IMPL-BLOK X K))
                (TR-IMPL-NEXT X Y K))
           (TR-IMPL-IINV Y))
  :hints (("Goal" :in-theory (disable tr-impl-next)
           :use ((:instance tr-impl-s-iinv-next)))))

;; system matching proof attempts:

(local
 (defthm subset-scdr-property
   (implies (subset x y)
            (subset (scdr x) y))
   :hints (("Goal" :in-theory (disable subset-is-transitive)
            :use ((:instance subset-is-transitive
                             (x (scdr x))
                             (y x)
                             (z y)))))))

(local
 (defthm scar-subset-in-transfer
   (implies (and s
                 (subset s x))
            (in (scar s) x))
   :hints (("Goal" :in-theory (disable in-subset-transits)
            :use ((:instance in-subset-transits
                             (x s)
                             (y x)
                             (e (scar s))))))))

(local 
 (defthm ==-but-transfer
   (implies (and (subset s (keys))
                 (==-but x y k s))
            (==-but (tr-impl-map x)
                    (tr-impl-map y)
                    k s))))


(defthm ==-but-g-k
  (implies (and (in k s)
                (not (equal k l))
                (==-but x y l s))
           (equal (g k y) (g k x))))

(local
 (defthm key-p-bactrack
   (implies (key-p x)
            (in x (keys)))))

(local
 (defthm impl-map-tr-next-back-help
   (IMPLIES (AND (IN K (KEYS))
                 (==-BUT X Y K (KEYS))
                 (SUBSET S (KEYS))
                 (EQUAL (TR-IMPL-T-MAP (G K X))
                        (TR-IMPL-T-MAP (G K Y))))
            (EQUAL (TR-IMPL-MAP* X S)
                   (TR-IMPL-MAP* Y S)))   
   :hints (("Subgoal *1/3" :in-theory (disable ==-but-g-k)
            :use ((:instance ==-but-g-k
                             (k (scar s))
                             (s (keys))
                             (l k)))))))

(local
 (defthm impl-map-tr-next-back
   (implies (and (key-p k)
                 (==-but x y k (keys))
                 (not (equal (tr-impl-map x)
                             (tr-impl-map y))))
            (not (equal (tr-impl-t-map (g k x))
                        (tr-impl-t-map (g k y)))))
   :hints (("Goal" :in-theory (disable tr-impl-map-redux
                                       ==-but-g-k)
            :use ((:instance tr-impl-map-redux)
                  (:instance tr-impl-map-redux (x y)))))))

(DEFTHM TR-IMPL-MAP-MATCH-NEXT-1
  (IMPLIES (AND (TR-IMPL-IINV X)
                (KEY-P K)
                (TR-IMPL-NEXT X Y K)
                (NOT (TR-IMPL-BLOK X K))
                (NOT (EQUAL (TR-IMPL-MAP X)
                            (TR-IMPL-MAP Y))))
           (TR-SPEC-NEXT (TR-IMPL-MAP X)
                         (TR-IMPL-MAP Y)
                         K))
  :hints (("Goal" :in-theory (disable tr-impl-map))))

(DEFTHM TR-IMPL-MAP-MATCH-NEXT-2
  (IMPLIES (AND (TR-IMPL-IINV X)
                (KEY-P K)
                (TR-IMPL-NEXT X Y K)
                (NOT (TR-IMPL-BLOK X K))
                (NOT (EQUAL (TR-IMPL-MAP X)
                            (TR-IMPL-MAP Y))))
           (NOT (TR-SPEC-BLOK (TR-IMPL-MAP X) K)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable tr-impl-map
                                      impl-map-tr-next-back
                                      tr-impl-t-map-match-blok
                                      tr-spec-impl-blok
                                      tr-impl-impl-blok
                                      tr-spec-blok-impl)
           :use ((:instance impl-map-tr-next-back)
                 (:instance tr-spec-blok-impl
                            (x (tr-impl-map x)))
                 (:instance tr-impl-impl-blok
                            (l (tr-spec-blocker k (tr-impl-map x))))
                 (:instance tr-spec-impl-blok
                            (l (tr-spec-blocker k (tr-impl-map x)))
                            (x (tr-impl-map x)))
                 (:instance tr-impl-t-map-match-blok
                            (b (g k y))
                            (x x)
                            (l (tr-spec-blocker k (tr-impl-map x))))))))

(DEFTHM TR-IMPL-MAP-MATCH-NEXT
  (IMPLIES (AND (TR-IMPL-IINV X)
                (KEY-P K)
                (TR-IMPL-NEXT X Y K)
                (NOT (TR-IMPL-BLOK X K))
                (NOT (EQUAL (TR-IMPL-MAP X)
                            (TR-IMPL-MAP Y))))
           (AND (TR-SPEC-NEXT (TR-IMPL-MAP X)
                              (TR-IMPL-MAP Y)
                              K)
                (NOT (TR-SPEC-BLOK (TR-IMPL-MAP X) K))))
  :hints (("Goal" :in-theory (disable tr-impl-map)
           :use (:instance TR-IMPL-MAP-MATCH-NEXT-2))))

(DEFTHM TR-IMPL-MAP-FINITE-STUTTER
  (IMPLIES (AND (TR-IMPL-IINV X)
                (KEY-P K)
                (TR-IMPL-NEXT X Y K)
                (NOT (TR-IMPL-BLOK X K))
                (EQUAL (TR-IMPL-MAP X) (TR-IMPL-MAP Y)))
           (O< (TR-IMPL-RANK K Y)
               (TR-IMPL-RANK K X)))
  :hints (("Goal" :in-theory (disable tr-impl-map-redux
                                      tr-impl-t-map-finite-stutter)
           :use ((:instance tr-impl-map-redux)
                 (:instance tr-impl-map-redux (x y))
                 (:instance tr-impl-t-map-finite-stutter
                            (b (g k y)))))))

;; system validation proof work (a lot of it...):

(local
(defthm ti-noblk*-covers
  (implies (and (in l s)
                (ti-noblk* k x s))
           (tr-impl-t-noblk (g k x) (g l x)))))

(DEFTHM TR-IMPL-NOBLK-BLK-THM
  (IMPLIES (AND (TR-IMPL-IINV X)
                (KEY-P K)
                (TR-IMPL-NOBLK K X))
           (NOT (TR-IMPL-BLOK X K)))
  :hints (("Goal" :in-theory (disable tr-impl-blok-impl
                                      tr-impl-t-noblk-blk-thm
                                      ti-noblk*-covers)
           :use ((:instance tr-impl-blok-impl)
                 (:instance ti-noblk*-covers
                            (l (tr-impl-blocker k x))
                            (s (keys)))
                 (:instance tr-impl-t-noblk-blk-thm
                            (l (tr-impl-blocker k x)))))))

(defun simple-set-ind (s)
  (declare (xargs :measure (card s)))
  (cond ((not s) 0)
        (t (1+ (simple-set-ind (scdr s))))))

(defthm ==-but-expand-1
  (implies (and s
                (==-but x y k s))
           (==-but x y k (scdr s))))

(defthm noblk-inv-help
  (IMPLIES (AND (TR-IMPL-IINV X)
                (NOT (EQUAL K L))
                (KEY-P K)
                (KEY-P L)
                (TR-IMPL-NEXT X Y L)
                (SUBSET S (KEYS))
                (TI-NOBLK* K X S))
           (TI-NOBLK* K Y S))  
  :hints (("Goal" :induct (simple-set-ind s))
          ("Subgoal *1/2"
           :cases ((equal k (scar s))
                   (equal l (scar s)))
           :in-theory (disable ==-but-g-k)
           :use ((:instance ==-but-g-k
                            (s (keys))
                            (k (scar s)))
                 (:instance ==-but-g-k
                            (s (keys)))
                 (:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y))))))
  :rule-classes nil)

(DEFTHM TR-IMPL-NOBLK-INV-THM
  (IMPLIES (AND (TR-IMPL-IINV X)
                (KEY-P K)
                (KEY-P L)
                (NOT (EQUAL K L))
                (TR-IMPL-NOBLK K X)
                (TR-IMPL-NEXT X Y L)
                (NOT (TR-IMPL-BLOK X L)))
           (TR-IMPL-NOBLK K Y))
  :hints (("Goal" :use (:instance noblk-inv-help
                                  (s (keys))))))

(defthm sum-nsts-bplp
  (bplp (sum-nsts* k x s) (nstb)))

(defthm nstrvs*-bpllp
  (bpllp (nstrvs* k x) (nstb)))

(DEFTHM TR-IMPL-NSTRV-IS-ORD
  (O-P (TR-IMPL-NSTRV K X)))

(DEFTHM TR-IMPL-STARVER-IS-ID
  (IMPLIES (KEY-P K)
           (KEY-P (TR-IMPL-STARVER K X))))

(defthm ti-noblk*-impl-not-tr-impl-blok*
  (implies (and (subset s (keys))
                (tr-impl-iinv x)
                (key-p k)
                (ti-noblk* k x s))
           (not (tr-impl-blok* x k s))))

(DEFTHM TR-IMPL-STARVER-THM
  (IMPLIES (AND (KEY-P K)
                (TR-IMPL-IINV X)
                (NOT (TR-IMPL-NOBLK K X)))
           (NOT (TR-IMPL-BLOK X (TR-IMPL-STARVER K X)))))

(defthm bnl<-nil
  (implies (bplp l b)
           (not (bnl< l nil b)))
  :hints (("Goal" :induct (bnl< l nil b))))

(defthm bnll<=-nstrvs*-redux
  (implies (syntaxp (and (consp a) (equal (car a) 'cons)))
           (equal (bnll<= (nstrvs* k x) a (nstb))
                  (or (bnl< (sum-nsts k x) (car a) (nstb))
                      (and (equal (sum-nsts k x) (car a))
                           (bnll<= (cdr (nstrvs* k x)) (cdr a) (nstb)))))))

(defthm bnll<-nstrvs*-redux
  (implies (syntaxp (and (consp a) (equal (car a) 'cons)))
           (equal (bnll< (nstrvs* k x) a (nstb))
                  (or (bnl< (sum-nsts k x) (car a) (nstb))
                      (and (equal (sum-nsts k x) (car a))
                           (bnll< (cdr (nstrvs* k x)) (cdr a) (nstb)))))))

;; ASIDE on proving (len (nstrvs* k x)) < (card (keys))
;;
;; we need to prove that the (len (nstrvs* k x)) < (card (keys))
;; this holds because each (pikblk k x) (for blocked k in x) must
;; not be equal to k and further not equal to any previous k in
;; sequence of pikblks.. this is because we have a measure (nlock)
;; which strictly decreases for any sequence of bloking k, but
;; to prove this, we need to build this set and introduce a notion
;; of o<-nlock with a whole set to show that each time we add a
;; new element that we could not have an element previously in the
;; set.. then we compare the cardinality and we are done.. ez pz.

(defun nst-set (k x)
  (declare (xargs :measure (tr-impl-t-nlock k x)))
  (if (and (tr-impl-iinv x) (key-p k) (tr-impl-blok x k))
      (sadd (pikblk k x) (nst-set (pikblk k x) x))
    ()))

(defun o<-nlock-set (k x s)
  (declare (xargs :measure (card s)))
  (or (null s)
      (and (o< (tr-impl-t-nlock (scar s) x)
               (tr-impl-t-nlock k x))
           (o<-nlock-set k x (scdr s)))))

(defun induct-unite (r s)
  (declare (xargs :measure (+ (card r) (card s))))
  (cond ((or (null r) (null s)) nil)
        ((equal (scar r) (scar s))
         (induct-unite (scdr r) (scdr s)))
        ((<< (scar r) (scar s))
         (induct-unite (scdr r) s))
        (t (induct-unite r (scdr s)))))

(defthm o<-nlock-set-unite
  (implies (and (o<-nlock-set k x r)
                (o<-nlock-set k x s))
           (o<-nlock-set k x (unite r s)))
  :hints (("Goal" :induct (induct-unite r s))
          ("Subgoal *1/4"
           :in-theory (disable scar-is-least-member)
           :expand (o<-nlock-set k x (unite r s))
           :use ((:instance scar-is-least-member
                            (e (scar s))
                            (x r))))
          ("Subgoal *1/3"
           :in-theory (disable scar-is-least-member)
           :expand (o<-nlock-set k x (unite r s))
           :use ((:instance scar-is-least-member
                            (e (scar r))
                            (x s))))))

(in-theory (enable o<))

(defthm o<-irreflexive
  (not (o< a a)))

(defthm o<-totality
  (implies (o< a b)
           (and (not (o< b a))
                (not (equal a b))))
  :rule-classes :forward-chaining)

(defthm o-infp-o-finp-not-o<
  (implies (and (o-infp a)
		(o-finp b))
	   (not (o< a b)))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(defthm o<-transits
  (implies (and (o< x y) (o< y z))
           (o< x z))
  :rule-classes nil)

(in-theory (disable o<))

(defthm o<-nlock-set-transfer
  (implies (and (o<-nlock-set l x s)
                (o< (tr-impl-t-nlock l x)
                    (tr-impl-t-nlock k x)))
           (o<-nlock-set k x s))
  :rule-classes nil
  :hints (("Subgoal *1/4" :use ((:instance o<-transits
                                           (x (tr-impl-t-nlock (scar s) x))
                                           (y (tr-impl-t-nlock l x))
                                           (z (tr-impl-t-nlock k x)))))))

(defthm o<-nlock-set-nst-set
  (implies (and (tr-impl-iinv x)
                (key-p k))
           (o<-nlock-set k x (nst-set k x)))
  :hints (("Subgoal *1/2" :use ((:instance o<-nlock-set-transfer
                                           (s (nst-set (pikblk k x) x))
                                           (l (pikblk k x)))))))

(defthm nst-set-subset-keys
  (implies (and (tr-impl-iinv x)
                (key-p k))
           (subset (nst-set k x) (keys))))

(defthm o<-nlock-set-not-in
  (implies (and (tr-impl-iinv x)
                (key-p k)
                (o<-nlock-set k x s))
           (not (in k s))))

(defthm not-in-nst-set
  (implies (and (tr-impl-iinv x)
                (key-p k))
           (not (in k (nst-set k x)))))

(defthm card-nil
  (equal (card nil) 0)
  :hints (("Goal" :use ((:instance card-of-empty-set
                                   (x nil))))))

(defun nst-set+ (k x) (sadd k (nst-set k x)))

(defthm nst-set-card-len-nstrvs*
  (implies (and (tr-impl-iinv x)
                (key-p k))
           (equal (len (nstrvs* k x))
                  (card (nst-set+ k x)))))

(defthm nst-set+-subset-keys
  (implies (and (tr-impl-iinv x)
                (key-p k))
           (subset (nst-set+ k x) (keys))))

(in-theory (disable nst-set+))

(defthm len-nstrvs*-<=
  (implies (and (tr-impl-iinv x)
                (key-p k))
           (<= (len (nstrvs* k x)) (card (keys))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable nst-set-card-len-nstrvs*))

(defthm sum-nsts-<=-not-next
  (implies (and (tr-impl-iinv x)
                (key-p k)
                (key-p l)
                (not (equal k l))
                (tr-impl-next x y l)
                (not (tr-impl-noblk k x))
                (subset s (keys)))
           (bnl<= (sum-nsts* k y s)
                  (sum-nsts* k x s)
                  (nstb)))
  :hints (("Subgoal *1/3"
           :in-theory (disable tr-impl-t-noblk-inv-thm
                               ==-but-g-k
                               tr-impl-t-nstrv-decreases)
           :cases ((equal l (scar s)))
           :use ((:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))
                 (:instance ==-but-g-k
                            (s (keys)))
                 (:instance tr-impl-t-noblk-inv-thm
                            (c (g l y)))
                 (:instance tr-impl-t-nstrv-decreases
                            (l (scar s))
                            (c (g (scar s) y)))))))

(defthm consp-nstrvs*
  (consp (nstrvs* k x))
  :rule-classes (:type-prescription :rewrite))

(defthm atom-cdr-redx
  (implies (and (tr-impl-iinv x)
                (key-p k))
           (iff (consp (cdr (nstrvs* k x)))
                (tr-impl-blok x k))))

;; BOZO -- this is basically same theorem as TR-IMPL-NOBLK-INV-THM..
;;         ugh.. still just gonna reuse it with this name.. (this one
;;         with no rule-classes).. and since the previous one needs
;;         to match the generated theorem from the macro perfectly,
;;         we might tweak this one and I don't want to mess the other..
;;
(defthm noblk-persists
  (implies (and (key-p k)
                (key-p l)
                (tr-impl-iinv x)
                (tr-impl-next x y l)
                (not (tr-impl-blok x l))
                (not (equal k l))
                (tr-impl-noblk k x))
           (tr-impl-noblk k y))
  :hints (("Goal" :in-theory (disable TR-IMPL-NOBLK-INV-THM)
           :use (:instance TR-IMPL-NOBLK-INV-THM)))
  :rule-classes nil)

(defthm sum-nsts-<=-
  (implies (and (tr-impl-iinv x)
                (key-p k)
                (key-p l)
                (not (equal k l))
                (subset s (keys))
                (tr-impl-next x y l))
           (bnl<= (sum-nsts* k y s) (sum-nsts* k x s) (nstb)))
  :hints (("Subgoal *1/3"
           :cases ((equal l (scar s)))
           :in-theory (disable TR-IMPL-NOBLK-INV-THM
                               tr-impl-t-noblk-inv-thm
                               tr-impl-t-nstrv-decreases
                               ==-but-g-k)
           :use ((:instance TR-IMPL-NOBLK-INV-THM
                            (l (scar s)))
                 (:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))
                 (:instance tr-impl-t-nstrv-decreases
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (s (keys)))))))

(defthm sum-nsts-<-in
  (implies (and (tr-impl-iinv x)
                (key-p k)
                (key-p l)
                (not (equal k l))
                (not (tr-impl-t-noblk (g k x) (g l x)))
                (subset s (keys))
                (tr-impl-next x y l))
           (if (in l s)
               (bnl< (sum-nsts* k y s) (sum-nsts* k x s) (nstb))
             (equal (sum-nsts* k y s) (sum-nsts* k x s))))
  :rule-classes nil
  :hints (("Subgoal *1/2"
           :cases ((equal l (scar s)))
           :in-theory (disable TR-IMPL-NOBLK-INV-THM
                               tr-impl-t-noblk-inv-thm
                               tr-impl-t-nstrv-decreases
                               ==-but-g-k)
           :use ((:instance TR-IMPL-NOBLK-INV-THM
                            (l (scar s)))
                 (:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))
                 (:instance tr-impl-t-nstrv-decreases
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (s (keys)))))))

(defthm o<-irreflexive-ordinals
  (implies (o-p x) (not (o< x x)))
  :hints (("Goal" :in-theory (enable o< o-p))))

(defthm not-blok-same-iinv
  (implies (and (tr-impl-iinv x)
                (key-p k))
           (not (tr-impl-t-blok (g k x) (g k x))))
  :hints (("Goal"
           :in-theory (disable tr-impl-t-nlock-decreases)
           :use ((:instance tr-impl-t-nlock-decreases
                            (l k))))))

(defthm pikblk-not=k
  (implies (and (key-p k)
                (tr-impl-iinv x)
                (subset s (keys))
                (tr-impl-blok* x k s))
           (not (equal (pikblk* s k x) k))))

(defthm noblk-pikblk-not-possible
  (implies (and (key-p k)
                (tr-impl-iinv x)
                (subset s (keys))
                (tr-impl-blok* x k s))
           (not (tr-impl-t-noblk (g k x)
                                 (g (pikblk* s k x) x)))))

(defthm pikblk-sum-nsts<
  (implies (and (key-p k)
                (tr-impl-iinv x)
                (tr-impl-next x y (pikblk k x))
                (tr-impl-blok x k)
                (not (tr-impl-noblk k x)))
           (bnl< (sum-nsts k y) (sum-nsts k x) (nstb)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance sum-nsts-<-in
                            (l (pikblk k x))
                            (s (keys)))))))

(in-theory (disable TR-IMPL-NOBLK-INV-THM
                    TR-IMPL-IINV-NEXT
                    tr-impl-t-noblk-inv-thm
                    tr-impl-t-nstrv-decreases
                    ==-but-g-k))

(defthm pikblk*-is-nil
  (implies (and (tr-impl-iinv x)
                (key-p k)
                (subset s (keys))
                (ti-noblk* k x s))
           (equal (pikblk* s k x) nil))
  :hints (("Subgoal *1/2"
           :use ((:instance tr-impl-t-noblk-blk-thm
                            (l (scar s)))))))

(defthm ti-noblk*-persist
  (implies (and (key-p k)
                (key-p l)
                (not (equal k l))
                (tr-impl-iinv x)
                (tr-impl-next x y l)
                (subset s (keys))
                (ti-noblk* k x s))
           (ti-noblk* k y s))
  :rule-classes nil
  :hints (("Subgoal *1/5"
           :cases ((equal l (scar s)))
           :use ((:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (s (keys)))
                 (:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))))))

(defthm bnl<-is-not=-nstb
  (implies (bnl< x y (nstb)) (not (equal x y))))


(defthm sum-nsts-=-noblk1
  (implies (and (key-p k)
                (key-p l)
                (tr-impl-iinv x)
                (tr-impl-next x y l)
                (not (tr-impl-blok x l))
                (not (equal k l))
                (subset s (keys))
                (not (ti-noblk* k x s))
                (equal (sum-nsts* k x s) (sum-nsts* k y s)))
           (equal (pikblk* s k y)
                  (pikblk* s k x)))
  :rule-classes nil
  :hints (("Subgoal *1/6"
           :cases ((equal l (scar s)))
           :use ((:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (s (keys)))
                 (:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))
                 (:instance sum-nsts-<-in
                            (l (scar s))
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-nstrv-decreases
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance tr-impl-t-noblk-blk-thm
                            (x y)
                            (l (scar s)))
                 (:instance TR-IMPL-IINV-NEXT
                            (k (scar s)))))
          ("Subgoal *1/5"
           :cases ((equal l (scar s)))
           :use ((:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (s (keys)))
                 (:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))
                 (:instance sum-nsts-<-in
                            (l (scar s))
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-nstrv-decreases
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance tr-impl-t-noblk-blk-thm
                            (x y)
                            (l (scar s)))
                 (:instance TR-IMPL-IINV-NEXT
                            (k (scar s)))))
          ("Subgoal *1/4"
           :cases ((equal l (scar s)))
           :use ((:instance ti-noblk*-persist
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (s (keys)))
                 (:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))
                 (:instance sum-nsts-<-in
                            (l (scar s))
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-nstrv-decreases
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance tr-impl-t-noblk-blk-thm
                            (x y)
                            (l (scar s)))
                 (:instance TR-IMPL-IINV-NEXT
                            (k l))
                 (:instance TR-IMPL-IINV-NEXT
                            (k (scar s)))))
          ("Subgoal *1/2"
           :cases ((equal l (scar s)))
           :use ((:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (s (keys)))
                 (:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))
                 (:instance sum-nsts-<-in
                            (l (scar s))
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-nstrv-decreases
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance tr-impl-t-noblk-blk-thm
                            (x y)
                            (l (scar s)))
                 (:instance TR-IMPL-IINV-NEXT
                            (k (scar s)))))))

(defthm sum-nsts-=-noblk2
  (implies (and (key-p k)
                (key-p l)
                (tr-impl-iinv x)
                (not (tr-impl-blok x l))
                (tr-impl-next x y l)
                (not (equal k l))
                (subset s (keys))
                (not (ti-noblk* k x s))
                (equal (sum-nsts* k x s) (sum-nsts* k y s)))
           (equal (tr-impl-blok* y k s)
                  (tr-impl-blok* x k s)))
  :rule-classes nil
  :hints (("Subgoal *1/5"
           :cases ((equal l (scar s)))
           :use ((:instance ti-noblk*-persist
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (s (keys)))
                 (:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))
                 (:instance sum-nsts-<-in
                            (l (scar s))
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-nstrv-decreases
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance tr-impl-t-noblk-blk-thm
                            (x y)
                            (l (scar s)))
                 (:instance TR-IMPL-IINV-NEXT
                            (k l))
                 (:instance TR-IMPL-IINV-NEXT
                            (k (scar s)))))
          ("Subgoal *1/4"
           :cases ((equal l (scar s)))
           :use ((:instance ti-noblk*-persist
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (s (keys)))
                 (:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))
                 (:instance sum-nsts-<-in
                            (l (scar s))
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-nstrv-decreases
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance tr-impl-t-noblk-blk-thm
                            (x y)
                            (l (scar s)))
                 (:instance TR-IMPL-IINV-NEXT
                            (k l))
                 (:instance TR-IMPL-IINV-NEXT
                            (k (scar s)))))
          ("Subgoal *1/3"
           :cases ((equal l (scar s)))
           :use ((:instance ti-noblk*-persist
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-noblk-inv-thm
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance ==-but-g-k
                            (s (keys)))
                 (:instance ==-but-g-k
                            (k (scar s))
                            (s (keys)))
                 (:instance sum-nsts-<-in
                            (l (scar s))
                            (s (sdiff s (s1 (scar s)))))
                 (:instance tr-impl-t-nstrv-decreases
                            (l (scar s))
                            (c (g (scar s) y)))
                 (:instance tr-impl-t-noblk-blk-thm
                            (x y)
                            (l (scar s)))
                 (:instance TR-IMPL-IINV-NEXT
                            (k l))
                 (:instance TR-IMPL-IINV-NEXT
                            (k (scar s)))))))

(defthm sum-nsts-=-noblk
  (implies (and (key-p k)
                (key-p l)
                (tr-impl-iinv x)
                (not (tr-impl-noblk k x))
                (equal (sum-nsts k x) (sum-nsts k y))
                (not (tr-impl-blok x l))
                (tr-impl-next x y l)
                (not (equal k l)))
           (and (equal (tr-impl-blok y k)
                       (tr-impl-blok x k))
                (equal (pikblk k y)
                       (pikblk k x))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance sum-nsts-=-noblk1
                            (s (keys)))
                 (:instance sum-nsts-=-noblk2
                            (s (keys)))))))

(in-theory (enable TR-IMPL-NOBLK-INV-THM
                   TR-IMPL-IINV-NEXT
                   tr-impl-t-noblk-inv-thm
                   tr-impl-t-nstrv-decreases
                   ==-but-g-k))

(defthm noblk-expand-nstrvs
  (implies (ti-noblk* k x s)
           (equal (sum-nsts* k x s) (bnl1 (nstb)))))

(defthm noblk-implies-not-blk
  (implies (and (key-p k)
                (tr-impl-iinv x)
                (ti-noblk* k x s)
                (subset s (keys)))
           (not (tr-impl-blok* x k s))))

(defthm cdr-nstrvs-open
  (implies (and (tr-impl-iinv x)
                (key-p k)
                (tr-impl-blok x k))
           (equal (cdr (nstrvs* k x))
                  (nstrvs* (pikblk k x) x))))

(defthm sum-nsts-total
  (implies (and (bnl<= (sum-nsts* k x s)
                       (sum-nsts* k y s)
                       (nstb))
                (bnl<= (sum-nsts* k y s)
                       (sum-nsts* k x s)
                       (nstb)))
           (equal (sum-nsts* k y s)
                  (sum-nsts* k x s)))
  :rule-classes nil)

(defthm no-strv-prep1
  (IMPLIES (AND (TR-IMPL-IINV X)
                (IN K (KEYS))
                (IN L (KEYS))
                (NOT (EQUAL K L))
                (NOT (TR-IMPL-BLOK X L))
                (TR-IMPL-NEXT X Y L)
                (NOT (TR-IMPL-NOBLK K X)))
           (bnll<= (NSTRVS* K Y)
                   (NSTRVS* K X)
                   (nstb)))
  :hints (("Goal" :induct (nstrvs* k x))
          ("Subgoal *1/2"
           :in-theory (disable sum-nsts-<=-not-next
                               TR-IMPL-IINV-NEXT)
           :use ((:instance sum-nsts-<=-not-next
                            (s (keys)))
                 (:instance sum-nsts-=-noblk)
                 (:instance TR-IMPL-IINV-NEXT
                            (k l))))
          ("Subgoal *1/1"
           :in-theory (disable sum-nsts-<=-not-next
                               TR-IMPL-IINV-NEXT)
           :cases ((equal l (pikblk k x)))
           :use ((:instance sum-nsts-<=-not-next
                            (s (keys)))
                 (:instance noblk-persists
                            (k (pikblk k x)))
                 (:instance TR-IMPL-IINV-NEXT
                            (k l))
                 (:instance sum-nsts-total
                            (s (keys)))
                 (:instance pikblk-sum-nsts<)
                 (:instance sum-nsts-=-noblk)
                 (:instance sum-nsts-<=-not-next
                            (l (pikblk* (keys) k x))
                            (s (keys))))))
  :rule-classes nil)

(defthm nstrv*-open-equal-cons
  (implies (and (syntaxp (and (consp a) (equal (car a) 'cons)))
                (consp a))
           (equal (equal (nstrvs* k x) a)
                  (and (equal (sum-nsts* k x (keys)) (car a))
                       (equal (cdr (nstrvs* k x)) (cdr a)))))
  :hints (("Goal" :do-not-induct t
           :expand (nstrvs* k x))))

(defthm starver-persists-prep1
  (IMPLIES (AND (TR-IMPL-IINV X)
                (IN K (KEYS))
                (IN L (KEYS))
                (NOT (TR-IMPL-BLOK X L))
                (TR-IMPL-NEXT X Y L)
                (NOT (EQUAL L K))
                (NOT (TR-IMPL-NOBLK K X))
                (NOT (EQUAL L (TR-IMPL-STARVER K X)))
              (EQUAL (NSTRVS* K Y)
                     (NSTRVS* K X)))
         (EQUAL (TR-IMPL-STARVER K Y)
                (TR-IMPL-STARVER K X)))
  :hints (("Subgoal *1/7"
           :use ((:instance sum-nsts-=-noblk)))
          ("Subgoal *1/6"
           :use ((:instance sum-nsts-=-noblk)))
          ("Subgoal *1/5"
           :use ((:instance sum-nsts-=-noblk)))
          ("Subgoal *1/4"
           :use ((:instance sum-nsts-=-noblk)))
          ("Subgoal *1/3"
           :use ((:instance sum-nsts-=-noblk)
                 (:instance noblk-persists
                            (k (pikblk k x)))))
          ("Subgoal *1/2"
           :in-theory (disable sum-nsts-<=-not-next)
           :use ((:instance sum-nsts-=-noblk)
                 (:instance pikblk-sum-nsts<)
                 (:instance sum-nsts-<=-not-next
                            (l (pikblk* (keys) k x))
                            (s (keys))))))
    :rule-classes nil)

(defthm no-starver-prep1
  (IMPLIES (AND (TR-IMPL-IINV X)
                (IN K (KEYS))
                (NOT (EQUAL (TR-IMPL-STARVER K X) K))
                (TR-IMPL-NEXT X Y (TR-IMPL-STARVER K X))
                (NOT (TR-IMPL-NOBLK K X)))
           (bnll< (NSTRVS* K Y)
                  (NSTRVS* K X)
                  (nstb)))
  :hints (("Goal" :induct (nstrvs* k x))          
          ("Subgoal *1/1.6"
           :in-theory (disable sum-nsts-<=-not-next)
           :use ((:instance sum-nsts-<=-not-next
                            (l (pikblk k x))
                            (s (keys)))
                 (:instance sum-nsts-=-noblk
                            (l (pikblk k x)))))
          ("Subgoal *1/1.5"
           :in-theory (disable sum-nsts-<=-not-next)
           :use ((:instance pikblk-sum-nsts<)
                 (:instance sum-nsts-<=-not-next
                            (l (pikblk k x))
                            (s (keys)))
                 (:instance sum-nsts-=-noblk
                            (l (pikblk k x)))))
          ("Subgoal *1/1.4"
           :in-theory (disable sum-nsts-<=-not-next)
           :use ((:instance sum-nsts-<=-not-next
                            (l (pikblk k x))
                            (s (keys)))
                 (:instance sum-nsts-=-noblk
                            (l (pikblk k x)))))
          ("Subgoal *1/1.3"
           :in-theory (disable sum-nsts-<=-not-next)
           :use ((:instance pikblk-sum-nsts<)
                 (:instance sum-nsts-<=-not-next
                            (l (pikblk k x))
                            (s (keys)))
                 (:instance sum-nsts-=-noblk
                            (l (pikblk k x)))))
          ("Subgoal *1/1.2"
           :in-theory (disable sum-nsts-<=-not-next)
           :use ((:instance sum-nsts-<=-not-next
                            (l (tr-impl-starver (pikblk k x) x))
                            (s (keys)))))
          ("Subgoal *1/1.1"
           :in-theory (disable sum-nsts-<=-not-next
                               TR-IMPL-STARVER-THM)
           :use ((:instance TR-IMPL-STARVER-THM
                            (K (PIKBLK* (KEYS) K X)))
                 (:instance sum-nsts-<=-not-next
                            (l (tr-impl-starver (pikblk k x) x))
                            (s (keys)))
                 (:instance sum-nsts-=-noblk
                            (l (tr-impl-starver (pikblk k x) x))))))
  :rule-classes nil)

(DEFTHM TR-IMPL-NO-STARVER-THM
  (IMPLIES (AND (TR-IMPL-IINV X)
                (KEY-P K)
                (NOT (EQUAL (TR-IMPL-STARVER K X) K))
                (TR-IMPL-NEXT X Y (TR-IMPL-STARVER K X))
                (NOT (TR-IMPL-NOBLK K X)))
           (O< (TR-IMPL-NSTRV K Y)
               (TR-IMPL-NSTRV K X)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable TR-IMPL-STARVER-THM)
           :use ((:instance no-starver-prep1)
                 (:instance TR-IMPL-STARVER-THM)
                 (:instance TR-IMPL-IINV-NEXT
                            (k (tr-impl-starver k x)))))))

(DEFTHM TR-IMPL-NO-STRV-THM
  (IMPLIES (AND (TR-IMPL-IINV X)
                (KEY-P K)
                (KEY-P L)
                (NOT (EQUAL K L))
                (TR-IMPL-NEXT X Y L)
                (NOT (TR-IMPL-BLOK X L))
                (NOT (TR-IMPL-NOBLK K X)))
           (O<= (TR-IMPL-NSTRV K Y)
                (TR-IMPL-NSTRV K X)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance no-strv-prep1)
                 (:instance TR-IMPL-IINV-NEXT
                            (k l))))))

(DEFTHM TR-IMPL-STARVER-PERSISTS
  (IMPLIES (AND (TR-IMPL-IINV X)
                (KEY-P K)
                (KEY-P L)
                (TR-IMPL-NEXT X Y L)
                (NOT (TR-IMPL-BLOK X L))
                (NOT (EQUAL L K))
                (NOT (TR-IMPL-NOBLK K X))
                (NOT (EQUAL L (TR-IMPL-STARVER K X)))
                (EQUAL (TR-IMPL-NSTRV K Y)
                       (TR-IMPL-NSTRV K X)))
           (EQUAL (TR-IMPL-STARVER K Y)
                  (TR-IMPL-STARVER K X)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance =-bnll->o-implies-equal
                            (x (nstrvs* k y))
                            (y (nstrvs* k x))
                            (n (card (keys)))
                            (b (nstb)))
                 (:instance starver-persists-prep1)
                 (:instance TR-IMPL-IINV-NEXT
                            (k l))))))

(defthm tr-map-init-help
  (implies (and (tr-impl-init* x s)
                (subset s (keys)))
           (tr-spec-init* (tr-impl-map x) s))
  :hints (("Goal" :induct (simple-set-ind s))))

(DEFTHM TR-IMPL-MAP-INIT-TO-INIT
  (IMPLIES (TR-IMPL-INIT X)
           (TR-SPEC-INIT (TR-IMPL-MAP X)))
  :hints (("Goal" :in-theory (disable tr-impl-map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; P1::: IMPORTANT NOTE:
;;  As we mentioned before, the only non-local properties from this encapsulation are the following macros which
;;  expand as we presented before and represent the assumptions we make moving forward:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-system-props  tr-impl key-p)
(def-valid-system  tr-impl key-p)
(def-match-systems tr-impl tr-spec key-p)

