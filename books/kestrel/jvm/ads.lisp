; Addresses and new addresses
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;This book is about generating new ("fresh") elements that are not members of a given set.  The intended application will be to generate "new" addresses for a map or heap (the set in question will be the "domain" of the map or heap, and the goal will be to generate new addresses that are not bound in that domain).
;A simple approach would be to just call len on the map/heap, but that would require the invariant that all addresses bound in the heap are less than its length, which I don't want to have to maintain.
;Instead, the basic approach in this book is to first get the domain of the map/heap (the set of bound addresses) and then find an address which is not in that set.
;The functions in this book are guaranteed to return fresh addresses (even if, for example, the addresses already in use are not numbered consecutively).
;Often one wants to get a bunch of new addresses at once (e.g., "give me 64 new addresses").  This book provides functions for doing that.
;Also, one sometimes wants to talk about a chunk of addresses not starting with the first fresh address. example: a program allocates two objects and then an array with 64 subarrays.  the subarrays will occupy "new addresses 3 through 66".  this book provides (or will provide!) a way to specify such things.

;FIXME what about issues of addresses becoming unbound if we set values to nil?

;fixme include less?
(include-book "kestrel/lists-light/memberp-def" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(local (include-book "kestrel/lists-light/memberp2" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(include-book "kestrel/sets/sets" :dir :system)


;move
;may be safer that take-of-cons
(defthm take-of-cons-when-posp
  (implies (posp n)
           (equal (take n (cons a x))
                  (cons a (take (+ -1 n) x))))
  :hints (("Goal" :in-theory (enable take))))

(defthm intersection-equal-of-singleton-iff-arg2
  (iff (intersection-equal x (list a))
       (member-equal a x)))

;move
(defthm no-duplicatesp-equal-of-reverse-list
  (equal (no-duplicatesp-equal (reverse-list x))
         (no-duplicatesp-equal x))
  :hints (("Goal" :in-theory (enable reverse-list no-duplicatesp-equal))))

(defthm no-duplicatesp-equal-of-nthcdr
  (implies (no-duplicatesp-equal x)
           (no-duplicatesp-equal (nthcdr n x)))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal nthcdr))))

;; An address in the JVM heap is just a natural number:
;FIXME Should NULL be an addressp?
(defund addressp (x)
  (declare (xargs :guard t))
  (natp x))

;Don't remove this theorem; it justifies the inclusion of addressp in
;*known-predicates-except-not* in Axe.
(defthm booleanp-of-addressp
  (booleanp (addressp x)))

;fixme think about the uses of this.  instead of using this, maybe
;change the model to be more defensive (that is, check whether the
;thing that must be an address is in fact an address, and throw an
;error if not).
(defund addressfix (item)
  (declare (xargs :guard t))
  (nfix item))

(defthm addressp-of-addressfix
  (acl2::addressp (addressfix item))
  :hints (("Goal" :in-theory (enable acl2::addressp addressfix))))

(defthm addressfix-when-addressp
  (implies (addressp x)
           (equal (addressfix x)
                  x))
  :hints (("Goal" :in-theory (enable acl2::addressp addressfix))))

(defthm equal-of-addressfix-same
  (equal (equal x (addressfix x))
         (addressp x))
  :hints (("Goal" :in-theory (enable addressfix))))

;the addresses now come in in a set (because rkeys returns a set)
;returns the smallest integer >= current-try which is not in ads
;prove that property?
(defund new-ad-aux (ads current-try)
  (declare (xargs :measure (set::cardinality ads)
                  :hints (("goal" :in-theory (disable ;DELETE-FROM-SET-IS-JUST-REMOVE
                                              )))
                  :guard (and (acl2-numberp current-try)
                              (set::setp ads))))
  (if (not (set::in current-try ads))
      current-try
    (new-ad-aux (set::delete current-try ads)
                (+ 1 current-try))))

(defthmd new-ad-not-bound-helper
  (<= current-try (new-ad-aux ads current-try))
  :hints (("Goal" :in-theory (enable new-ad-aux))))

(defthm integerp-of-new-ad-aux
  (implies (integerp current-try)
           (integerp (new-ad-aux ads current-try)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable new-ad-aux))))

;won't bind an adr which is in used-adrs or which is bound in the heap
;Takes a set of adresses and returns a fresh address not in that list.
;should this setify its argument before passing it to new-ad-aux?
(defund new-ad (ads)
  (declare (xargs :guard (set::setp ads)))
  (new-ad-aux ads 0))

(defthm new-ad-non-negative
  (<= 0 (new-ad ads))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable new-ad new-ad-not-bound-helper))))

(defthm integerp-of-new-ad
  (integerp (new-ad ads))
  :rule-classes (:rewrite :type-prescription))

;fixme abstract natp to addressp?
(defthm natp-of-new-ad
  (natp (new-ad ads)))

;strengthen to memberp?
(defthm new-ad-not-bound-helper2
  (equal (set::in (new-ad-aux ads current-try) ads)
         nil)
  :hints (("subgoal *1/2"
           :use (:instance new-ad-not-bound-helper
                           (ads (set::delete CURRENT-TRY ADS))
                           (current-try (+ 1 current-try))))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (new-ad-aux) ( ;DELETE-FROM-SET-IS-JUST-REMOVE
                                         )))))

;The key property of NEW-AD.
;rename
(defthm new-ad-not-memberp-ads
  (equal (set::in (new-ad ads) ads)
         nil)
  :hints (("Goal" :in-theory (enable new-ad))))


;n should be 1 or greater (should we shift things to allow 0??)
;could define this by calling n-new-ads?
(defund nth-new-ad (n ads)
  (declare (type (integer 0 *) n)
           (xargs :guard (set::setp ads)))
  (if (or (zp n)
          (equal 1 n))
      (new-ad ads)
    (nth-new-ad (+ -1 n) (set::insert (new-ad ads) ads))))

;; (defun n-new-ads (n ads)
;;   (if (zp n)
;;       nil ;emptyset
;;     (set::insert (nth-new-ad n ads)
;;                  (n-new-ads (+ -1 n) ads))))

;BOZO write this using sets as above?  did we already abandon that idea?
;returns a list
;inefficient!
(defun n-new-ads-aux (n ads)
  (declare (type (integer 0 *) n)
           (xargs :guard (set::setp ads)))
  (if (zp n)
      nil ;empty list
    (cons (nth-new-ad n ads)
          (n-new-ads-aux (+ -1 n) ads))))

;returns a list
;inefficient!
(defund n-new-ads (n ads)
  (declare (type (integer 0 *) n)
           (xargs :guard (set::setp ads)))
  (reverse-list (n-new-ads-aux n ads)))

;returns a list
;fixme numbering starts at 1?
(defun new-ads-slice (start end ads)
  (declare (type (integer 1 *) start end)
           (xargs :guard (set::setp ads)))
  (nthcdr (+ -1 start) (n-new-ads end ads)))


(defthm in-of-nth-new-ad-and-n-new-ads
  (implies (and (integerp n)
                (< 0 n))
           (memberp (NTH-NEW-AD n ADS) (N-NEW-ADS n ADS)))
  :hints (("Goal" :expand ((N-NEW-ADS-AUX 1 ADS)
                           (N-NEW-ADS 1 ADS))
           :in-theory (e/d (N-NEW-ADS) (reverse)))))

(defthm NTH-NEW-AD-of-1
  (equal (NTH-NEW-AD 1 ads)
         (new-ad ads))
  :hints (("Goal"
           :in-theory (e/d (NTH-NEW-AD) ()))))

(defthm in-of-new-ad-and-n-new-ads
  (implies (and (integerp n)
                (< 0 n))
           (memberp (NEW-AD ADS) (N-NEW-ADS n ADS)))
  :hints (("Goal" :expand ((N-NEW-ADS-AUX 1 ADS)
                           (N-NEW-ADS 1 ADS))
           :in-theory (enable N-NEW-ADS))))


;drop?
(defthm new-ad-aux-bound
  (implies (integerp start)
           (<= start (new-ad-aux ads start)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal"  :do-not '(generalize eliminate-destructors)
           :in-theory (enable NEW-AD-aux))))

(defthm new-ad-aux-<=-new-ad-aux-when-subset
  (implies (and (set::subset ads ads2)
                (integerp start))
           (<= (new-ad-aux ads start)
               (new-ad-aux ads2 start)))
  :hints (("Goal"  :do-not '(generalize eliminate-destructors)
           :in-theory (enable new-ad-aux))))

;gen?
(defthm new-ad-subset-bound
  (<= (new-ad ads)
      (new-ad (set::insert (new-ad ads) ads)))
  :hints (("Goal" :in-theory (enable new-ad))))

(defthm nth-new-ad-of-insert-new-ad
  (implies (and (integerp n)
                (< 0 n))
           (equal (nth-new-ad n (set::insert (new-ad ads) ads))
                  (nth-new-ad (+ 1 n) ads)))
  :hints (("Goal" :in-theory (enable nth-new-ad))))


(defthm new-ad-of-sfix
  (equal (new-ad (set::sfix ads))
         (new-ad ads))
  :hints (("Goal" :in-theory (enable new-ad new-ad-aux))))

(defthm not-equal-new-ad-when-bound
  (implies (set::in x ads)
           (equal (equal x (new-ad ads))
                  nil)))

(defthm not-equal-new-ad-when-bound-alt
  (implies (set::in x ads)
           (not (equal (new-ad ads) x))))

(defthm equal-nth-new-ad-nil
  (equal (equal (nth-new-ad n ads) nil)
         nil))

(defthm equal-nth-new-ad-nil2
  (equal (equal nil (nth-new-ad n ads))
         nil))





(defthm nth-new-ad-not-in-ads
  (equal (set::in (nth-new-ad n ads) ads)
         nil)
  :hints (("Goal" :in-theory (enable nth-new-ad))))


(defthm nth-new-ad-collect
  (equal (new-ad (set::insert (new-ad ads) ads))
         (nth-new-ad 2 ads))
  :hints (("Goal" :expand (nth-new-ad 2 ads)
           :in-theory (enable nth-new-ad))))

(defthm not-equal-nth-new-ad-when-bound
  (implies (set::in x ads)
           (equal (equal x (nth-new-ad n ads))
                  nil)))

(defthm not-equal-nth-new-ad-when-bound-alt
  (implies (set::in x ads)
           (equal (equal (nth-new-ad n ads) x)
                  nil)))

;sort of lets us keep from deciding which we prefer
(defthm new-ad-equal-nth-new-ad
  (equal (equal (new-ad ads) (nth-new-ad 1 ads))
         t)
  :hints (("Goal" :in-theory (enable nth-new-ad))))

(defthm n-new-ads-of-0
  (equal (n-new-ads 0 ads)
         nil)
  :hints (("Goal" :in-theory (enable n-new-ads))))


(defthm equal-new-ad-nil
  (equal (equal (new-ad ads) nil)
         nil))

(defthm equal-new-ad-nil2
  (equal (equal nil (new-ad ads))
         nil))



;strengthen?
(defthm new-ad-not-equal-nth-new-ad
  (implies (and (integerp n)
                (< 1 n))
           (not (equal (new-ad ads) (nth-new-ad n ads))))
  :hints (("Goal" :expand (nth-new-ad 2 ads)
           :in-theory (e/d (nth-new-ad) (nth-new-ad-of-insert-new-ad NTH-NEW-AD-COLLECT)))))

(defthm consp-of-n-new-ads
  (equal (consp (n-new-ads n ads))
         (not (zp n)))
  :hints (("Goal" :in-theory (enable n-new-ads))))

(defthm equal-nth-new-ad-nth-new-ad
  (implies (and (posp m)
                (posp n))
           (equal (EQUAL (NTH-NEW-AD M ADS) (NTH-NEW-AD N ADS))
                  (equal n m)))
  :hints (("Goal" :in-theory (e/d (NTH-NEW-AD) (NTH-NEW-AD-OF-INSERT-NEW-AD)))))

(defthm not-memberp-nth-new-ad-n-new-ads
  (IMPLIES (AND (> m n)
                (natp n)
                (natp m)
                )
           (not (MEMBERP (NTH-NEW-AD m ADS) (N-NEW-ADS-AUX n ADS))))
  :hints (("Goal" :in-theory (enable N-NEW-ADS-AUX))))

(defthm no-duplicatesp-equal-of-n-new-ads
  (no-duplicatesp-equal (n-new-ads n ads))
  :hints (("Goal" :in-theory (enable n-new-ads ;no-duplicatesp-equal-of-cons
                                     ))))

(defthm len-of-n-new-ads
  (implies (natp n)
           (equal (len (n-new-ads n ads))
                  n))
  :hints (("Goal" :in-theory (enable n-new-ads))))

(defthm true-listp-of-n-new-ads
  (true-listp (n-new-ads n ads))
  :hints (("Goal" :in-theory (enable n-new-ads))))

;switch to use last-elem
(defthm car-last-of-n-new-ads-aux
  (implies (not (zp n))
           (EQUAL (CAR (LAST (N-NEW-ADS-AUX n ADS)))
                  (NEW-AD ADS)))
  :hints (("Goal" :in-theory (enable n-new-ads-aux))))

(defthm len-of-N-NEW-ADS-AUX
  (implies (natp n)
           (equal (len (N-NEW-ADS-AUX n ads))
                  n)))

(defthm consp-of-N-NEW-ADS-AUX
  (equal (consp (N-NEW-ADS-AUX n ads))
         (and (integerp n)
              (< 0 n)))
  :hints (("Goal" :expand ((N-NEW-ADS-AUX 1 ADS)))))

;; (defthm n-new-ads-2-recollect
;;   (equal (set::insert (new-ad ads) (set::insert (nth-new-ad 2 ads) ads))
;;          (set::union (n-new-ads 2 ads) ads))
;;   :hints (("Goal" :expand ((n-new-ads 1 ads)
;;                            (n-new-ads 2 ads))
;;            :in-theory (enable n-new-ads nth-new-ad))))

;; (defthm n-new-ads-2-recollect-two
;;   (equal (set::insert (nth-new-ad 1 ads) (set::insert (nth-new-ad 2 ads) ads))
;;          (set::union (n-new-ads 2 ads) ads))
;;   :hints (("Goal" :expand ((n-new-ads 1 ads)
;;                            (n-new-ads 2 ads))
;;            :in-theory (e/d (n-new-ads nth-new-ad) (N-NEW-ADS-2-RECOLLECT)))))

;gross proof?
;; (defthm insert-new-ad-hack
;;   (implies (and (integerp n)
;;                 (<= 0 n))
;;            (equal (set::insert (new-ad ads) (n-new-ads n (set::insert (new-ad ads) ads)))
;;                   (n-new-ads (+ 1 n) ads)))
;;   :hints (("Goal" :in-theory (e/d (n-new-ads) (SET::USE-WEAK-INSERT-INDUCTION)))))

;; (defthm new-ad-of-union-with-n-new-ads
;;   (implies (and (integerp n)
;;                 (< 0 n))
;;            (equal (new-ad (set::union ads (n-new-ads (+ -1 n) ads)))
;;                   (nth-new-ad n ads)))
;;   :hints (("subgoal *1/4" :use (:instance insert-new-ad-hack (n (+ -2 n)))
;;            :in-theory (disable insert-new-ad-hack))
;;           ("Goal" :in-theory (enable nth-new-ad
;;                                      ;;n-new-ads
;;                                      ))))

;; ;matches better
;; (defthm new-ad-of-union-with-n-new-ads-better
;;   (implies (and (integerp n)
;;                 (<= 0 n))
;;            (equal (new-ad (set::union ads (n-new-ads n ads)))
;;                   (nth-new-ad (+ 1 n) ads)))
;;   :hints (("Goal" :use (:instance new-ad-of-union-with-n-new-ads (n (+ 1 n)))
;;            :in-theory (disable new-ad-of-union-with-n-new-ads)))
;;   )


;; (thm
;;  (implies (and (integerp n) (< 0 n))
;;           (equal (nth-new-ad 1 (set::union ads (n-new-ads n ads)))
;;                  (nth-new-ad (+ 1 n) ads)))
;;  :hints (("Goal"
;; ;          :expand (nth-new-ad (+ 1 n) ads)
;; ;          :induct (ind-hint m n ads)
;;           :do-not '(generalize eliminate-destructors)
;;           :in-theory (e/d (nth-new-ad
;;                            n-new-ads
;;                            )
;;                           (n-new-ads-2-recollect-two n-new-ads-2-recollect)))))

;; (thm
;;  (implies (and (integerp n) (< 0 n)
;;                (integerp m) (< 0 m))
;;           (equal (nth-new-ad m (set::union ads (n-new-ads n ads)))
;;                  (nth-new-ad (+ m n) ads)))
;;  :hints (("Goal"
;; ;          :expand (nth-new-ad (+ 1 n) ads)
;;           :induct (ind-hint m n ads)
;;           :do-not '(generalize eliminate-destructors)
;;           :in-theory (e/d (;nth-new-ad
;;                            n-new-ads
;;                            )
;;                           (n-new-ads-2-recollect-two n-new-ads-2-recollect)))))

;; (thm
;;  (implies (and (integerp n)
;;                (< 0 n))
;;           (equal (new-ad (set::union ads (n-new-ads n ads)))
;;                  (nth-new-ad (+ 1 n) ads)))
;;  :hints (("Goal"
;;           :expand (nth-new-ad (+ 1 n) ads)
;;           :in-theory (e/d (nth-new-ad
;; ;n-new-ads
;;                            )
;;                           (N-NEW-ADS-2-RECOLLECT-TWO N-NEW-ADS-2-RECOLLECT)))))

;; (defthm n-new-ads-recollect-3
;;   (equal (set::insert (nth-new-ad 2 ads) (set::insert (new-ad ads) ads))
;;          (set::union (n-new-ads 2 ads) ads))
;;   :hints (("Goal" :expand ((n-new-ads 1 ads)
;;                            (n-new-ads 2 ads))
;;            :in-theory (e/d (n-new-ads nth-new-ad) (n-new-ads-2-recollect)))))

;; (defthm new-ads-recollect
;;   (implies (and (equal m (+ 1 n))
;;                 (integerp n)
;;                 (integerp m)
;;                 (< 0 m))
;;            (equal (SET::INSERT (NTH-NEW-AD m ads) (SET::UNION ads (N-NEW-ADS n ads)))
;;                   (set::union ads (N-NEW-ADS m ads))))
;;   :hints (("Goal" :in-theory (enable n-new-ads))))

;; (defthm new-ads-recollect-alt
;;   (implies (and (equal m (+ 1 n))
;;                 (integerp n)
;;                 (integerp m)
;;                 (< 0 m))
;;            (equal (SET::INSERT (NTH-NEW-AD m ads) (SET::UNION (N-NEW-ADS n ads) ads))
;;                   (set::union ads (N-NEW-ADS m ads))))
;;   :hints (("Goal" :use (:instance new-ads-recollect)
;;            :in-theory (disable new-ads-recollect))))

;; (defthm not-in-n-new-ads
;;   (implies (set::in ad ads)
;;            (not (set::in ad (n-new-ads n ads))))
;;   :hints (("Goal" :in-theory (enable n-new-ads))))

(defthm not-memberp-n-new-ads
  (implies (set::in ad ads)
           (not (memberp ad (n-new-ads n ads))))
  :hints (("Goal" :in-theory (enable n-new-ads))))

(defthm nth-of-n-new-ads
  (implies (and (natp n) (natp m) (< n m) (<= 0 n))
           (equal (nth n (n-new-ads m ads))
                  (nth-new-ad (+ 1 n) ads)))
  :hints (("Goal" :in-theory (enable n-new-ads))))

(theory-invariant (incompatible (:definition nth-new-ad) (:rewrite NTH-NEW-AD-OF-INSERT-NEW-AD)))

(defthm car-of-n-new-ads
  (implies (and (natp n)
                (< 0 n))
           (equal (car (n-new-ads n ads))
                  (new-ad ads)))
  :hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0) ()))))

(defthmd cons-new-ad-and-2nd-ad
   (equal (cons (new-ad ads) (cons (nth-new-ad '2 ads) lst))
          (append (n-new-ads 2 ads) lst))
   :hints (("Goal" :in-theory (disable nth-new-ad-of-insert-new-ad NTH-NEW-AD-COLLECT)
            :expand ((n-new-ads 2 ads)
                     (n-new-ads-aux 2 ads)
                     (n-new-ads-aux 1 ads)
                     (nth-new-ad 2 ads))))
   :otf-flg t)

;; (defthmd n-new-ads-expand-constant
;;   (implies (and (syntaxp (quotep n))
;;                 (not (zp n)))
;;            (equal (n-new-ads n ads)
;;                   (cons (nth-new-ad n ads)
;;                         (n-new-ads (+ -1 n) ads))))
;;   :hints (("Goal" :in-theory (enable n-new-ads))))

(defthm n-new-ads-aux-hack
  (implies (not (zp n))
           (not (equal (n-new-ads-aux n (set::insert (new-ad ads) ads))
                       (n-new-ads-aux n ads)))))

(defthm n-new-ads-aux-of-insert-of-new-ad
  (implies (natp n)
           (equal (n-new-ads-aux n (set::insert (new-ad ads) ads))
                  (butlast (n-new-ads-aux (+ 1 n) ads) 1)))
  :hints (("Goal" :induct (n-new-ads-aux n ads)
           :in-theory (e/d (n-new-ads-aux) (take-of-cons ;looped
                                            cons-equal)))))

(defthm n-new-ads-of-insert-new-ad
  (implies (natp n)
           (equal (n-new-ads n (set::insert (new-ad ads) ads))
                  (new-ads-slice 2 (+ 1 n) ads)))
  :hints (("Goal" :in-theory (enable N-NEW-ADS))))

(defthm cdr-of-n-new-ads
  (implies (not (zp n))
           (equal (cdr (n-new-ads n ads))
                  (new-ads-slice 2 n ads)))
  :hints (("Goal" :in-theory (enable new-ads-slice))))

(in-theory (disable new-ads-slice))

(defthm new-ad-not-memberp-of-new-ads-slice ;new-ads-not-memberp-of-new-ads-slice
  (implies (and (< 1 start)
                (natp start))
           (equal (memberp (NEW-AD ads) (NEW-ADS-SLICE start end ads))
                  nil))
  :hints (("Goal" :in-theory (enable new-ads-slice N-NEW-ADS))))


(defthm len-of-new-ads-slice
  (implies (and (<= start end)
                (natp start)
                (< 0 start)
                (natp end))
           (equal (len (new-ads-slice start end ads))
                  (+ 1 end (- start))))
  :hints (("Goal" :in-theory (enable new-ads-slice))))

(defthm no-duplicatesp-equal-of-new-ads-slice
  (no-duplicatesp-equal (new-ads-slice start end ads))
  :hints (("Goal" :in-theory (enable new-ads-slice))))



(defthm not-memberp-of-new-ads-slice
  (implies (set::in ad ads)
           (equal (memberp ad (new-ads-slice start end ads))
                  nil))
  :hints (("Goal" :in-theory (enable new-ads-slice))))

(defthm nth-of-new-ads-slice
 (implies (and (natp n)
               (<= n (- end start))
               (<= start end)
               (natp start)
               (< 0 start)
               (natp end))
          (equal (nth n (new-ads-slice start end ads))
                 (nth-new-ad (+ n start) ads)))
  :hints (("Goal" :in-theory (enable new-ads-slice))))

(defthm memberp-of-nth-new-ad-and-new-ads-slice
  (implies (and (natp n)
                (< 0 n)
                (natp start)
                (natp end)
                (<= start n)
                (<= n end))
           (equal (memberp (nth-new-ad n ads) (new-ads-slice start end ads))
                  t))
  :hints (("Goal" :in-theory (enable new-ads-slice N-NEW-ADS))))

(defthm new-ad-not-memberp-of-new-ads
  (implies (and (natp start)
                (< 1 start))
           (equal (memberp (new-ad ads) (new-ads-slice start end ads))
                  nil))
  :hints (("Goal" :in-theory (enable new-ads-slice n-new-ads))))

(defthm new-ads-slice-iff
  (implies (and (natp start)
                (natp end)
                (<= 1 start))
           (iff (new-ads-slice start end ads)
                (<= start end)))
  :hints (("Goal" :in-theory (enable new-ads-slice n-new-ads))))

(defthm new-ads-type
  (implies (and (natp start)
                (natp end)
                (<= 1 start)
                (<= start end))
           (consp (new-ads-slice start end ads)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable new-ads-slice n-new-ads))))

(defthmd new-ads-slice-recollect-1
  (implies (and (natp m)
                (< 0 m)
                (natp n)
                (equal n (+ 1 m)))
           (equal (cons (nth-new-ad m ads) (cons (nth-new-ad n ads) nil))
                  (new-ads-slice m n ads)))
  :hints (("Goal" :in-theory (enable new-ads-slice
                                     cdr-of-nthcdr))))

(defthmd new-ads-slice-recollect-2
  (implies (and (natp m)
                (< 0 m)
                (natp n)
                (equal n (+ 1 m)))
           (equal (cons (nth-new-ad m ads) (cons (nth-new-ad n ads) lst))
                  (append (new-ads-slice m n ads) lst)))
  :hints (("Goal" :in-theory (enable new-ads-slice
                                     cdr-of-nthcdr))))

(defthm new-ads-slice-out-of-order-indices
  (implies (and (< n m)
                (natp n)
                (natp m))
           (equal (new-ads-slice m n ads)
                  nil))
  :hints (("Goal" :in-theory (enable new-ads-slice))))

;disable?!
(defthm new-ads-slice-opener
  (implies (and (natp m)
                (< 0 m)
                (natp n)
                (<= m n))
           (equal (NEW-ADS-SLICE m n ads)
                  (cons (nth-new-ad m ads) (NEW-ADS-SLICE (+ 1 m) n ads))))
  :hints (("Goal" :in-theory (enable new-ads-slice ;equal-cons-cases2
                                     cdr-of-nthcdr))))

(defthm memberp-of-new-ad-cons-nth-new-ad
 (implies (and (natp n)
               (< 0 n)
               (not (equal 1 n)))
          (equal (MEMBERP (NEW-AD ads) (CONS (NTH-NEW-AD n ads) lst))
                 (MEMBERP (NEW-AD ads) lst))))

(defthm n-new-ads-iff
  (iff (n-new-ads n ads)
       (not (zp n)))
  :hints (("Goal" :in-theory (enable n-new-ads))))

(encapsulate
 ()
 (local (defthm fw
          (IMPLIES (AND (NATP NUM)
                        (< 0 N)
                        (NATP N)
                        (NOT (MEMBERP (NTH-NEW-AD N ADS)
                                            (N-NEW-ADS-AUX NUM ADS))))
                   (< NUM N))
          :hints (("Goal" :in-theory (disable ;CANCEL-<-+
                                      ))) ;bozo why?
          ))

 (defthm memberp-nth-new-ad-n-new-ads
   (implies (and (natp num)
                 (< 0 n)
                 (natp n))
            (equal (MEMBERP (NTH-NEW-AD n ads) (N-NEW-ADS num ads))
                   (<= n num)))
   :hints (("Goal" :in-theory (enable n-new-ads N-NEW-ADS-AUX)))))

;; ;bozo gross hack
;; (skip -proofs
;; (defthm 5-new-ads-recollapse
;;  (equal (CONS (NEW-AD (RKEYS (JVM::HEAP S0)))
;;            (CONS (NTH-NEW-AD '2 (RKEYS (JVM::HEAP S0)))
;;                  (CONS (NTH-NEW-AD '3 (RKEYS (JVM::HEAP S0)))
;;                        (CONS (NTH-NEW-AD '4 (RKEYS (JVM::HEAP S0)))
;;                              (CONS (NTH-NEW-AD '5 (RKEYS (JVM::HEAP S0)))
;;                                    'NIL)))))
;;         (n-new-ads 5 (RKEYS (JVM::HEAP S0)))))
;; )



;yuck?
;gen?
(defthm new-ad-<<-nth-new-ad-2
  (<< (NEW-AD ADS) (NTH-NEW-AD 2 ADS))
  :hints (("Goal" :expand ((NTH-NEW-AD 2 ADS))
           :in-theory (e/d (<< LEXORDER ALPHORDER) (NTH-NEW-AD-OF-INSERT-NEW-AD
                                                    NTH-NEW-AD-COLLECT ;bozo
                                                    )))))
;yuck?
 ;bad rule?
(defthmd list-new-ad-nth-new-ad-2
  (equal (LIST (NEW-AD ADS) (NTH-NEW-AD 2 ADS))
         (set::insert (NEW-AD ADS) (set::insert (NTH-NEW-AD 2 ADS) nil)))
  :hints (("Goal" :expand ((set::insert (NEW-AD ADS) (set::insert (NTH-NEW-AD 2 ADS) nil))
                           ))))

;; (thm
;;  (<= (NEW-AD ADS)
;;      (NEW-AD (SET::INSERT (NEW-AD ADS) ADS))))

(defthm consp-of-new-ads-slice
  (implies (and (posp start)
                (posp end))
           (equal (consp (new-ads-slice start end ads))
                  (<= start end)))
  :hints (("Goal" :in-theory (enable new-ads-slice))))

(defthm car-of-new-ads-slice
  (implies (and (<= 0 (- end start))
                (<= start end)
                (natp start)
                (< 0 start)
                (natp end))
           (equal (car (new-ads-slice start end ads))
                  (nth-new-ad start ads)))
  :hints (("Goal" :in-theory (enable new-ads-slice))))

(defthm cdr-of-new-ads-slice
  (implies (and (<= 0 (- end start))
                (<= start end)
                (natp start)
                (< 0 start)
                (natp end))
           (equal (cdr (new-ads-slice start end ads))
                  (new-ads-slice (+ 1 start) end ads)))
  :hints (("Goal" :in-theory (enable new-ads-slice
                                     cdr-of-nthcdr))))

;; (defun n-new-ads-better-aux (ads-left current-try ads acc)
;;   (declare (xargs :measure (make-ord 1 (+ 2 (nfix (+ 2 ads-left))) (+ 1 (set::cardinality ads))) ;simplify measure?
;;                   :guard (and (acl2-numberp current-try)
;;                               (set::setp ads)
;;                               (natp ads-left)
;;                               (true-listp acc))))
;;   (if (zp ads-left)
;;       (reverse-list acc)
;;     (if (set::in current-try ads)
;;         (n-new-ads-better-aux ads-left (+ 1 current-try) (set::delete current-try ads) acc)
;;       (n-new-ads-better-aux (+ -1 ads-left) (+ 1 current-try) ads (cons current-try acc)))))

;; ;old
;; ;measure is ads-left first, then the number of elements in ads that are >= than the current try?
;; ;; (skip- proofs
;; ;;  (defun n-new-ads-better-aux (ads-left current-try ads acc)
;; ;;    (declare (xargs :measure (make-ord 1 (+ 2 (nfix (+ 2 ads-left))) (+ 1 (nfix (- (maxelem ads) ;mixes sets and lists!
;; ;;                                                                                   current-try))))))
;; ;;    (if (zp ads-left)
;; ;;        (reverse-list acc)
;; ;;      (if (set::in current-try ads)
;; ;;          (n-new-ads-better-aux ads-left (+ 1 current-try) ads acc)
;; ;;        (n-new-ads-better-aux (+ -1 ads-left) (+ 1 current-try) ads (cons current-try acc))))))


;; ;(skip -proofs (verify-guards n-new-ads-better-aux))

;; (defthm len-of-n-new-ads-better-aux
;;   (equal (len (n-new-ads-better-aux ads-left current-try ads acc))
;;          (+ (nfix ads-left) (len acc)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable n-new-ads-better-aux))))

;; ;returns a list (because the order may matter)
;; (defun n-new-ads-better (n ads)
;;   (declare (xargs :guard (and (set::setp ads)
;;                               (natp n))))
;;   (n-new-ads-better-aux n 0 ads nil))


;; ;(skip -proofs (verify-guards n-new-ads-better))

;; (defthm len-of-n-new-ads-better
;;   (equal (len (n-new-ads-better n ads))
;;          (nfix n))
;;   :hints (("Goal" :in-theory (enable n-new-ads-better))))

(defthm addressfix-of-new-ad
  (equal (addressfix (new-ad ads))
         (new-ad ads))
  :hints (("Goal" :in-theory (enable addressfix))))

(defthm addressfix-of-nth-new-ad
  (equal (addressfix (nth-new-ad n ads))
         (nth-new-ad n ads))
  :hints (("Goal" :in-theory (enable addressfix))))

(defthm addressp-of-new-ad
  (addressp (new-ad ads))
  :hints (("Goal" :in-theory (enable addressfix))))

(defthm addressp-of-nth-new-ad
  (addressp (nth-new-ad n ads))
  :hints (("Goal" :in-theory (enable addressfix))))

;fixme handle all this better!
;sort the inserts, collapse into unions, etc.

(defthm new-address-hack
  (equal (NTH-NEW-AD 2
                     (SET::INSERT (NTH-NEW-AD 2 dom)
                                  (SET::INSERT (NEW-AD dom)
                                               dom)))
         (nth-new-ad 4 dom))
  :hints (("Goal" :expand ((NTH-NEW-AD 4 DOM))
           :in-theory (e/d (NTH-NEW-AD) (NTH-NEW-AD-OF-INSERT-NEW-AD)))))

(defthm new-address-hackb
  (equal (NTH-NEW-AD 2
                     (SET::INSERT (NEW-AD dom)
                                  (SET::INSERT (NTH-NEW-AD 2 dom)
                                               dom)))
         (nth-new-ad 4 dom))
  :hints (("Goal" :use (:instance new-address-hack)
           :in-theory (e/d (SET::INSERT-INSERT) ( new-address-hack)))))

(defthm new-address-hack2
  (equal (new-ad (set::insert (nth-new-ad 2 dom)
                              (set::insert (new-ad dom)
                                           dom)))
         (nth-new-ad 3 dom))
  :hints (("Goal" :expand ((nth-new-ad 3 dom))
           :in-theory (e/d (nth-new-ad) (nth-new-ad-of-insert-new-ad)))))

(defthm new-address-hack2b
  (equal (NEW-AD (SET::INSERT (NEW-AD dom)
                              (SET::INSERT (NTH-NEW-AD 2 dom)
                                           dom)))
         (nth-new-ad 3 dom))
  :hints (("Goal" :use (:instance new-address-hack2)
           :in-theory (e/d (SET::INSERT-INSERT) (new-address-hack2)))))

(theory-invariant (incompatible (:definition nth-new-ad) (:rewrite NTH-NEW-AD-COLLECT)))

(defthm new-address-hack3
  (equal (NEW-AD (SET::INSERT (NTH-NEW-AD 3 dom)
                              (SET::INSERT (NTH-NEW-AD 2 dom)
                                           (SET::INSERT (NEW-AD dom)
                                                        dom))))
         (nth-new-ad 4 dom))
  :hints (("Goal" :expand ((NTH-NEW-AD 4 DOM)
                           (NTH-NEW-AD 3 DOM)
                           (NTH-NEW-AD 2 DOM)
                           (NTH-NEW-AD 3 (SET::INSERT (NEW-AD DOM) DOM))
                           (NTH-NEW-AD 2 (SET::INSERT (NEW-AD DOM) DOM))
                           (NTH-NEW-AD 2
                                       (SET::INSERT (NEW-AD DOM)
                                                    (SET::INSERT (NEW-AD (SET::INSERT (NEW-AD DOM) DOM))
                                                                 DOM))))
           :do-not-induct t
           :in-theory (e/d (SET::INSERT-INSERT) (NTH-NEW-AD-OF-INSERT-NEW-AD
                                                 NTH-NEW-AD-COLLECT)))))

(defthm new-address-hack3b
  (equal (NEW-AD (SET::INSERT (NEW-AD dom)
                              (SET::INSERT (NTH-NEW-AD 2 dom)
                                           (SET::INSERT (NTH-NEW-AD 3 dom)
                                                        dom))))
         (nth-new-ad 4 dom))
  :hints (("Goal" :use (:instance new-address-hack3)
           :in-theory (e/d (SET::INSERT-INSERT) (new-address-hack3)))))
