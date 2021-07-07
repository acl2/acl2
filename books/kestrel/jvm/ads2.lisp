; More material on addresses
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;fixme merge with ads.lisp

;This book is about generating new ("fresh") elements that are not members of a given set.  The intended application will be to generate "new" addresses for a map or heap (the set in question will be the "domain" of the map or heap, and the goal will be to generate new "addresses" that are not bound in that domain).
;A simple approach would be to just call len on the map/heap, but that would require the invariant that all addresses bound in the heap are less than its length, which I don't want to have to maintain.
;Instead, the basic approach in this book is to first get the domain of the map/heap (the set of bound addresses) and then create an address which is not in that set.
;The functions in this book are guaranteed to return fresh addresses (even if, for example, the addresses already in use are not numbered consecutively).
;Often one wants to get a bunch of new addresses at once ("give me 64 new addresses").  This book provides functions for doing that.
;Also, one sometimes wants to talk about a chunk of addresses not starting with the first fresh address. example: a program allocates two objects and then an array with 64 subarrays.  the subarrays live at "new addresses 3 through 66".  this book provides (or will provide!) a way to specify such things.

;FIXME what about issues of addresses becoming unbound if we set values to nil?

(include-book "ads")
(include-book "kestrel/lists-light/perm" :dir :system)
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable (:induction SET::INSERT))))

;move
(defthm perm-reverse-list
  (perm (reverse-list lst) lst)
  :hints (("Goal" :in-theory (enable reverse-list))))

;move
(defthm nth-of-cons-safer
  (implies (and (syntaxp (not (and (quotep x) (quotep y))))
                (not (zp n)))
           (equal (nth n (cons x y))
                  (nth (+ -1 n) y))))

;dup
;; (defthm memberp-nth-of-self-helper
;;   (implies (< n (len lst))
;;            (equal (memberp (nth n lst) lst)
;;                   (if (<= 0 n)
;;                       t
;;                     (consp lst)
;;                     )))
;;   :hints (("Goal" :in-theory (e/d (memberp nth) (NTH-OF-CDR
;;                                                        )))))

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

(defthm new-ad-aux-of-insert-irrel
  (implies (and (< ad current-try)
                (natp ad)
                (natp current-try))
           (equal (new-ad-aux (set::insert ad ads) current-try)
                  (new-ad-aux ads current-try)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (new-ad-aux ads current-try)
           :do-not-induct t
           :expand ((NEW-AD-AUX (SET::INSERT AD ADS)
                        CURRENT-TRY))
           :in-theory (enable new-ad-aux))))

(defthmd new-ad-aux-is-current-try
  (implies (not (set::in current-try ads))
           (equal (new-ad-aux ads current-try)
                  current-try))
  :hints (("Goal" :in-theory (enable new-ad-aux))))

(defthm new-ad-aux-of-insert-irrel2
  (implies (and (not (equal ad (new-ad-aux ads current-try)))
                (natp current-try)
                (natp ad)
                (natp n))
           (equal (new-ad-aux (set::insert ad ads) current-try)
                  (new-ad-aux ads current-try)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (new-ad-aux ads current-try)
           :do-not-induct t
           :expand ((NEW-AD-AUX (SET::INSERT AD ADS)
                        CURRENT-TRY))
           :in-theory (e/d (new-ad-aux set-delete-insert-strong) ())
           )))

(defthm new-ad-aux-of-sfix
  (equal (new-ad-aux (set::sfix ads) current-try)
         (new-ad-aux ads current-try))
  :hints (("Goal" :in-theory (enable new-ad-aux))))

;ads is a set of addresses
;won't bind an adr which is in used-adrs or which is bound in the heap
;Takes a set of adresses and returns a fresh address not in that list.
;should this setify its argument before passing it to new-ad-aux?
(defund new-ad (ads)
  (declare (xargs :guard (set::setp ads)))
  (new-ad-aux ads 0))

(defthmd new-ad-recollapse
  (equal (new-ad-aux ads 0)
         (new-ad ads))
  :hints (("Goal" :in-theory (enable new-ad))))

(defthm new-ad-non-negative
  (<= 0 (new-ad ads))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable new-ad new-ad-not-bound-helper))))

(defthm integerp-of-new-ad
  (integerp (new-ad ads))
  :rule-classes (:rewrite :type-prescription))

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

(defthm not-equal-new-ad-when-bound
  (implies (set::in x ads)
           (equal (equal x (new-ad ads))
                  nil)))

(defthm new-ad-of-sfix
  (equal (new-ad (set::sfix ads))
         (new-ad ads))
  :hints (("Goal" :in-theory (enable new-ad))))

(defthm equal-new-ad-nil
  (equal (equal (new-ad ads) nil)
         nil))

(defthm equal-new-ad-nil2
  (equal (equal nil (new-ad ads))
         nil))

;gen?
(defthm new-ad-subset-bound
  (<= (new-ad ads)
      (new-ad (set::insert (new-ad ads) ads)))
  :hints (("Goal" :in-theory (enable new-ad))))

;;;
;;; n-new-ads2-aux
;;;

(defun n-new-ads2-aux (n current-try ads)
  (declare (type (integer 0 *) n)
           (xargs :guard (and (acl2-numberp current-try)
                              (set::setp ads))))
  (if (zp n)
      nil
    (let ((ad (new-ad-aux ads current-try)))
      (cons ad (n-new-ads2-aux (+ -1 n) (+ 1 ad) ads)))))

(defthm len-of-n-new-ads2-aux
  (implies (natp n)
           (equal (len (n-new-ads2-aux n current-try ads))
                  n)))

(defund n-new-ads2 (n ads)
  (declare (type (integer 0 *) n)
           (xargs :guard (SET::SETP ADS))
           )
  (n-new-ads2-aux n 0 ads))

(defthm len-of-n-new-ads2
  (implies (natp n)
           (equal (len (n-new-ads2 n ads))
                  n))
  :hints (("Goal" :in-theory (enable n-new-ads2))))

(defthm consp-of-n-new-ads2
  (equal (consp (n-new-ads2 n ads))
         (not (zp n)))
  :hints (("Goal" :in-theory (enable n-new-ads2))))

(defthm true-listp-of-n-new-ads2
  (true-listp (n-new-ads2 n ads))
  :hints (("Goal" :in-theory (enable n-new-ads2))))

(defthm n-new-ads2-of-0
  (equal (n-new-ads2 0 ads)
         nil)
  :hints (("Goal" :in-theory (enable n-new-ads2))))

;these would be faster:
;; (defun nth-new-ad2-aux (n prev-new-ad ads)
;;   (if (zp n)
;;       prev-new-ad
;;     (let ((ad (new-ad-aux ads (+ 1 prev-new-ad))))
;;       (nth-new-ad2-aux (+ -1 n) ad ads))))

;; ;n should be 1 or greater (should we shift things to allow 0??)
;; (defun nth-new-ad2 (n ads)
;;   (let ((ad (new-ad ads)))
;;     (nth-new-ad2-aux (+ -1 n) ad ads)))

;n should be 1 or greater (should we shift things to allow 0??)
(defund nth-new-ad2 (n ads)
  (if (zp n) ;bad case
      (new-ad ads)
    (nth (+ -1 n) (n-new-ads2 n ads))))

;fixme faster way to write this?
;returns a list, because the order matters
(defun new-ads-slice2 (start end ads)
  (nthcdr (+ -1 start) (n-new-ads2 end ads)))

(defthm nth-new-ad2-of-1
  (equal (nth-new-ad2 1 ads)
         (new-ad ads))
  :hints (("Goal"
           :expand ((N-NEW-ADS2-AUX 1 0 ADS)
                    (NEW-AD-AUX ADS 0))
           :in-theory (e/d (n-new-ads2 nth-new-ad2 N-NEW-ADS2-AUX new-ad) ()))))


;rename
(defthm in-of-nth-new-ad2-and-n-new-ads2
  (implies (and (integerp n)
                (< 0 n))
           (equal (memberp (NTH-NEW-AD2 n ADS)
                          (N-NEW-ADS2 n ADS))
                  t))
  :hints (("Goal" :in-theory (enable NTH-NEW-AD2))))

(local
 (defun ind (m n)
  (if (or (zp m)
          (zp n))
      (list m n)
    (ind (+ -1 m) (+ -1 n)))))

(defthm subbagp-of-n-new-ads2-aux-and-n-new-ads2-aux
  (implies (and (<= m n)
                (natp m)
                (natp n))
           (subsetp-equal (n-new-ads2-aux m try ads)
                          (n-new-ads2-aux n try ads)))
  :hints (("Goal" ;:induct (ind m n)
           :do-not '(generalize eliminate-destructors)
           :expand ()
           :in-theory (enable n-new-ads2-aux))))

(defthm subbagp-of-n-new-ads2-and-n-new-ads2
  (implies (and (<= m n)
                (natp m)
                (natp n))
           (subsetp-equal (n-new-ads2 m ads)
                          (n-new-ads2 n ads)))
  :hints (("Goal" :in-theory (enable n-new-ads2))))

(defthm member-of-nth-new-ad2-and-n-new-ads2-gen
  (implies (and (natp n)
                (<= m n)
                (posp m))
           (memberp (nth-new-ad2 m ads)
                    (n-new-ads2 n ads)))
  :hints (("Goal" :in-theory (disable ;bag::memberp-subbagp
                              MEMBERP-WHEN-SUBSETP-EQUAL-1
                              MEMBERP-WHEN-SUBSETP-EQUAL-2
                              )
           :use (:instance MEMBERP-WHEN-SUBSETP-EQUAL-1
                           (x (N-NEW-ADS2 N ADS))
                           (A (NTH-NEW-AD2 M ADS))
                           (y (n-new-ads2 m ads)))
;           :use (:instance bag::memberp-subbagp (bag::a (nth-new-ad2 m ads)) (bag::y (n-new-ads2 m ads)) (bag::x (n-new-ads2 n ads)))
           )))


;rename
(defthm in-of-new-ad-and-n-new-ads2
  (implies (and (integerp n)
                (< 0 n))
           (equal (memberp (NEW-AD ADS)
                          (N-NEW-ADS2 n ADS))
                  t))
  :hints (("Goal" :use (:instance member-of-nth-new-ad2-and-n-new-ads2-gen (m 1))
           :in-theory (disable member-of-nth-new-ad2-and-n-new-ads2-gen))))

(defthm n-new-ads2-aux-of-insert-irrel
  (implies (and (< ad current-try)
                (natp current-try)
                (natp ad)
                (natp n)
                )
           (equal (n-new-ads2-aux n current-try (set::insert ad ads))
                  (n-new-ads2-aux n current-try ads)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (n-new-ads2-aux n current-try ads)
           :expand ((N-NEW-ADS2-AUX N CURRENT-TRY (SET::INSERT AD ADS)))
           )))

(defthm n-new-ads2-aux-of-insert-irrel2
  (implies (and (not (memberp ad (n-new-ads2-aux n current-try ads))) ;this case
                (natp current-try)
                (natp ad)
                (natp n))
           (equal (n-new-ads2-aux n current-try (set::insert ad ads))
                  (n-new-ads2-aux n current-try ads)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (n-new-ads2-aux n current-try ads)
           :do-not-induct t
           :expand (;(NEW-AD-AUX ADS CURRENT-TRY)
                    ;(NEW-AD-AUX (SET::INSERT AD ADS) CURRENT-TRY)
                    (N-NEW-ADS2-AUX N CURRENT-TRY (SET::INSERT AD ADS)))
           :in-theory (e/d (new-ad-aux-is-current-try) ())
           )))



;the last case is when ad is in (n-new-ads2-aux n current-try ads)
;prove a theorem about splitting n-new-ads2-aux  ?  then split right at the point of insertion?  or union??

(defthm new-ad-aux-of-delete-irrel
  (implies (and (< x current-try)
                (natp x)
                (natp current-try))
           (equal (new-ad-aux (set::delete x ads) current-try)
                  (new-ad-aux ads current-try)))
  :hints (("Goal" :induct (new-ad-aux ads current-try)
           :in-theory (enable new-ad new-ad-aux))))



(defthm new-ad-aux-known
  (implies (and (not (set::in hole ads))
                (<= hole (new-ad-aux ads current-try))
                (<= current-try hole)
                (natp current-try)
                (natp hole))
           (equal (new-ad-aux ads current-try)
                  hole))
  :hints (("Goal" :in-theory (enable new-ad new-ad-aux))))

(defthm new-ad-known
  (implies (and (not (set::in hole ads))
                (<= hole (new-ad ads))
                (natp hole))
           (equal (new-ad ads)
                  hole))
  :hints (("Goal" :in-theory (enable new-ad new-ad-aux))))



(local (in-theory (disable SET::USE-WEAK-INSERT-INDUCTION)))



(defthm new-ad-aux-of-delete-irrel2
  (implies (and (< (new-ad-aux ads current-try) x)
                (natp x)
                (natp current-try))
           (equal (new-ad-aux (set::delete x ads) current-try)
                  (new-ad-aux ads current-try)))
  :hints (("Goal" :induct (new-ad-aux ads current-try)
           :expand ((NEW-AD-AUX (SET::DELETE X ADS)
                            CURRENT-TRY))
           :in-theory (enable new-ad new-ad-aux))))

(defthm new-ad-of-delete-irrel2
  (implies (and (< (new-ad ads) x)
                (natp x)
                (natp current-try))
           (equal (new-ad (set::delete x ads))
                  (new-ad ads)))
  :hints (("Goal" :in-theory (enable new-ad))))

(defthmd advance-current-try
  (implies (and (<= current-try (new-ad ads))
                (natp current-try))
           (equal (new-ad-aux ads current-try)
                  (new-ad-aux ads (new-ad-aux ads current-try))))
  :hints (("Goal" :in-theory (enable new-ad-aux))))

(defthmd advance-current-try2
  (equal (new-ad ads)
         (new-ad-aux ads (new-ad ads)))
  :hints (("Goal" :in-theory (enable new-ad-aux))))

(defthm new-ad-aux-of-insert-helper
  (implies (and (<= current-try (new-ad ads))
                (natp current-try))
           (equal (new-ad-aux (set::insert (new-ad ads) ads) (new-ad ads))
                  (new-ad-aux ads (+ 1 (new-ad ads)))))
  :hints (("Goal" :expand ((new-ad-aux (set::insert (new-ad ads) ads) (new-ad ads))))))



;; (DEFUN ind2 (ADS CURRENT-TRY CURRENT-TRY2)
;;   (DECLARE (XARGS :MEASURE (SET::CARDINALITY ADS)
;;                   :HINTS (("goal" :IN-THEORY (DISABLE)))))
;;   (IF (or (NOT (SET::IN CURRENT-TRY ADS))
;;           (NOT (SET::IN CURRENT-TRY2 ADS)))
;;       (list CURRENT-TRY current-try2)
;;       (ind2 (SET::DELETE CURRENT-TRY ADS)
;;             (+ 1 CURRENT-TRY)
;;             (+ 1 CURRENT-TRY2))))

;; (defthmd advance-current-try4
;;   (implies (and (<= current-try (new-ad ads))
;;                 (<= current-try2 (new-ad ads))
;;                 (< current-try current-try2)
;;                 (natp current-try)
;;                 (natp current-try2))
;;            (equal (new-ad-aux ads current-try)
;;                   (new-ad-aux ads current-try2)))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :do-not '(generalize eliminate-destructors fertilize)
;;            :induct (ind2 ads current-try current-try2)
;;            :do-not-induct t
;;            :in-theory (enable new-ad-aux))))

(defthmd advance-current-try3
  (implies (and (<= current-try (new-ad-aux ads lo))
                (<= lo current-try)
                (natp lo)
                (natp current-try))
           (equal (new-ad-aux ads current-try)
                  (new-ad-aux ads lo)))
  :hints (("subgoal *1/6" :cases ((equal lo current-try)))
          ("Goal"
           :do-not '(generalize eliminate-destructors fertilize)
;           :do-not-induct t
           :in-theory (enable new-ad-aux))))

(defthmd advance-current-try3-special
  (implies (and (<= current-try (new-ad-aux ads 0))
                (natp current-try))
           (equal (new-ad-aux ads current-try)
                  (new-ad-aux ads 0)))
  :hints (("Goal" :use (:instance advance-current-try3 (lo 0))
           :in-theory (disable advance-current-try3))))

(defthmd advance-current-try3-special-safe
  (implies (and (syntaxp (not (quotep current-try)))
                (<= current-try (new-ad-aux ads 0))
                (natp current-try))
           (equal (new-ad-aux ads current-try)
                  (new-ad-aux ads 0)))
  :hints (("Goal" :use (:instance advance-current-try3-special))))


(defthm new-ad-aux-of-insert-of-delete-irrel
  (implies (and (< x current-try)
                (natp x)
                (natp current-try))
           (equal (new-ad-aux (set::insert y (set::delete x ads)) current-try)
                  (new-ad-aux (set::insert y ads) current-try)))
  :hints (("Goal" :in-theory (e/d (set-insert-delete-strong) (set-delete-insert set::insert set::delete)))))


(defthm new-ad-aux-of-insert-bound
  (implies (and (natp ad)
                (natp current-try))
           (<= (new-ad-aux ads current-try)
               (new-ad-aux (set::insert ad ads) current-try)))
  :hints (("Goal" :in-theory (enable new-ad-aux)
           :induct t
           :expand ((new-ad-aux (set::insert ad ads)
                                current-try))
           )))

(defthm new-ad-aux-hole-bound
  (implies (and (not (set::in hole ads))
                (<= current-try hole)
                (natp hole)
                (natp current-try))
           (<= (new-ad-aux ads current-try)
               hole))
  :hints (("Goal"
           :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable new-ad-aux))))

(defthm new-ad-aux-mono-helper
  (implies (and ;(<= start start2)
                (natp start)
                (natp start2))
           (<= (new-ad-aux ads start)
               (new-ad-aux ads (+ start start2))))
  :hints (("Goal"
           :cases ((equal start2 0))
           :do-not '(generalize eliminate-destructors)
           :expand ((NEW-AD-AUX ads (+ START START2)))
           :in-theory (enable new-ad-aux))))

(defthm new-ad-aux-mono
  (implies (and (<= start start2)
                (natp start)
                (natp start2))
           (<= (new-ad-aux ads start)
               (new-ad-aux ads start2)))
:hints (("Goal" :use (:instance new-ad-aux-mono-helper (start2 (- start2 start)))
         :in-theory (disable new-ad-aux-mono-helper))))

(defthm new-ad-aux-<=-new-ad-aux-when-subset-gen
  (implies (and (set::subset ads ads2)
                (<= start start2)
                (natp start)
                (natp start2))
           (<= (new-ad-aux ads start)
               (new-ad-aux ads2 start2)))
  :hints (("Goal"  :do-not '(generalize eliminate-destructors)
           :use (:instance new-ad-aux-<=-new-ad-aux-when-subset)
           :in-theory (disable new-ad-aux-<=-new-ad-aux-when-subset))))

(defthm new-ad-aux-of-insert
  (implies (and (<= current-try (new-ad ads))
                (natp current-try))
           (equal (new-ad-aux (set::insert (new-ad ads) ads) current-try)
                  (new-ad-aux ads (+ 1 (new-ad ads)))))
  :hints (("Goal" :in-theory (e/d (new-ad) ( new-ad-aux-of-insert-helper new-ad-aux-of-insert-bound NEW-AD-AUX-<=-NEW-AD-AUX-WHEN-SUBSET))
           :use ((:instance new-ad-aux-of-insert-helper)
                 (:instance advance-current-try3 (ads (SET::INSERT (NEW-AD ADS) ADS))  (lo current-try) (current-try (NEW-AD ADS)))
;                 (:instance advance-current-try (ads (SET::INSERT (NEW-AD ADS) ADS))
                 (:instance new-ad-aux-of-insert-bound (ad (NEW-AD ADS)))
                 )))
  )

(defthm new-ad-aux-of-insert-of-new-ad-aux
  (implies (and (<= current-try (new-ad ads))
                (natp current-try))
           (equal (new-ad-aux (set::insert (new-ad-aux ads 0) ads) current-try)
                  (new-ad-aux ads (+ 1 (new-ad ads)))))
  :hints (("Goal" :use (:instance new-ad-aux-of-insert)
           :in-theory (e/d (new-ad) (new-ad-aux-of-insert)))))

(defthmd new-ad-of-insert-of-new-ad
  (equal (new-ad (set::insert (new-ad ads) ads))
         (new-ad-aux ads (+ 1 (new-ad ads))))
  :hints (("Goal" :use (:instance new-ad-aux-of-insert-of-new-ad-aux (current-try 0))
           :in-theory (e/d (new-ad)( new-ad-aux-of-insert-of-new-ad-aux)))))


;; (thm
;;  (implies (and (<= current-try (new-ad ads))
;;                (natp current-try))
;;           (equal (new-ad-aux (set::insert (new-ad ads) ads) current-try)
;;                  (new-ad-aux ads (+ 1 (new-ad-aux ads current-try)))))
;;  :otf-flg t
;;  :hints (("Subgoal *1/2" :cases ((equal current-try (NEW-AD ADS))))
;;          ("Goal" :do-not '(generalize eliminate-destructors)
;;           :induct t
;;           :expand ((NEW-AD-AUX (SET::INSERT CURRENT-TRY ADS)
;;                                CURRENT-TRY)
;;                    (NEW-AD-AUX (SET::INSERT (NEW-AD ADS) ADS)
;;                                CURRENT-TRY))
;;           :do-not-induct t
;;           :in-theory (enable new-ad-aux))))

(defthm n-new-ads2-aux-of-insert-new-ad
  (implies (and (<= current-try (new-ad ads))
                (natp n)
                (natp current-try))
           (equal (n-new-ads2-aux n current-try (set::insert (new-ad ads) ads))
                  (cdr (n-new-ads2-aux (+ 1 n) current-try ads))))
  :hints (
          ("Goal"                                               ;:cases ((zp n))
           :do-not '(generalize eliminate-destructors)
;           :do-not-induct t
           :expand ((N-NEW-ADS2-AUX (+ 1 N)
                            CURRENT-TRY ADS)
                    (N-NEW-ADS2-AUX N
                                (+ 1
                                   (NEW-AD-AUX (SET::INSERT (NEW-AD ADS) ADS)
                                               CURRENT-TRY))
                                ADS)
                    (N-NEW-ADS2-AUX N (+ 1 (NEW-AD-AUX ADS CURRENT-TRY))
                            ADS))
           :induct (n-new-ads2-aux n current-try (set::insert (new-ad ads) ads))
           :in-theory (e/d (new-ad advance-current-try3-special-safe)
                           ()))))

;this might be easier to reason about in some cases (e.g., when stuff has been inserted or unioned into the ads)
;; ;n should be 1 or greater (should we shift things to allow 0??)
;; (defund nth-new-ad (n ads)
;;   (if (or (zp n)
;;           (equal 1 n))
;;       (new-ad ads)
;;     (nth-new-ad (+ -1 n) (set::insert (new-ad ads) ads))))


(defthmd nth-new-ad2-collect
  (equal (new-ad (set::insert (new-ad ads) ads))
         (nth-new-ad2 2 ads))
  :hints (("Goal" :expand ((nth-new-ad2 2 ads)
                           (N-NEW-ADS2 2 ADS)
                           (N-NEW-ADS2-AUX 2 0 ADS)
                           (N-NEW-ADS2-AUX 1 (+ 1 (NEW-AD-AUX ADS 0))
                                          ADS)
                           (N-NEW-ADS2-AUX 1 (+ 1 (NEW-AD ADS))
                                          ADS)
                           )
           :use new-ad-of-insert-of-new-ad
           :in-theory (enable nth-new-ad2  new-ad-recollapse))))

(DEFUN N-NEW-ADS2-AUX-ind (N CURRENT-TRY ADS n2)
  (IF (ZP N)
      (list N CURRENT-TRY ADS n2)
      (LET ((AD (NEW-AD-AUX ADS CURRENT-TRY)))
           (N-NEW-ADS2-AUX-ind (+ -1 N)
                              (+ 1 AD)
                              ADS
                              (+ -1 n2)
                              ))))

(defthm nth-0-of-N-NEW-ADS2-AUX
  (implies (posp n)
           (equal (NTH 0 (N-NEW-ADS2-AUX n CURRENT-TRY ADS))
                  (NEW-AD-AUX ADS CURRENT-TRY)))
  :hints (("Goal" :expand ((N-NEW-ADS2-AUX n CURRENT-TRY ADS)))))

(defthmd nth-of-n-new-ads2-aux-longer-helper
  (implies (and (< n m)
                (natp n)
                (natp k)
                (natp m))
           (equal (nth n (n-new-ads2-aux (+ k m) current-try ads))
                  (nth n (n-new-ads2-aux m current-try ads))))
  :hints (("Goal" :induct (N-NEW-ADS2-AUX-ind m current-try ads n))))

(defthmd nth-of-n-new-ads2-aux-longer
  (implies (and (< n m)
                (natp n)
                (natp m)
                (natp m2)
                (<= m m2))
           (equal (nth n (n-new-ads2-aux m2 current-try ads))
                  (nth n (n-new-ads2-aux m current-try ads))))
  :hints (("Goal" :use ((:instance nth-of-n-new-ads2-aux-longer-helper (k (- m2 m))))
           :in-theory (disable nth-of-n-new-ads2-aux-longer-helper))))

(defthmd nth-of-n-new-ads2-aux-longer-special
  (implies (and (< (+ 1 n) m2) ;strict < avoids loops
                (natp n)
                (natp m2))
           (equal (nth n (n-new-ads2-aux m2 current-try ads))
                  (nth n (n-new-ads2-aux (+ 1 n) current-try ads))))
  :hints (("Goal" :use (:instance nth-of-n-new-ads2-aux-longer (m (+ 1 n))))))

(defthm equal-of-new-ad-aux-and-new-ads
  (equal (EQUAL (NEW-AD-AUX ADS 0) (NEW-AD ADS))
         t)
  :hints (("Goal" :in-theory (enable new-ad-recollapse))))

;introduces the old function
(defthmd recharacterize-nth-of-n-new-ads2-aux
  (implies (and (natp n)
                (<= m n)
                (posp m))
           (equal (nth (+ -1 m) (n-new-ads2-aux n 0 ads))
                  (nth-new-ad m ads)))
  :hints (("Subgoal *1/2" :cases ((equal m n)))
          ("Subgoal *1/1" :in-theory (enable equal-of-new-ad-aux-and-new-ads))
          ("Goal"
           :expand ( ;(NTH (+ -1 M) (N-NEW-ADS2-AUX N 0 ADS))
                    (N-NEW-ADS2-AUX N 0 ADS)
;                   (N-NEW-ADS2-AUX N (+ 1 (NEW-AD-AUX ADS 0)) ADS)
                    )
           :in-theory (e/d (nth-new-ad nth-of-n-new-ads2-aux-longer-special
                                       )
                           (NTH-NEW-AD-COLLECT; NTH-OF-CDR
                            equal-of-new-ad-aux-and-new-ads NTH-NEW-AD-OF-INSERT-NEW-AD)))))

(defthmd nth-of-n-new-ads2-aux-of-0
  (implies (and (natp n)
                (<= (+ 1 m) n)
                (natp m))
           (equal (nth m (n-new-ads2-aux n 0 ads))
                  (nth-new-ad (+ 1 m) ads)))
  :hints (("Goal" :use (:instance recharacterize-nth-of-n-new-ads2-aux
                                  (m (+ 1 m))))))


;expressed the new function in terms of the old one
(defthmd recharacterize-nth-of-n-new-ads2
  (implies (posp m)
           (equal (nth-new-ad2 m ads)
                  (nth-new-ad m ads)))
  :hints (("Goal" :in-theory (enable nth-new-ad2 n-new-ads2)
           :use (:instance recharacterize-nth-of-n-new-ads2-aux (n m)))))

(defthm NTH-NEW-AD-when-zp
  (IMPLIES (zp M)
           (EQUAL (NTH-NEW-AD M ADS)
                  (new-ad ads)))
  :hints (("Goal" :in-theory (e/d (NTH-NEW-AD) (NTH-NEW-AD-OF-INSERT-NEW-AD NTH-NEW-AD-COLLECT)))))

(defthm NTH-NEW-AD2-when-zp
  (IMPLIES (zp M)
           (EQUAL (NTH-NEW-AD2 M ADS)
                  (new-ad ads)))
  :hints (("Goal" :in-theory (e/d (NTH-NEW-AD2) ()))))

(defthmd recharacterize-nth-new-ad
  (equal (nth-new-ad m ads)
         (nth-new-ad2 m ads))
  :hints (("Goal" :cases ((posp m))
           :use (:instance recharacterize-nth-of-n-new-ads2))))


;; ;old version. nicer in some cases to reason about but less efficient.
;; ;BOZO write this using sets as above?  did we already abandon that idea?
;; ;returns a list
;; ;inefficient!
;; (defun n-new-ads-aux (n ads)
;;   (if (zp n)
;;       nil ;empty list
;;     (cons (nth-new-ad n ads)
;;           (n-new-ads-aux (+ -1 n) ads))))

;; ;returns a list
;; ;inefficient!
;; (defund n-new-ads (n ads)
;;   (reverse-list (n-new-ads-aux n ads)))

(defthm consp-of-N-NEW-ADS2-AUX
  (equal (CONSP (N-NEW-ADS2-AUX n current-try ADS))
         (not (zp n))))

(defthm len-of-n-new-ads-aux
  (implies (natp n)
           (equal (len (n-new-ads-aux n ads))
                  n)))

(defthm consp-of-n-new-ads-aux
  (equal (consp (n-new-ads-aux n ads))
         (and (integerp n)
              (< 0 n)))
  :hints (("Goal" :expand ((n-new-ads-aux 1 ads)))))

(defthm car-of-N-NEW-ADS2-AUX
  (implies (posp n)
           (equal (CAR (N-NEW-ADS2-AUX n current-try ADS))
                  (NEW-AD-AUX ADS current-try)))
  :hints (("Goal" :expand ((N-NEW-ADS2-AUX 1 CURRENT-TRY ADS))
           :in-theory (enable N-NEW-ADS2-AUX))))

(defthm take-of-N-NEW-ADS2-AUX
  (implies (and (<= m n)
                (natp m)
                (natp n))
           (equal (TAKE m (N-NEW-ADS2-AUX n current-try ADS))
                  (N-NEW-ADS2-AUX m current-try ADS))))

(defthm n-new-ads-aux-of-1
  (equal (n-new-ads-aux 1 ads)
         (list (nth-new-ad 1 ads)))
  :hints (("Goal" :expand (N-NEW-ADS-AUX 1 ADS)
           :in-theory (enable n-new-ads-aux))))

(local
 (defun n-new-ads-aux-n-induct (n1 ads n2)
   (if (zp n2)
       (list n1 ads n2)
     (n-new-ads-aux-n-induct (+ -1 n1) ads (+ -1 n2)))))

(defthm nth-of-n-new-ads-aux
  (implies (and (natp n1)
                (posp n2)
                (< n1 n2))
           (equal (nth n1 (n-new-ads-aux n2 ads))
                  (nth-new-ad (- n2 n1) ads)))
  :hints (("Goal" :induct (N-NEW-ADS-AUX-n-induct N1 ADS n2)
           :expand (N-NEW-ADS-AUX N2 ADS)
           :in-theory (e/d (N-NEW-ADS-AUX)
                           ( ;NTH-OF-CONS-SAFE
                            )))))

;; (defthm nth-of-n-new-ads2-aux
;;   (implies (and (natp n1)
;;                 (posp n2)
;;                 (< n1 n2)
;;                 (natp curr))
;;            (equal (nth n1 (n-new-ads2-aux n2 curr ads))
;;                   (+ 1 (nth-new-ad (+ curr n1) ads))))
;;   :hints (("Goal" ;:induct (N-NEW-ADS-AUX-n-induct N1 ADS n2)
;; ;           :expand (N-NEW-ADS-AUX N2 ADS)
;;            :in-theory (e/d (N-NEW-ADS2-AUX)
;;                            ( ;NTH-OF-CONS-SAFE
;;                             )))))


(defthmd n-new-ads-becomes-n-new-ads2-helper
  (implies (natp n)
           (equal (reverse-list (n-new-ads-aux n ads))
                  (n-new-ads2-aux n 0 ads)))
  :hints (("subgoal *1/4" ;; :expand ((N-NEW-ADS2-AUX (+ -1 N) 0 ADS)
                          ;;
           ;;          (N-NEW-ADS2 N ADS))
           :expand ((N-NEW-ADS-AUX N ADS)
                    (NTH-NEW-AD2 N ADS)
                    (N-NEW-ADS2 N ADS))
           :in-theory (e/d (recharacterize-nth-new-ad ;LIST::EQUAL-APPEND-REDUCTION!
                            equal-of-append
                            equal-of-cons
                            ) ( ;LIST::NTH-OF-CONS
                            N-NEW-ADS-AUX
                            ))
           )
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (    ;LIST::CAR-APPEND LIST::CDR-APPEND
                            ) ( ;N-NEW-ADS-AUX
                               ;;LIST::NTH-OF-CONS
                            )))))

(in-theory (disable N-NEW-ADS2-AUX N-NEW-ADS-aux))

(defthm N-NEW-ADS-AUX-when-zp
  (implies (zp n)
           (equal (N-NEW-ADS-AUX N ADS)
                  nil))
  :hints (("Goal" :in-theory (enable N-NEW-ADS-AUX))))

(defthm N-NEW-ADS2-AUX-when-zp
  (implies (zp n)
           (equal (N-NEW-ADS2-AUX N 0 ADS)
                  nil))
  :hints (("Goal" :in-theory (enable N-NEW-ADS2-AUX))))

;recharacterizes
(defthmd n-new-ads-becomes-n-new-ads2
  (equal (n-new-ads n ads)
         (n-new-ads2 n ads))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable n-new-ads n-new-ads2 N-NEW-ADS-BECOMES-N-NEW-ADS2-helper))))

;; zz

;; (defthm nth-new-ad2-of-insert-new-ad
;;   (implies (and (integerp n)
;;                 (< 0 n))
;;            (equal (nth-new-ad2 n (set::insert (new-ad ads) ads))
;;                   (nth-new-ad2 (+ 1 n) ads)))
;;   :hints (("Goal" :in-theory (enable nth-new-ad2))))



;; (defthm equal-nth-new-ad2-nil
;;   (equal (equal (nth-new-ad2 n ads) nil)
;;          nil))

;; (defthm equal-nth-new-ad2-nil2
;;   (equal (equal nil (nth-new-ad2 n ads))
;;          nil))





;; (defthm nth-new-ad2-not-in-ads
;;   (equal (set::in (nth-new-ad2 n ads) ads)
;;          nil)
;;   :hints (("Goal" :in-theory (enable nth-new-ad2))))




;; (defthm not-equal-nth-new-ad2-when-bound
;;   (implies (set::in x ads)
;;            (equal (equal x (nth-new-ad2 n ads))
;;                   nil)))

;; (defthm not-equal-nth-new-ad2-when-bound-alt
;;   (implies (set::in x ads)
;;            (equal (equal (nth-new-ad2 n ads) x)
;;                   nil)))

;; ;sort of lets us keep from deciding which we prefer
;; (defthm new-ad-equal-nth-new-ad2
;;   (equal (equal (new-ad ads) (nth-new-ad2 1 ads))
;;          t)
;;   :hints (("Goal" :in-theory (enable nth-new-ad2))))



;; (defthm nth-new-ad2-not-in-ads2
;;   (equal (set::in (nth-new-ad2 n ads) ads)
;;          nil))

;; ;strengthen?
;; (defthm new-ad-not-equal-nth-new-ad2
;;   (implies (and (integerp n)
;;                 (< 1 n))
;;            (not (equal (new-ad ads) (nth-new-ad2 n ads))))
;;   :hints (("Goal" :expand (nth-new-ad2 2 ads)
;;            :in-theory (e/d (nth-new-ad2) (nth-new-ad2-of-insert-new-ad NTH-NEW-AD2-COLLECT)))))



;; (defthm equal-nth-new-ad2-nth-new-ad2
;;   (implies (and (posp m)
;;                 (posp n))
;;            (equal (EQUAL (NTH-NEW-AD2 M ADS) (NTH-NEW-AD2 N ADS))
;;                   (equal n m)))
;;   :hints (("Goal" :in-theory (e/d (NTH-NEW-AD2) (NTH-NEW-AD2-OF-INSERT-NEW-AD)))))

;; (defthm not-memberp-nth-new-ad2-n-new-ads2
;;   (IMPLIES (AND (> m n)
;;                 (natp n)
;;                 (natp m)
;;                 )
;;            (equal (MEMBERP (NTH-NEW-AD2 m ADS)
;;                                (N-NEW-ADS2-AUX n ADS))
;;                   nil))
;;   :hints (("Goal" :in-theory (enable N-NEW-ADS2-AUX))))



;; (defthm unique-of-n-new-ads2
;;   (no-duplicatesp-equal (n-new-ads2 n ads))
;;   :hints (("Goal" :in-theory (enable n-new-ads2 no-duplicatesp-equal-of-cons))))





;; ;switch to use last-elem
;; (defthm car-last-of-n-new-ads2-aux
;;   (implies (not (zp n))
;;            (EQUAL (CAR (LAST (N-NEW-ADS2-AUX n ADS)))
;;                   (NEW-AD ADS)))
;;   :hints (("Goal" :in-theory (enable n-new-ads2-aux))))

;; ;dup
;; (defthm car-of-reverse-list
;;   (equal (car (reverse-list lst))
;;          (nth (+ -1 (len lst)) lst))
;;   :hints (("Goal" :in-theory (enable reverse-list))))


;; (defthm consp-of-N-NEW-ADS2-AUX
;;   (equal (consp (N-NEW-ADS2-AUX n ads))
;;          (and (integerp n)
;;               (< 0 n)))
;;   :hints (("Goal" :expand ((N-NEW-ADS2-AUX 1 ADS)))))

;; ;; (defthm n-new-ads2-2-recollect
;; ;;   (equal (set::insert (new-ad ads) (set::insert (nth-new-ad2 2 ads) ads))
;; ;;          (set::union (n-new-ads2 2 ads) ads))
;; ;;   :hints (("Goal" :expand ((n-new-ads2 1 ads)
;; ;;                            (n-new-ads2 2 ads))
;; ;;            :in-theory (enable n-new-ads2 nth-new-ad2))))

;; ;; (defthm n-new-ads2-2-recollect-two
;; ;;   (equal (set::insert (nth-new-ad2 1 ads) (set::insert (nth-new-ad2 2 ads) ads))
;; ;;          (set::union (n-new-ads2 2 ads) ads))
;; ;;   :hints (("Goal" :expand ((n-new-ads2 1 ads)
;; ;;                            (n-new-ads2 2 ads))
;; ;;            :in-theory (e/d (n-new-ads2 nth-new-ad2) (N-NEW-ADS2-2-RECOLLECT)))))

;; ;gross proof?
;; ;; (defthm insert-new-ad-hack
;; ;;   (implies (and (integerp n)
;; ;;                 (<= 0 n))
;; ;;            (equal (set::insert (new-ad ads) (n-new-ads2 n (set::insert (new-ad ads) ads)))
;; ;;                   (n-new-ads2 (+ 1 n) ads)))
;; ;;   :hints (("Goal" :in-theory (e/d (n-new-ads2) (SET::USE-WEAK-INSERT-INDUCTION)))))

;; ;; (defthm new-ad-of-union-with-n-new-ads2
;; ;;   (implies (and (integerp n)
;; ;;                 (< 0 n))
;; ;;            (equal (new-ad (set::union ads (n-new-ads2 (+ -1 n) ads)))
;; ;;                   (nth-new-ad2 n ads)))
;; ;;   :hints (("subgoal *1/4" :use (:instance insert-new-ad-hack (n (+ -2 n)))
;; ;;            :in-theory (disable insert-new-ad-hack))
;; ;;           ("Goal" :in-theory (enable nth-new-ad2
;; ;;                                      ;;n-new-ads2
;; ;;                                      ))))

;; ;; ;matches better
;; ;; (defthm new-ad-of-union-with-n-new-ads2-better
;; ;;   (implies (and (integerp n)
;; ;;                 (<= 0 n))
;; ;;            (equal (new-ad (set::union ads (n-new-ads2 n ads)))
;; ;;                   (nth-new-ad2 (+ 1 n) ads)))
;; ;;   :hints (("Goal" :use (:instance new-ad-of-union-with-n-new-ads2 (n (+ 1 n)))
;; ;;            :in-theory (disable new-ad-of-union-with-n-new-ads2)))
;; ;;   )


;; ;; (thm
;; ;;  (implies (and (integerp n) (< 0 n))
;; ;;           (equal (nth-new-ad2 1 (set::union ads (n-new-ads2 n ads)))
;; ;;                  (nth-new-ad2 (+ 1 n) ads)))
;; ;;  :hints (("Goal"
;; ;; ;          :expand (nth-new-ad2 (+ 1 n) ads)
;; ;; ;          :induct (ind-hint m n ads)
;; ;;           :do-not '(generalize eliminate-destructors)
;; ;;           :in-theory (e/d (nth-new-ad2
;; ;;                            n-new-ads2
;; ;;                            )
;; ;;                           (n-new-ads2-2-recollect-two n-new-ads2-2-recollect)))))

;; ;; (thm
;; ;;  (implies (and (integerp n) (< 0 n)
;; ;;                (integerp m) (< 0 m))
;; ;;           (equal (nth-new-ad2 m (set::union ads (n-new-ads2 n ads)))
;; ;;                  (nth-new-ad2 (+ m n) ads)))
;; ;;  :hints (("Goal"
;; ;; ;          :expand (nth-new-ad2 (+ 1 n) ads)
;; ;;           :induct (ind-hint m n ads)
;; ;;           :do-not '(generalize eliminate-destructors)
;; ;;           :in-theory (e/d (;nth-new-ad2
;; ;;                            n-new-ads2
;; ;;                            )
;; ;;                           (n-new-ads2-2-recollect-two n-new-ads2-2-recollect)))))

;; ;; (thm
;; ;;  (implies (and (integerp n)
;; ;;                (< 0 n))
;; ;;           (equal (new-ad (set::union ads (n-new-ads2 n ads)))
;; ;;                  (nth-new-ad2 (+ 1 n) ads)))
;; ;;  :hints (("Goal"
;; ;;           :expand (nth-new-ad2 (+ 1 n) ads)
;; ;;           :in-theory (e/d (nth-new-ad2
;; ;; ;n-new-ads2
;; ;;                            )
;; ;;                           (N-NEW-ADS2-2-RECOLLECT-TWO N-NEW-ADS2-2-RECOLLECT)))))

;; ;; (defthm n-new-ads2-recollect-3
;; ;;   (equal (set::insert (nth-new-ad2 2 ads) (set::insert (new-ad ads) ads))
;; ;;          (set::union (n-new-ads2 2 ads) ads))
;; ;;   :hints (("Goal" :expand ((n-new-ads2 1 ads)
;; ;;                            (n-new-ads2 2 ads))
;; ;;            :in-theory (e/d (n-new-ads2 nth-new-ad2) (n-new-ads2-2-recollect)))))

;; ;; (defthm new-ads-recollect
;; ;;   (implies (and (equal m (+ 1 n))
;; ;;                 (integerp n)
;; ;;                 (integerp m)
;; ;;                 (< 0 m))
;; ;;            (equal (SET::INSERT (NTH-NEW-AD2 m ads) (SET::UNION ads (N-NEW-ADS2 n ads)))
;; ;;                   (set::union ads (N-NEW-ADS2 m ads))))
;; ;;   :hints (("Goal" :in-theory (enable n-new-ads2))))

;; ;; (defthm new-ads-recollect-alt
;; ;;   (implies (and (equal m (+ 1 n))
;; ;;                 (integerp n)
;; ;;                 (integerp m)
;; ;;                 (< 0 m))
;; ;;            (equal (SET::INSERT (NTH-NEW-AD2 m ads) (SET::UNION (N-NEW-ADS2 n ads) ads))
;; ;;                   (set::union ads (N-NEW-ADS2 m ads))))
;; ;;   :hints (("Goal" :use (:instance new-ads-recollect)
;; ;;            :in-theory (disable new-ads-recollect))))

;; ;; (defthm not-in-n-new-ads2
;; ;;   (implies (set::in ad ads)
;; ;;            (not (set::in ad (n-new-ads2 n ads))))
;; ;;   :hints (("Goal" :in-theory (enable n-new-ads2))))

;; (defthm not-memberp-n-new-ads2
;;   (implies (set::in ad ads)
;;            (equal (memberp ad (n-new-ads2 n ads))
;;                   nil))
;;   :hints (("Goal" :in-theory (enable n-new-ads2))))

;; (defthm nth-of-n-new-ads2
;;   (implies (and (natp n) (natp m) (< n m) (<= 0 n))
;;            (equal (nth n (n-new-ads2 m ads))
;;                   (nth-new-ad2 (+ 1 n) ads)))
;;   :hints (("Goal" :in-theory (enable n-new-ads2))))

;; (theory-invariant (incompatible (:definition nth-new-ad2) (:rewrite NTH-NEW-AD2-OF-INSERT-NEW-AD)))

;; (defthm car-of-n-new-ads2
;;   (implies (and (natp n)
;;                 (< 0 n))
;;            (equal (car (n-new-ads2 n ads))
;;                   (new-ad ads)))
;;   :hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0) ()))))

;; (defthmd cons-new-ad-and-2nd-ad
;;    (equal (cons (new-ad ads) (cons (nth-new-ad2 '2 ads) lst))
;;           (append (n-new-ads2 2 ads) lst))
;;    :hints (("Goal" :in-theory (disable nth-new-ad2-of-insert-new-ad NTH-NEW-AD2-COLLECT)
;;             :expand ((n-new-ads2 2 ads)
;;                      (n-new-ads2-aux 2 ads)
;;                      (n-new-ads2-aux 1 ads)
;;                      (nth-new-ad2 2 ads))))
;;    :otf-flg t)

;; ;; (defthmd n-new-ads2-expand-constant
;; ;;   (implies (and (syntaxp (quotep n))
;; ;;                 (not (zp n)))
;; ;;            (equal (n-new-ads2 n ads)
;; ;;                   (cons (nth-new-ad2 n ads)
;; ;;                         (n-new-ads2 (+ -1 n) ads))))
;; ;;   :hints (("Goal" :in-theory (enable n-new-ads2))))


;; (defthm nth-new-ad2-not-equal-nth-new-ad2
;;   (implies (and (integerp m)
;;                 (integerp n)
;;                 (< 0 n)
;;                 (< 0 m)
;;                 (not (equal m n))
;;                 )
;;            (equal (EQUAL (NTH-NEW-AD2 m ADS) (NTH-NEW-AD2 n ADS))
;;                   nil))
;;   :hints (("Goal" :in-theory (e/d (nth-new-ad2) (NTH-NEW-AD2-OF-INSERT-NEW-AD)))))


;; (defthm n-new-ads2-aux-hack
;;   (implies (not (zp n))
;;            (not (equal (n-new-ads2-aux n (set::insert (new-ad ads) ads))
;;                        (n-new-ads2-aux n ads)))))

;; (defthm n-new-ads2-of-insert-new-ad
;;  (implies (and (natp n)
;; ;               (< 1 n)
;;                )
;;           (equal (n-new-ads2 n (set::insert (new-ad ads) ads))
;;                  (new-ads-slice 2 (+ 1 n) ads)))
;;  :hints (("Subgoal *1/4" :in-theory (enable LIST::CDR-APPEND)) ;yuck
;;          ("Goal" ;:cases ((zp n))
;;           :do-not '(generalize eliminate-destructors)
;;           :in-theory (enable n-new-ads2 ;LIST::CDR-APPEND
;;                              ;LIST::CDR-APPEND
;;                              ))))

;; (defthm cdr-of-n-new-ads2
;;   (implies (not (zp n))
;;            (equal (cdr (n-new-ads2 n ads))
;;                   (new-ads-slice 2 n ads)))
;;   :hints (("Goal" :in-theory (enable new-ads-slice))))

;; (in-theory (disable new-ads-slice))

;; (defthm new-ad-not-memberp-of-new-ads-slice ;new-ads-not-memberp-of-new-ads-slice
;;  (implies (and (< 1 start)
;;          ;      (natp n)
;;                (natp start))
;;           (equal (memberp (NEW-AD ads)
;;                               (NEW-ADS-SLICE start end ads))
;;                  nil))
;;  :hints (("Goal" :in-theory (enable new-ads-slice N-NEW-ADS2))))


;; (defthm len-of-new-ads-slice
;;   (implies (and (<= start end)
;;                 (natp start)
;;                 (< 0 start)
;;                 (natp end))
;;            (equal (len (new-ads-slice start end ads))
;;                   (+ 1 end (- start))))
;;   :hints (("Goal" :in-theory (enable new-ads-slice))))

;; (defthm unique-of-new-ads-slice
;;   (no-duplicatesp-equal (new-ads-slice start end ads))
;;   :hints (("Goal" :in-theory (enable new-ads-slice))))



;; (defthm not-memberp-of-new-ads-slice
;;   (implies (set::in ad ads)
;;            (equal (memberp ad (new-ads-slice start end ads))
;;                   nil))
;;   :hints (("Goal" :in-theory (enable new-ads-slice))))

;; (defthm nth-of-new-ads-slice
;;   (implies (and (natp n)
;;                 (<= n (- end start))
;;                 (<= start end)
;;                 (natp start)
;;                 (< 0 start)
;;                 (natp end))
;;            (equal (nth n (new-ads-slice start end ads))
;;                   (nth-new-ad2 (+ n start) ads)))
;;   :hints (("Goal" :in-theory (enable new-ads-slice))))

;; (defthm memberp-of-nth-new-ad2-and-new-ads-slice
;;   (implies (and (natp n)
;;                 (< 0 n)
;;                 (natp start)
;;                 (natp end)
;;                 (<= start n)
;;                 (<= n end))
;;            (equal (memberp (nth-new-ad2 n ads) (new-ads-slice start end ads))
;;                   t))
;;   :hints (("Goal" :in-theory (enable new-ads-slice N-NEW-ADS2))))

;; (defthm new-ad-not-memberp-of-new-ads
;;   (implies (and (natp start)
;;                 (< 1 start))
;;            (equal (memberp (new-ad ads) (new-ads-slice start end ads))
;;                   nil))
;;   :hints (("Goal" :in-theory (enable new-ads-slice n-new-ads2))))

;; (defthm new-ads-slice-iff
;;   (implies (and (natp start)
;;                 (natp end)
;;                 (<= 1 start))
;;            (iff (new-ads-slice start end ads)
;;                 (<= start end)))
;;   :hints (("Goal" :in-theory (enable new-ads-slice n-new-ads2))))

;; (defthm new-ads-type
;;   (implies (and (natp start)
;;                 (natp end)
;;                 (<= 1 start)
;;                 (<= start end))
;;            (consp (new-ads-slice start end ads)))
;;   :rule-classes (:rewrite :type-prescription)
;;   :hints (("Goal" :in-theory (enable new-ads-slice n-new-ads2))))

;; (defthmd new-ads-slice-recollect-1
;;   (implies (and (natp m)
;;                 (< 0 m)
;;                 (natp n)
;;                 (equal n (+ 1 m)))
;;            (equal (cons (nth-new-ad2 m ads) (cons (nth-new-ad2 n ads) nil))
;;                   (new-ads-slice m n ads)))
;;   :hints (("Goal" :in-theory (enable new-ads-slice  ;bozo compare to JVM::CONS-EQUAL-REWRITE
;;                                      ))))

;; (defthmd new-ads-slice-recollect-2
;;   (implies (and (natp m)
;;                 (< 0 m)
;;                 (natp n)
;;                 (equal n (+ 1 m)))
;;            (equal (cons (nth-new-ad2 m ads) (cons (nth-new-ad2 n ads) lst))
;;                   (append (new-ads-slice m n ads) lst)))
;;   :hints (("Goal" :in-theory (enable new-ads-slice))))

;; (defthm new-ads-slice-out-of-order-indices
;;   (implies (and (< n m)
;;                 (natp n)
;;                 (natp m))
;;            (equal (new-ads-slice m n ads)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable new-ads-slice))))

;; ;disable?!
;; (defthm new-ads-slice-opener
;;   (implies (and (natp m)
;;                 (< 0 m)
;;                 (natp n)
;;                 (<= m n))
;;            (equal (NEW-ADS-SLICE m n ads)
;;                   (cons (nth-new-ad2 m ads) (NEW-ADS-SLICE (+ 1 m) n ads))))
;;   :hints (("Goal" :in-theory (enable new-ads-slice ;equal-cons-cases2
;;                                      ))))

;; (defthm memberp-of-new-ad-cons-nth-new-ad2
;;  (implies (and (natp n)
;;                (< 0 n)
;;                (not (equal 1 n)))
;;           (equal (MEMBERP (NEW-AD ads) (CONS (NTH-NEW-AD2 n ads) lst))
;;                  (MEMBERP (NEW-AD ads) lst))))

;; (defthm n-new-ads2-iff
;;   (iff (n-new-ads2 n ads)
;;        (not (zp n)))
;;   :hints (("Goal" :in-theory (enable n-new-ads2))))

;; (encapsulate
;;  ()
;;  (local (defthm fw
;;           (IMPLIES (AND (NATP NUM)
;;                         (< 0 N)
;;                         (NATP N)
;;                         (NOT (MEMBERP (NTH-NEW-AD2 N ADS)
;;                                             (N-NEW-ADS2-AUX NUM ADS))))
;;                    (< NUM N))
;;           :hints (("Goal" :in-theory (disable ;CANCEL-<-+
;;                                       ))) ;bozo why?
;;           ))

;;  (defthm memberp-nth-new-ad2-n-new-ads2
;;    (implies (and (natp num)
;;                  (< 0 n)
;;                  (natp n))
;;             (equal (MEMBERP (NTH-NEW-AD2 n ads) (N-NEW-ADS2 num ads))
;;                    (<= n num)))
;;    :hints (("Goal" :in-theory (enable n-new-ads2 N-NEW-ADS2-AUX)))))

;; ;; ;bozo gross hack
;; ;; (skip -proofs
;; ;; (defthm 5-new-ads-recollapse
;; ;;  (equal (CONS (NEW-AD (RKEYS (JVM::HEAP S0)))
;; ;;            (CONS (NTH-NEW-AD2 '2 (RKEYS (JVM::HEAP S0)))
;; ;;                  (CONS (NTH-NEW-AD2 '3 (RKEYS (JVM::HEAP S0)))
;; ;;                        (CONS (NTH-NEW-AD2 '4 (RKEYS (JVM::HEAP S0)))
;; ;;                              (CONS (NTH-NEW-AD2 '5 (RKEYS (JVM::HEAP S0)))
;; ;;                                    'NIL)))))
;; ;;         (n-new-ads2 5 (RKEYS (JVM::HEAP S0)))))
;; ;; )



;; ;yuck?
;; ;gen?
;; (defthm new-ad-<<-nth-new-ad2-2
;;   (<< (NEW-AD ADS) (NTH-NEW-AD2 2 ADS))
;;   :hints (("Goal" :expand ((NTH-NEW-AD2 2 ADS))
;;            :in-theory (e/d (<< LEXORDER ALPHORDER) (NTH-NEW-AD2-OF-INSERT-NEW-AD
;;                                                     NTH-NEW-AD2-COLLECT ;bozo
;;                                                     )))))
;; ;yuck?
;;  ;bad rule?
;; (defthmd list-new-ad-nth-new-ad2-2
;;   (equal (LIST (NEW-AD ADS) (NTH-NEW-AD2 2 ADS))
;;          (set::insert (NEW-AD ADS) (set::insert (NTH-NEW-AD2 2 ADS) nil)))
;;   :hints (("Goal" :expand ((set::insert (NEW-AD ADS) (set::insert (NTH-NEW-AD2 2 ADS) nil))
;;                            ))))

;; ;; (thm
;; ;;  (<= (NEW-AD ADS)
;; ;;      (NEW-AD (SET::INSERT (NEW-AD ADS) ADS))))

;; (defthm consp-of-new-ads-slice
;;   (implies (and (posp start)
;;                 (posp end))
;;            (equal (consp (new-ads-slice start end ads))
;;                   (<= start end)))
;;   :hints (("Goal" :in-theory (enable new-ads-slice))))

;; (defthm car-of-new-ads-slice
;;   (implies (and (<= 0 (- end start))
;;                 (<= start end)
;;                 (natp start)
;;                 (< 0 start)
;;                 (natp end))
;;            (equal (car (new-ads-slice start end ads))
;;                   (nth-new-ad2 start ads)))
;;   :hints (("Goal" :in-theory (enable new-ads-slice))))

;; (defthm cdr-of-new-ads-slice
;;   (implies (and (<= 0 (- end start))
;;                 (<= start end)
;;                 (natp start)
;;                 (< 0 start)
;;                 (natp end))
;;            (equal (cdr (new-ads-slice start end ads))
;;                   (new-ads-slice (+ 1 start) end ads)))
;;   :hints (("Goal" :in-theory (enable new-ads-slice))))
