;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "utilities")
(include-book "total-order")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; BOZO move to utilities

(defthm mapp-of-rev
  (equal (mapp (rev x))
         (mapp x))
  :hints(("Goal" :induct (cdr-induction x))))



;; We now introduce a simple mergesort.
;;
;; We split the list by walking down it in a funny way; see halve-list.
;; Initially, mid and x both point to the front of the list.  We walk down x
;; taking two steps for every one step we take for mid; hence mid stays at the
;; middle of the list.  As we traverse mid, we puts its members into acc, and
;; when x runs out we return both acc and the rest of mid.  This effectively
;; lets us split the list in two (1) without doing any arithmetic, which can be
;; expensive since we can't use fixnum declarations, and (2) while consing only
;; (1/2)n times, where n is the length of the list.  This splitting function
;; performs well, handily beating SETS::split-list from the ordered sets books
;; on a large list of symbols we used to test it.

(defund halve-list-aux (mid x acc)
  (declare (xargs :guard t))
  (if (and (consp x)
           (consp (cdr x)))
      (halve-list-aux (cdr mid)
                      (cdr (cdr x))
                      (cons (car mid) acc))
    (cons acc mid)))

(definlined halve-list (x)
  (declare (xargs :guard t))
  (halve-list-aux x x nil))

(defthm halve-list-aux-when-not-consp
  (implies (not (consp x))
           (equal (halve-list-aux mid x acc)
                  (cons acc mid)))
  :hints(("Goal" :in-theory (enable halve-list-aux))))

(defthm halve-list-aux-when-not-consp-of-cdr
  (implies (not (consp (cdr x)))
           (equal (halve-list-aux mid x acc)
                  (cons acc mid)))
  :hints(("Goal" :in-theory (enable halve-list-aux))))


(defthm halve-list-aux-append-property
  (implies (<= (len x) (len mid))
           (equal (app (rev (car (halve-list-aux mid x acc)))
                       (cdr (halve-list-aux mid x acc)))
                  (app (rev acc)
                       mid)))
  :hints(("Goal" :in-theory (enable halve-list-aux))))

(defthm halve-list-aux-len-1
  (implies (and (<= (len x) (len mid))
                (consp x)
                (consp (cdr x)))
           (< (len (car (halve-list-aux mid x acc)))
              (+ (len mid) (len acc))))
  :hints(("Goal" :in-theory (enable halve-list-aux))))

(defthm halve-list-aux-len-2
  (implies (and (<= (len x) (len mid))
                (consp x)
                (consp (cdr x)))
           (< (len (cdr (halve-list-aux mid x acc)))
              (len mid)))
  :hints(("Goal" :in-theory (enable halve-list-aux))))

(defthm halve-list-correct
  (equal (app (rev (car (halve-list x)))
              (cdr (halve-list x)))
         (list-fix x))
  :hints(("Goal" :in-theory (enable halve-list))))

(defthm halve-list-len-1
  (implies (and (consp x)
                (consp (cdr x)))
           (< (len (car (halve-list x)))
              (len x)))
  :hints(("Goal"
          :in-theory (e/d (halve-list)
                          (halve-list-aux-len-1))
          :use ((:instance halve-list-aux-len-1
                           (mid x) (x x) (acc nil))))))

(defthm halve-list-len-2
  (implies (and (consp x)
                (consp (cdr x)))
           (< (len (cdr (halve-list x)))
              (len x)))
  :hints(("Goal" :in-theory (enable halve-list))))

(defthm halve-list-membership-property
  (equal (memberp a x)
         (or (memberp a (car (halve-list x)))
             (memberp a (cdr (halve-list x)))))
  :rule-classes nil
  :hints(("Goal"
          :in-theory (disable memberp-of-app)
          :use ((:instance memberp-of-app
                           (x (rev (car (halve-list x))))
                           (y (cdr (halve-list x))))))))

(defthm halve-list-lookup-property
  (equal (lookup a x)
         (or (lookup a (rev (car (halve-list x))))
             (lookup a (cdr (halve-list x)))))
  :rule-classes nil
  :hints(("Goal"
          :in-theory (disable lookup-of-app)
          :use ((:instance lookup-of-app
                           (x (rev (car (halve-list x))))
                           (y (cdr (halve-list x))))))))

(defthm mapp-of-first-of-halve-list-aux-1
  (implies (and (<= (len x) (len mid))
                (mapp mid)
                (mapp acc))
           (equal (mapp (car (halve-list-aux mid x acc)))
                  t))
  :hints(("Goal"
          :in-theory (enable halve-list-aux)
          :induct (halve-list-aux mid x acc))))

(defthm mapp-of-first-of-halve-list-aux-2
  (implies (and (mapp x)
                (mapp mid))
           (equal (mapp (cdr (halve-list-aux mid x acc)))
                  t))
  :hints(("Goal"
          :in-theory (enable halve-list-aux)
          :induct (halve-list-aux mid x acc))))

(defthm mapp-of-first-of-halve-list-1
  (implies (mapp x)
           (equal (mapp (car (halve-list x)))
                  t))
  :hints(("Goal" :in-theory (enable halve-list))))

(defthm mapp-of-first-of-halve-list-2
  (implies (mapp x)
           (equal (mapp (cdr (halve-list x)))
                  t))
  :hints(("Goal" :in-theory (enable halve-list))))




;; Our merging operation is quite conventional.  We have decided to eat
;; like-elements rather than preserving duplicity, so that mergesort always
;; produces a list with unique members.  Accordingly, our notion of ordered
;; lists requires (first x) << (second x) << (third x) << ..., which in turn
;; means that any ordered list is a unique list.

(defund ordered-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (consp (cdr x))
          (and (<< (first x) (second x))
               (ordered-listp (cdr x)))
        t)
    t))

(defthm ordered-listp-when-not-consp
  (implies (not (consp x))
           (equal (ordered-listp x)
                  t))
  :hints(("Goal" :in-theory (enable ordered-listp))))

(defthm ordered-listp-when-not-consp-of-cdr
  (implies (not (consp (cdr x)))
           (equal (ordered-listp x)
                  t))
  :hints(("Goal" :in-theory (enable ordered-listp))))

(defthm ordered-listp-of-cons
  (equal (ordered-listp (cons a x))
         (if (consp x)
             (and (<< a (car x))
                  (ordered-listp x))
           t))
  :hints(("Goal" :in-theory (enable ordered-listp))))

(defthm booleanp-of-ordered-listp
  (equal (booleanp (ordered-listp x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd lemma-for-uniquep-when-ordered-listp
  (implies (and (<< a (first x))
                (ordered-listp x))
           (equal (memberp a x)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd uniquep-when-ordered-listp
  (implies (ordered-listp x)
           (uniquep x))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable lemma-for-uniquep-when-ordered-listp))))




(defund merge-lists (x y)
  (declare (xargs :guard (and (ordered-listp x)
                              (ordered-listp y))
                  :measure (+ (len x) (len y))))
  (if (consp x)
      (if (consp y)
          (if (<< (car x) (car y))
              (cons (car x) (merge-lists (cdr x) y))
            (if (equal (car x) (car y))
                (cons (car x) (merge-lists (cdr x) (cdr y)))
              (cons (car y) (merge-lists x (cdr y)))))
        x)
    y))

(defthm merge-lists-when-not-consp-left
  (implies (not (consp x))
           (equal (merge-lists x y)
                  y))
  :hints(("Goal" :in-theory (enable merge-lists))))

(defthm merge-lists-when-not-consp-right
  (implies (not (consp y))
           (equal (merge-lists x y)
                  (if (consp x)
                      x
                    y)))
  :hints(("Goal" :in-theory (enable merge-lists))))

(defthm merge-lists-of-cons-and-cons
  (equal (merge-lists (cons a x) (cons b y))
         (if (<< a b)
             (cons a (merge-lists x (cons b y)))
           (if (equal a b)
               (cons a (merge-lists x y))
             (cons b (merge-lists (cons a x) y)))))
  :hints(("Goal" :in-theory (enable merge-lists))))

(defthm consp-of-merge-lists
  (equal (consp (merge-lists x y))
         (or (consp x)
             (consp y)))
  :hints(("Goal" :in-theory (enable merge-lists))))

(defthm smaller-than-merge-lists
  (implies (and (<< a (car x))
                (<< a (car y)))
           (<< a (car (merge-lists x y))))
  :hints(("Goal" :in-theory (enable merge-lists))))

(defthm ordered-listp-of-merge-lists
  (implies (and (ordered-listp x)
                (ordered-listp y))
           (ordered-listp (merge-lists x y)))
  :hints(("Goal"
          :induct (merge-lists x y)
          :in-theory (enable merge-lists))))

(defthm memberp-of-merge-lists
  (equal (memberp a (merge-lists x y))
         (or (memberp a x)
             (memberp a y)))
  :hints(("Goal" :in-theory (enable merge-lists))))



;; Our mergesort seems to be perform pretty well.  It is faster than ACL2's
;; SETS::mergesort in an experiment involving a long list of symbols; taking
;; only 2.26 seconds and 308 MB of memory instead of 3.60 seconds and 584 MB.
;; It also slightly beat ACL2::<<-sort (from books/defsort/uniquep) on time,
;; 2.26 seconds versus 2.8 seconds, but ACL2::<<-sort seemed to use only about
;; half the memory.  I'm not sure what trick it's using to accomplish that.

(defund mergesort (x)
  (declare (xargs :guard t
                  :measure (len x)
                  :verify-guards nil))
  (cond ((not (consp x))
         nil)
        ((not (consp (cdr x)))
         (list (car x)))
        (t
         (let ((split (halve-list x)))
           (merge-lists (mergesort (car split))
                        (mergesort (cdr split)))))))

(defthm mergesort-when-not-consp
  (implies (not (consp x))
           (equal (mergesort x)
                  nil))
  :hints(("Goal" :in-theory (enable mergesort))))

(defthm mergesort-when-not-consp-of-cdr
  (implies (and (not (consp (cdr x)))
                (consp x))
           (equal (mergesort x)
                  (list (car x))))
  :hints(("Goal" :in-theory (enable mergesort))))

(defthm ordered-listp-of-mergesort
  (equal (ordered-listp (mergesort x))
         t)
  :hints(("Goal" :in-theory (enable mergesort))))

(verify-guards mergesort)

(defthm uniquep-of-mergesort
  (equal (uniquep (mergesort x))
         t)
  :hints(("Goal" :in-theory (enable uniquep-when-ordered-listp))))



(defthmd lemma-for-memberp-of-mergesort
  (implies (and (NOT (MEMBERP A (CAR (HALVE-LIST X))))
                (NOT (MEMBERP A (CDR (HALVE-LIST X)))))
           (not (MEMBERP A X)))
  :hints(("Goal" :use ((:instance halve-list-membership-property)))))

(defthmd lemma-2-for-memberp-of-mergesort
  (implies (or (MEMBERP A (CAR (HALVE-LIST X)))
               (MEMBERP A (CDR (HALVE-LIST X))))
           (MEMBERP A X))
  :hints(("Goal" :use ((:instance halve-list-membership-property)))))

(defthm memberp-of-mergesort
  (equal (memberp a (mergesort x))
         (memberp a x))
  :hints(("Goal"
          :induct (mergesort x)
          :in-theory (enable mergesort
                             lemma-for-memberp-of-mergesort
                             lemma-2-for-memberp-of-mergesort))))

(defthm subsetp-of-mergesort-left
  (equal (subsetp (mergesort x) y)
         (subsetp x y))
  :hints(("Goal"
          :use ((:instance subsetp-badguy-membership-property
                           (x (mergesort x))
                           (y y))
                (:instance subsetp-badguy-membership-property
                           (x x)
                           (y y))))))

(defthm subsetp-of-mergesort-right
  (equal (subsetp x (mergesort y))
         (subsetp x y))
  :hints(("Goal"
          :use ((:instance subsetp-badguy-membership-property
                           (x x)
                           (y (mergesort y)))))))



;; An important application of mergesort is to implement an O(n log_2 n) subset
;; check for use on long lists.  We introducing a linear subset check which can
;; be used in place of subsetp when both lists are ordered.  We considered
;; implementing a "fast-subsetp" function that would automatically determine
;; whether it seemed like mergesorting would likely be useful or not, but in
;; the end we decided that the criteria for this choice was fairly complex and
;; we would rather just have the caller figure out which one they thing is
;; appropriate.

(defund ordered-list-subsetp (x y)
  (declare (xargs :guard (and (ordered-listp x)
                              (ordered-listp y))))
  (if (consp x)
      (if (consp y)
          (if (equal (car x) (car y))
              (ordered-list-subsetp (cdr x) (cdr y))
            (ordered-list-subsetp x (cdr y)))
        nil)
    t))

(defthm booleanp-of-ordered-list-subsetp
  (equal (booleanp (ordered-list-subsetp x y))
         t)
  :hints(("Goal" :in-theory (enable ordered-list-subsetp))))


(defthmd lemma-1-for-ordered-list-subsetp-property
  (implies (and (not (equal a (first y)))
                (not (consp (cdr y))))
           (equal (memberp a y)
                  nil)))

(defthmd lemma-2-for-ordered-list-subsetp-property
  (implies (and (not (equal (first x) (first y)))
                (not (consp (cdr y))))
           (equal (subsetp x y)
                  (not (consp x)))))

(defthmd lemma-3-for-ordered-list-subsetp-property
  (implies (and (not (equal (first x) (first y)))
                (subsetp x y)
                (ordered-listp x)
                (ordered-listp y))
           (equal (subsetp x (cdr y))
                  t))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable lemma-2-for-ordered-list-subsetp-property
                             lemma-for-uniquep-when-ordered-listp
                             ))))

(defthmd lemma-4-for-ordered-list-subsetp-property
  (implies (and (equal (first x) (first y))
                (subsetp x y)
                (ordered-listp x)
                (ordered-listp y))
           (equal (subsetp (cdr x) (cdr y))
                  t))
  :hints(("Goal"
          :in-theory (enable (:induction ordered-listp)
                             lemma-1-for-ordered-list-subsetp-property
                             lemma-2-for-ordered-list-subsetp-property
                             lemma-3-for-ordered-list-subsetp-property))))

(defthm ordered-list-subsetp-property
  (implies (and (force (ordered-listp x))
                (force (ordered-listp y)))
           (equal (ordered-list-subsetp x y)
                  (subsetp x y)))
  :hints(("Goal"
          :in-theory (enable ordered-list-subsetp
                             lemma-1-for-ordered-list-subsetp-property
                             lemma-2-for-ordered-list-subsetp-property
                             lemma-3-for-ordered-list-subsetp-property
                             lemma-4-for-ordered-list-subsetp-property)
          :induct (ordered-list-subsetp x y))))



;; We would now also like to develop a faster submapp check for times when we
;; are dealing with large maps.  Here, we have a problem with simply using
;; mergesort.  In particular, so-called "hidden pairs" in the map might be
;; smaller in the term order than the "visible pairs" in front of them.  For
;; example, consider (mergesort '((a . 3) (a . 2))).
;;
;; We begin by developing mergesort-map, which simultaneously removes any
;; shadowed pairs and leaves the map sorted by its keys.  This is basically the
;; same as the mergesort above, except that our merging function only inspects
;; the keys.

(defund ordered-mapp (x)
  (declare (xargs :guard (mapp x)))
  (if (consp x)
      (if (consp (cdr x))
          (and (<< (car (first x))
                   (car (second x)))
               (ordered-mapp (cdr x)))
        t)
    t))

(defthm ordered-mapp-when-not-consp
  (implies (not (consp x))
           (equal (ordered-mapp x)
                  t))
  :hints(("Goal" :in-theory (enable ordered-mapp))))

(defthm ordered-mapp-when-not-consp-of-cdr
  (implies (not (consp (cdr x)))
           (equal (ordered-mapp x)
                  t))
  :hints(("Goal" :in-theory (enable ordered-mapp))))

(defthm ordered-mapp-of-cons
  (equal (ordered-mapp (cons a x))
         (if (consp x)
             (and (<< (car a) (car (first x)))
                  (ordered-mapp x))
           t))
  :hints(("Goal" :in-theory (enable ordered-mapp))))

(defthm booleanp-of-ordered-mapp
  (equal (booleanp (ordered-mapp x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm ordered-mapp-of-cdr-when-ordered-mapp
  (implies (ordered-mapp x)
           (ordered-mapp (cdr x))))

(defthmd lemma-for-uniquep-when-ordered-mapp
  (implies (and (<< a (car (first x)))
                (ordered-mapp x))
           (equal (lookup a x)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm uniquep-of-domain-when-ordered-mapp
  (implies (ordered-mapp x)
           (equal (uniquep (domain x))
                  t))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable lemma-for-uniquep-when-ordered-mapp))))




(defund merge-maps (x y)
  (declare (xargs :guard (and (mapp x)
                              (mapp y)
                              (ordered-mapp x)
                              (ordered-mapp y))
                  :measure (+ (len x) (len y))
                  :verify-guards nil))
  (if (consp x)
      (if (consp y)
          (if (<< (car (first x)) (car (first y)))
              (cons (first x) (merge-maps (cdr x) y))
            (if (equal (car (first x)) (car (first y)))
                (cons (first x) (merge-maps (cdr x) (cdr y)))
              (cons (first y) (merge-maps x (cdr y)))))
        x)
    y))

(defthm merge-maps-when-not-consp-left
  (implies (not (consp x))
           (equal (merge-maps x y)
                  y))
  :hints(("Goal" :in-theory (enable merge-maps))))

(defthm merge-maps-when-not-consp-right
  (implies (not (consp y))
           (equal (merge-maps x y)
                  (if (consp x)
                      x
                    y)))
  :hints(("Goal" :in-theory (enable merge-maps))))

(defthm merge-maps-of-cons-and-cons
  (equal (merge-maps (cons a x) (cons b y))
         (if (<< (car a) (car b))
             (cons a (merge-maps x (cons b y)))
           (if (equal (car a) (car b))
               (cons a (merge-maps x y))
             (cons b (merge-maps (cons a x) y)))))
  :hints(("Goal" :in-theory (enable merge-maps))))

(defthm consp-of-merge-maps
  (equal (consp (merge-maps x y))
         (or (consp x)
             (consp y)))
  :hints(("Goal" :in-theory (enable merge-maps))))

(defthm lookup-of-first-of-first
  (iff (lookup (first (first x)) x)
       (consp x)))

(defthm lookup-when-not-first-of-first
  (implies (not (equal a (first (first x))))
           (equal (lookup a (cdr x))
                  (lookup a x))))

(defthm smaller-than-merge-maps
  (implies (and (<< a (car (car x)))
                (<< a (car (car y))))
           (<< a (car (car (merge-maps x y)))))
  :hints(("Goal" :in-theory (enable merge-maps))))

(defthm ordered-mapp-of-merge-maps
  (implies (and (ordered-mapp x)
                (ordered-mapp y))
           (equal (ordered-mapp (merge-maps x y))
                  t))
  :hints(("Goal"
          :induct (merge-maps x y)
          :expand ((merge-maps x y))
          :in-theory (enable (:induction merge-maps)))))

(defthm mapp-of-merge-maps
  (implies (and (mapp x)
                (mapp y))
           (equal (mapp (merge-maps x y))
                  t))
  :hints(("Goal" :in-theory (enable merge-maps))))

(verify-guards merge-maps)

(defthm lookup-of-merge-maps
  (implies (and (ordered-mapp x)
                (ordered-mapp y))
           (equal (lookup a (merge-maps x y))
                  (or (lookup a x)
                      (lookup a y))))
  :hints(("Goal" :in-theory (enable merge-maps
                                    lemma-for-uniquep-when-ordered-mapp
                                    lemma-2-for-ordered-list-subsetp-property))))



(defund mergesort-map (x)
  (declare (xargs :guard (mapp x)
                  :measure (len x)
                  :verify-guards nil))
  (cond ((not (consp x))
         nil)
        ((not (consp (cdr x)))
         (list (car x)))
        (t
         (let ((split (halve-list x)))
           ;; Note that halve-list works in an accumulator style and reverses
           ;; the first half of the list.  We have to un-reverse it for our
           ;; lookup lemmas to hold.
           (merge-maps (mergesort-map (fast-rev (car split)))
                       (mergesort-map (cdr split)))))))

(defthm mergesort-map-when-not-consp
  (implies (not (consp x))
           (equal (mergesort-map x)
                  nil))
  :hints(("Goal" :in-theory (enable mergesort-map))))

(defthm mergesort-map-when-not-consp-of-cdr
  (implies (not (consp (cdr x)))
           (equal (mergesort-map x)
                  (if (consp x)
                      (list (car x))
                    nil)))
  :hints(("Goal" :in-theory (enable mergesort-map))))

(defthm mapp-of-mergesort-map
  (implies (mapp x)
           (equal (mapp (mergesort-map x))
                  t))
  :hints(("Goal" :in-theory (enable mergesort-map))))

(defthm ordered-mapp-of-mergesort-map
  (equal (ordered-mapp (mergesort-map x))
         t)
  :hints(("Goal" :in-theory (enable mergesort-map ordered-mapp))))

(verify-guards mergesort-map)

(defthm uniquep-of-domain-of-mergesort-map
  (equal (uniquep (domain (mergesort-map x)))
         t))

(defthmd lemma-1-for-lookup-of-mergesort-map
  (implies (not (lookup a (REV (FIRST (HALVE-LIST X)))))
           (equal (lookup a (cdr (halve-list x)))
                  (lookup a x)))
  :hints(("Goal" :use ((:instance halve-list-lookup-property)))))

(defthmd lemma-2-for-lookup-of-mergesort-map
  (implies (LOOKUP A (REV (FIRST (HALVE-LIST X))))
           (equal (LOOKUP A (REV (FIRST (HALVE-LIST X))))
                  (lookup a x)))
  :hints(("Goal" :use ((:instance halve-list-lookup-property)))))

(defthm lookup-of-mergesort-map
  (equal (lookup a (mergesort-map x))
         (lookup a x))
  :hints(("Goal"
          :induct (mergesort-map x)
          :in-theory (enable mergesort-map
                             lemma-1-for-lookup-of-mergesort-map
                             lemma-2-for-lookup-of-mergesort-map))))

(defthm submapp-of-mergesort-map-and-self-left
  (equal (submapp (mergesort-map x) x)
         t)
  :hints(("Goal" :use ((:instance submapp-badguy-membership-property
                                  (x (mergesort-map x))
                                  (y x))))))

(defthm submapp-of-mergesort-map-and-self-right
  (equal (submapp x (mergesort-map x))
         t)
  :hints(("Goal" :use ((:instance submapp-badguy-membership-property
                                  (y (mergesort-map x))
                                  (x x))))))

(defthm submapp-of-mergesort-map-left
  (equal (submapp (mergesort-map x) y)
         (submapp x y)))

(defthm submapp-of-mergesort-map-right
  (equal (submapp x (mergesort-map y))
         (submapp x y)))



;; Here is our fast submapp check that can be applied once the two maps have
;; been standardized using mergesort-map.  Although there are many lemmas for
;; the correctness proof here, they're each pretty straightforward and just
;; address the particular cases.

(defund ordered-map-submapp (x y)
  (declare (xargs :guard (and (mapp x)
                              (mapp y)
                              (ordered-mapp x)
                              (ordered-mapp y))))
  (if (consp x)
      (if (consp y)
          (if (equal (car (car x))
                     (car (car y)))
              (and (equal (cdr (car x))
                          (cdr (car y)))
                   (ordered-map-submapp (cdr x) (cdr y)))
            (if (<< (car (car x))
                    (car (car y)))
                nil
              (ordered-map-submapp x (cdr y))))
        nil)
    t))

(defthm ordered-map-submapp-when-not-consp-left
  (implies (not (consp x))
           (equal (ordered-map-submapp x y)
                  t))
  :hints(("Goal" :in-theory (enable ordered-map-submapp))))

(defthm ordered-map-submapp-when-not-consp-right
  (implies (not (consp y))
           (equal (ordered-map-submapp x y)
                  (not (consp x))))
  :hints(("Goal" :in-theory (enable ordered-map-submapp))))

(defthm ordered-map-submapp-of-cons-and-cons
  (equal (ordered-map-submapp (cons a x) (cons b y))
         (if (equal (car a) (car b))
             (and (equal (cdr a) (cdr b))
                  (ordered-map-submapp x y))
           (if (<< (car a) (car b))
               nil
             (ordered-map-submapp (cons a x) y))))
  :hints(("Goal" :in-theory (enable ordered-map-submapp))))

(defthm booleanp-of-ordered-map-submapp
  (equal (booleanp (ordered-map-submapp x y))
         t)
  :hints(("Goal" :in-theory (enable ordered-map-submapp))))

(defthmd lemma-1-for-ordered-map-submapp-property
  (implies (and (not (equal a (car (first y))))
                (not (consp (cdr y))))
           (equal (lookup a y)
                  nil)))

(defthmd lemma-2-for-ordered-map-submapp-property
  (implies (and (not (equal (car (first x)) (car (first y))))
                (not (consp (cdr y))))
           (equal (submapp x y)
                  (not (consp x))))
  :hints(("Goal" :in-theory (enable submapp))))

(defthmd lemma-3-for-ordered-map-submapp-property
  (implies (and (consp x)
                (not (consp y)))
           (equal (submapp x y)
                  nil))
  :hints(("Goal"
          :in-theory (disable equal-of-lookups-when-submapp)
          :use ((:instance equal-of-lookups-when-submapp
                           (x x)
                           (y y)
                           (a (car (car x))))))))

(defthmd lemma-4-for-ordered-map-submapp-property-aux
  (implies (not (memberp (first (first y)) dom))
           (equal (submapp1 dom x (cdr y))
                  (submapp1 dom x y)))
  :hints(("Goal" :in-theory (enable submapp1))))

(defthmd lemma-4-for-ordered-map-submapp-property
   (implies (and (submapp x y)
                 (not (equal (first (first x)) (first (first y))))
                 (not (<< (first (first x)) (first (first y))))
                 (ordered-mapp x))
            (equal (submapp x (cdr y))
                   t))
   :hints(("Goal"
           :in-theory (enable lemma-4-for-ordered-map-submapp-property-aux
                              lemma-for-uniquep-when-ordered-mapp
                              submapp))))

(defthmd lemma-5-for-ordered-map-submapp-property
  (implies (and (not (equal (first (first x)) (first (first y))))
                (<< (first (first x)) (first (first y)))
                (ordered-mapp y)
                (consp x))
           (equal (submapp x y)
                  nil))
  :hints(("Goal"
          :in-theory (disable lemma-for-uniquep-when-ordered-mapp)
          :use ((:instance lemma-for-uniquep-when-ordered-mapp
                           (a (first (first x)))
                           (x y))))))

(defthmd lemma-6-for-ordered-map-submapp-property
  (implies (and (consp x)
                (equal (first (first x)) (first (first y)))
                (not (equal (cdr (first x)) (cdr (first y)))))
           (equal (submapp x y)
                  nil))
  :hints(("Goal"
          :in-theory (e/d (equal-of-cons-rewrite-constants)
                          (equal-of-lookups-when-submapp))
          :use ((:instance equal-of-lookups-when-submapp
                           (a (first (first x)))
                           (x x)
                           (y y))))))

(defthmd lemma-7-for-ordered-map-submapp-property-aux
  (implies (and (equal (first (first x)) (first (first y)))
                (equal (cdr (first x)) (cdr (first y)))
                (consp x)
                (consp y))
           (equal (submapp1 (remove-all (first (first x)) dom) (cdr x) (cdr y))
                  (submapp1 dom x y)))
  :hints(("Goal" :in-theory (enable submapp1))))

(defthmd lemma-7-for-ordered-map-submapp-property
  (implies (and (equal (first (first x)) (first (first y)))
                (equal (cdr (first x)) (cdr (first y)))
                (ordered-mapp x)
                (consp x)
                (consp y))
           (equal (submapp (cdr x) (cdr y))
                  (submapp x y)))
  :hints(("Goal"
          :in-theory (enable submapp
                             lemma-for-uniquep-when-ordered-mapp)
          :use ((:instance lemma-7-for-ordered-map-submapp-property-aux
                           (dom (domain x)))))))

(defthm ordered-map-submapp-property
  (implies (and (force (ordered-mapp x))
                (force (ordered-mapp y)))
           (equal (ordered-map-submapp x y)
                  (submapp x y)))
  :hints(("Goal"
          :in-theory (enable ordered-map-submapp
                             lemma-1-for-ordered-map-submapp-property
                             lemma-2-for-ordered-map-submapp-property
                             lemma-3-for-ordered-map-submapp-property
                             lemma-4-for-ordered-map-submapp-property
                             lemma-5-for-ordered-map-submapp-property
                             lemma-6-for-ordered-map-submapp-property
                             lemma-7-for-ordered-map-submapp-property)
          :induct (ordered-map-submapp x y))))



(defthmd lemma-for-ordered-listp-when-ordered-mapp
  (implies (and (<< (car a) (car b))
                (consp a)
                (consp b))
           (equal (<< a b)
                  t))
  :hints(("Goal" :in-theory (enable <<))))

(defthm ordered-listp-when-ordered-mapp
  (implies (and (ordered-mapp x)
                (force (mapp x)))
           (equal (ordered-listp x)
                  t))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand (ordered-listp x)
          :in-theory (enable lemma-for-ordered-listp-when-ordered-mapp))))

(defthm ordered-listp-of-mergesort-map
  (implies (mapp x)
           (equal (ordered-listp (mergesort-map x))
                  t)))
