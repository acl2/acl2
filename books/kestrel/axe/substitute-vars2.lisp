; New tools for substituting equated vars in DAGS
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "substitute-vars")
(include-book "remove-duplicates-from-sorted-list")
(include-book "rebuild-nodes2") ;reduce
(include-book "../acl2-arrays/typed-acl2-arrays")
(local (include-book "kestrel/lists-light/remove-duplicates-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-listp" :dir :system))
(local (include-book "merge-sort-less-than-rules"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/arithmetic-light/max" :dir :system))

;; ACC contains the smallest items, in decreasing order.
(defund merge-<-and-remove-dups-aux (l1 l2 acc)
  (declare (xargs :measure (+ (len l1) (len l2))

                  :guard (and (all-rationalp l1)
                              (all-rationalp l2)
                              (true-listp acc))))
  (cond ((atom l1) (revappend acc l2))
        ((atom l2) (revappend acc l1))
        ((equal (car l1) (car l2)) ;drop one copy:
         (merge-<-and-remove-dups-aux (cdr l1) l2 acc))
        ((< (car l1) (car l2))
         (merge-<-and-remove-dups-aux (cdr l1)
                                      l2 (cons (car l1) acc)))
        (t (merge-<-and-remove-dups-aux l1 (cdr l2)
                                        (cons (car l2) acc)))))

(defthm nat-listp-of-merge-<-and-remove-dups-aux
  (implies (and (nat-listp l1)
                (nat-listp l2)
                (nat-listp acc))
           (nat-listp (merge-<-and-remove-dups-aux l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups-aux))))

(defthm sortedp-<=-of-merge-<-and-remove-dups-aux
  (implies (and (sortedp-<= l1)
                (sortedp-<= l2)
                (sortedp-<= (reverse-list acc))
                (all-<=-all acc l1)
                (all-<=-all acc l2))
           (sortedp-<= (merge-<-and-remove-dups-aux l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups-aux
                                     revappend-lemma))))

(defthmd not-intersection-equal-when-all-<-of-car-and-sortedp-<=
  (implies (and (all-< acc (car l2))
                (sortedp-<= l2))
           (not (intersection-equal l2 acc)))
  :hints (("Goal" :in-theory (enable all-< sortedp-<= intersection-equal))))

(defthmd <=-of-car-and-cadr-when-sortedp-<=
  (implies (and (sortedp-<= x)
                (consp (cdr x)))
           (<= (car x) (cadr x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable sortedp-<=))))

(defthmd <-of-car-and-cadr-when-sortedp-<=-and-no-duplicatesp-equal
  (implies (and (sortedp-<= x)
                (no-duplicatesp-equal x)
                (consp (cdr x))
                (all-rationalp x))
           (< (car x) (cadr x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable sortedp-<= no-duplicatesp-equal))))

(defthm no-duplicatesp-equal-of-merge-<-and-remove-dups-aux
  (implies (and (sortedp-<= l1)
                (sortedp-<= l2)
                (sortedp-<= (reverse-list acc))
                (implies (consp l1) (all-< acc (first l1)))
                (implies (consp l2) (all-< acc (first l2)))
                (no-duplicatesp-equal l1)
                (no-duplicatesp-equal l2)
                (no-duplicatesp-equal acc)
                (all-rationalp l1)
                (all-rationalp l2))
           (no-duplicatesp-equal (merge-<-and-remove-dups-aux l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups-aux
                                     revappend-lemma
                                     not-intersection-equal-when-all-<-of-car-and-sortedp-<=
                                     <=-of-car-and-cadr-when-sortedp-<=
                                     <-of-car-and-cadr-when-sortedp-<=-and-no-duplicatesp-equal))))

;; Merge L1 and L2 into a sorted list representing their union, except avoid
;; duplication that arises when an item is in both L1 and L2.  L1 and L2 should
;; each be sorted and duplicate-free.  If either L1 or L2 is empty, this should
;; be very fast.
(defund merge-<-and-remove-dups (l1 l2)
  (declare (xargs :guard (and (all-rationalp l1)
                              (all-rationalp l2))))
  (merge-<-and-remove-dups-aux l1 l2 nil))

;(merge-<-and-remove-dups '(1 2 2 3 5 5 5 6 6 8) '(1 2 3 4 5 6 7 7))

(defthm nat-listp-of-merge-<-and-remove-dups
  (implies (and (nat-listp l1)
                (nat-listp l2))
           (nat-listp (merge-<-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups))))

(defthm sortedp-<=-of-merge-<-and-remove-dups
  (implies (and (sortedp-<= l1)
                (sortedp-<= l2))
           (sortedp-<= (merge-<-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups))))

(defthm no-duplicatesp-equal-of-merge-<-and-remove-dups
  (implies (and (sortedp-<= l1)
                (sortedp-<= l2)
                (no-duplicatesp-equal l1)
                (no-duplicatesp-equal l2)
                (all-rationalp l1)
                (all-rationalp l2))
           (no-duplicatesp-equal (merge-<-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups))))

;move
(local
 (defthm consp-of-strip-caddrs
  (equal (consp (strip-caddrs x))
         (consp x))
  :hints (("Goal" :in-theory (enable strip-caddrs)))))

;move
;can expose the cdr to other rules
(local
 (defthm strip-caddrs-of-cdr
  (equal (strip-caddrs (cdr x))
         (cdr (strip-caddrs x)))
  :hints (("Goal" :in-theory (enable strip-caddrs)))))

;move
(local
 (defthm strip-caddrs-of-cons
  (equal (strip-caddrs (cons x y))
         (cons (caddr x)
               (strip-caddrs y)))
  :hints (("Goal" :in-theory (enable strip-caddrs)))))

(defthmd <-of-car-of-car-when-all-<-of-strip-cars
  (implies (and (all-< (strip-cars x) bound)
                (consp x))
           (< (car (car x)) bound))
  :hints (("Goal" :in-theory (enable strip-cars))))

(local (in-theory (enable <-of-car-of-car-when-all-<-of-strip-cars)))

(local (in-theory (disable set-difference-equal strip-cars strip-cadrs))) ;prevent inductions

(local (in-theory (disable natp dargp
                           default-car
                           max
                           )))

;;todo: NO-ATOMS, all-consp, and all-myquotep are the same for lists of dargs

(defthm <-of--1-and-largest-non-quotep
  (implies (all-dargp x)
           (equal (< -1 (largest-non-quotep x))
                  (not (all-consp x)))))

;dup
(defthm <-of-if-arg2
  (equal (< x (if test y z))
         (if test
             (< x y)
           (< x z))))

;move
(defthm largest-non-quotep-when-all-consp
  (implies (all-consp x)
           (equal (largest-non-quotep x)
                  -1))
  :hints (("Goal" :in-theory (enable largest-non-quotep all-consp))))

(local
 (defthm integerp-of-if
   (equal (integerp (if test tp ep))
          (if test
              (integerp tp)
            (integerp ep)))))

;; a triple of the form (<nodenum-of-var> <equated-nodenum-or-constant> <literal-nodenum>).
;; TODO: Save a cons by making the literal-nodenum the final cdr?
(defund subst-candidatep (cand)
  (declare (xargs :guard t))
  (and (true-listp cand)
       (equal 3 (len cand))
       (natp (first cand))
       (dargp (second cand))
       (natp (third cand))))

(defthmd natp-of-car-when-subst-candidatep
  (implies (subst-candidatep cand)
           (natp (car cand)))
  :hints (("Goal" :in-theory (enable subst-candidatep))))

(defthmd consp-when-subst-candidatep
  (implies (subst-candidatep cand)
           (consp cand))
  :hints (("Goal" :in-theory (enable subst-candidatep))))

(defthmd consp-of-cdr-when-subst-candidatep
  (implies (subst-candidatep cand)
           (consp (cdr cand)))
  :hints (("Goal" :in-theory (enable subst-candidatep))))

(defthmd len-of-cadr-when-subst-candidatep
  (implies (subst-candidatep cand)
           (equal (len (cadr cand))
                  (if (consp (cadr cand))
                      2
                    0)))
  :hints (("Goal" :in-theory (enable subst-candidatep))))

(defthmd dargp-of-cadr-when-subst-candidatep
  (implies (subst-candidatep cand)
           (dargp (cadr cand)))
  :hints (("Goal" :in-theory (enable subst-candidatep))))

(defthmd natp-of-cadr-when-subst-candidatep
  (implies (and (subst-candidatep cand)
                (not (consp (cadr cand))))
           (natp (cadr cand)))
  :hints (("Goal" :in-theory (enable subst-candidatep))))

(defund subst-candidate-listp (cands)
  (declare (xargs :guard t))
  (if (atom cands)
      (null cands)
    (and (subst-candidatep (first cands))
         (subst-candidate-listp (rest cands)))))

(defthm subst-candidatep-of-car
  (implies (and (subst-candidate-listp cands)
                (consp cands))
           (subst-candidatep (car cands)))
  :hints (("Goal" :in-theory (enable subst-candidate-listp))))

(defthm subst-candidate-listp-of-cons
  (equal (subst-candidate-listp (cons cand cands))
         (and (subst-candidatep cand)
              (subst-candidate-listp cands)))
  :hints (("Goal" :in-theory (enable subst-candidate-listp))))

;;so we can call strip-cadrs
(defthmd all->=-len-of-2-when-subst-candidate-listp
  (implies (subst-candidate-listp subst-candidates)
           (all->=-len subst-candidates 2))
  :hints (("Goal" :in-theory (enable subst-candidatep
                                     subst-candidate-listp))))

;;so we can call strip-caddrs
(defthmd all->=-len-of-3-when-subst-candidate-listp
  (implies (subst-candidate-listp subst-candidates)
           (all->=-len subst-candidates 3))
  :hints (("Goal" :in-theory (enable subst-candidatep
                                     subst-candidate-listp))))

(defthm subst-candidate-listp-of-cdr
  (implies (subst-candidate-listp subst-candidates)
           (subst-candidate-listp (cdr subst-candidates)))
  :hints (("Goal" :in-theory (enable subst-candidate-listp))))

(defthm natp-of-car-of-car-when-subst-candidate-listp
  (implies (and (subst-candidate-listp subst-candidates)
                (consp subst-candidates))
           (natp (car (car subst-candidates))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable subst-candidate-listp))))

;;So we can call strip-cars
(defthm subst-candidate-listp-forward-to-alistp
  (implies (subst-candidate-listp cands)
           (alistp cands))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable subst-candidate-listp alistp))))

(defthm rational-listp-of-strip-cars-when-subst-candidate-listp
  (implies (subst-candidate-listp subst-candidates)
           (rational-listp (strip-cars subst-candidates)))
  :hints (("Goal" :in-theory (enable subst-candidate-listp strip-cars))))

(defthm all-natp-of-strip-cars-when-subst-candidate-listp
  (implies (subst-candidate-listp subst-candidates)
           (all-natp (strip-cars subst-candidates)))
  :hints (("Goal" :in-theory (enable subst-candidate-listp strip-cars))))

(defthm nat-listp-of-strip-cars-when-subst-candidate-listp
  (implies (subst-candidate-listp subst-candidates)
           (nat-listp (strip-cars subst-candidates)))
  :hints (("Goal" :in-theory (enable subst-candidate-listp strip-cars))))

(defthm all-dargp-of-strip-cadrs-when-subst-candidate-listp
  (implies (subst-candidate-listp subst-candidates)
           (all-dargp (strip-cadrs subst-candidates)))
  :hints (("Goal" :in-theory (enable subst-candidatep subst-candidate-listp strip-cadrs))))

;; TODO: What if we have the equality of two vars?  Should we consider both?


;decides whether we should substitute (is it the nodenum of a var, and is it equated to a term that doesn't include itself?)
;; Returns (mv substp var).
;; Does not check whether the var depends on itself.
(defund ensure-substitutable-var2 (nodenum-or-quotep dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dargp-less-than nodenum-or-quotep dag-len))
                  :guard-hints (("Goal" :in-theory (disable myquotep))))
           (ignore dag-len))
  (if (atom nodenum-or-quotep)
      (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
        (if (symbolp expr)
            (mv t expr)
          (mv nil nil)))
    (mv nil nil)))

;;;
;;; find-var-and-expr-to-subst
;;;

;; Returns (mv foundp var nodenum-of-var equated-thing) where equated-thing will always be a nodenum or quotep.
;the awkwardness here is to avoid doing the aref more than once..
;; TODO: what if we have (equal var1 var2)?  is there a way to tell which would be better to eliminate? maybe it doesn't matter
;; Does not check whether the var depends on itself.
(defund find-var-and-expr-to-subst2 (lhs rhs dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dargp-less-than lhs dag-len)
                              (dargp-less-than rhs dag-len))))
  (mv-let (substp var)
    (ensure-substitutable-var2 lhs dag-array dag-len)
    (if substp
        (mv t var lhs rhs)
      (mv-let (substp var)
        (ensure-substitutable-var2 rhs dag-array dag-len)
        (if substp
            (mv t var rhs lhs)
          (mv nil nil nil nil))))))

(defthm natp-of-mv-nth-2-of-find-var-and-expr-to-subst2
  (implies (and (mv-nth 0 (find-var-and-expr-to-subst2 lhs rhs dag-array dag-len))
                (dargp rhs)
                (dargp lhs))
           (natp (mv-nth 2 (find-var-and-expr-to-subst2 lhs rhs dag-array dag-len))))
  :hints (("Goal" :in-theory (enable find-var-and-expr-to-subst2 ensure-substitutable-var2))))

(defthm <-of-mv-nth-2-of-find-var-and-expr-to-subst2
  (implies (and (mv-nth 0 (find-var-and-expr-to-subst2 lhs rhs dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (dargp-less-than lhs dag-len)
                (dargp-less-than rhs dag-len))
           (< (mv-nth 2 (find-var-and-expr-to-subst2 lhs rhs dag-array dag-len))
              dag-len))
  :hints (("Goal" :in-theory (enable find-var-and-expr-to-subst2 ensure-substitutable-var2))))

(defthm dargp-of-mv-nth-3-of-find-var-and-expr-to-subst2
  (implies (and (mv-nth 0 (find-var-and-expr-to-subst2 lhs rhs dag-array dag-len))
                (dargp rhs)
                (dargp lhs)
                (not (consp (mv-nth 3 (find-var-and-expr-to-subst2 lhs rhs dag-array dag-len)))))
           (dargp (mv-nth 3 (find-var-and-expr-to-subst2 lhs rhs dag-array dag-len))))
  :hints (("Goal" :in-theory (enable find-var-and-expr-to-subst2 ensure-substitutable-var2))))

(defthm dargp-less-than-of-mv-nth-3-of-find-var-and-expr-to-subst2
  (implies (and (mv-nth 0 (find-var-and-expr-to-subst2 lhs rhs dag-array dag-len))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (dargp-less-than lhs dag-len)
                (dargp-less-than rhs dag-len))
           (dargp-less-than (mv-nth 3 (find-var-and-expr-to-subst2 lhs rhs dag-array dag-len))
                            dag-len))
  :hints (("Goal" :in-theory (enable find-var-and-expr-to-subst2 ensure-substitutable-var2))))

;;;
;;; check-for-var-subst-literal
;;;

;; Checks whether LITERAL-NODENUM represents a (negated) equality we can use to substitute.
;; Returns (mv foundp var nodenum-of-var nodenum-or-quotep-to-put-in).
;; Does not check whether the var depends on itself.
(defund check-for-var-subst-literal2 (literal-nodenum dag-array dag-len)
  (declare (xargs :guard (and (natp literal-nodenum)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< literal-nodenum dag-len))
                  :guard-hints (("Goal" :in-theory (enable consp-of-cdr
                                                           NATP-OF-+-OF-1)))))
  (let ((expr (aref1 'dag-array dag-array literal-nodenum)))
    ;; we seek an expr of the form (not <nodenum>)
    (if (not (and (call-of 'not expr)
                  (consp (dargs expr))
                  (integerp (darg1 expr))))
        (mv nil nil nil nil) ;fail
      (let ((non-nil-expr (aref1 'dag-array dag-array (darg1 expr)))) ;;we seek a NON-NIL-EXPR of the form (equal <nodenum-of-var> <thing>) or vice-versa
        (if (not (and (call-of 'equal non-nil-expr)
                      (consp (cdr (dargs non-nil-expr)))))
            (mv nil nil nil nil) ;fail
          (find-var-and-expr-to-subst2 (darg1 non-nil-expr) (darg2 non-nil-expr) dag-array dag-len) ;this is what prevents loops
          )))))

(defthm natp-of-mv-nth-2-of-check-for-var-subst-literal2
  (implies (and (mv-nth 0 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))
                (natp literal-nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< literal-nodenum dag-len))
           (natp (mv-nth 2 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))))
  :hints (("Goal" :in-theory (enable check-for-var-subst-literal2 len-of-0-and-len consp-of-cdr))))

(defthm <-mv-nth-2-of-check-for-var-subst-literal2
  (implies (and (mv-nth 0 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))
                (natp literal-nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< literal-nodenum dag-len))
           (< (mv-nth 2 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))
              dag-len))
  :hints (("Goal" :in-theory (enable check-for-var-subst-literal2 len-of-0-and-len consp-of-cdr))))

(defthm dargp-less-than-of-mv-nth-3-of-check-for-var-subst-literal2
  (implies (and (mv-nth 0 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))
                (natp literal-nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< literal-nodenum dag-len))
           (dargp-less-than (mv-nth 3 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))
                            dag-len))
  :hints (("Goal" :in-theory (enable check-for-var-subst-literal2 len-of-0-and-len consp-of-cdr))))

(defthm dargp-less-than-of-mv-nth-3-of-check-for-var-subst-literal2-gen
  (implies (and (mv-nth 0 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))
                (natp literal-nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< literal-nodenum dag-len)
                (<= dag-len bound))
           (dargp-less-than (mv-nth 3 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))
                            bound))
  :hints (("Goal" :use (:instance dargp-less-than-of-mv-nth-3-of-check-for-var-subst-literal2)
           :in-theory (disable dargp-less-than-of-mv-nth-3-of-check-for-var-subst-literal2))))

(defthm dargp-of-mv-nth-3-of-check-for-var-subst-literal2
  (implies (and (mv-nth 0 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))
                (natp literal-nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< literal-nodenum dag-len))
           (dargp (mv-nth 3 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))))
  :hints (("Goal" :use (:instance dargp-less-than-of-mv-nth-3-of-check-for-var-subst-literal2)
           :in-theory (disable dargp-less-than-of-mv-nth-3-of-check-for-var-subst-literal2
                               dargp-less-than-of-mv-nth-3-of-check-for-var-subst-literal2-gen))))

(defthm natp-of-mv-nth-3-of-check-for-var-subst-literal2
  (implies (and (mv-nth 0 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))
                (natp literal-nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< literal-nodenum dag-len))
           (equal (natp (mv-nth 3 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len)))
                  (not (consp (mv-nth 3 (check-for-var-subst-literal2 literal-nodenum dag-array dag-len))))))
  :hints (("Goal" :use (:instance dargp-less-than-of-mv-nth-3-of-check-for-var-subst-literal2)
           :in-theory (disable dargp-less-than-of-mv-nth-3-of-check-for-var-subst-literal2
                               dargp-less-than-of-mv-nth-3-of-check-for-var-subst-literal2-gen))))

;; Returns a subst-candidate-listp representing all the substitution candidates
;; for the LITERAL-NODENUMS.  Looks through the literals for ones that equate
;; vars with other nodes.  Does not check whether the var depends on itself.
(defund subst-candidates (literal-nodenums dag-array dag-len lim acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len)
                              (natp lim))))
  (if (or (endp literal-nodenums)
          (zp lim))
      acc
    (b* ((literal-nodenum (first literal-nodenums))
         ((mv foundp
              & ;; var
              nodenum-of-var
              nodenum-or-quotep-to-put-in)
          ;;  TTODO: Use a version of this that doesn't check supporters (make sure, elsewhere, that we avoid self-supporting vars):
          (check-for-var-subst-literal2 literal-nodenum dag-array dag-len)))
      (subst-candidates (rest literal-nodenums)
                        dag-array
                        dag-len
                        (if foundp (+ -1 lim) lim)
                        (if foundp
                            (cons (list nodenum-of-var nodenum-or-quotep-to-put-in literal-nodenum)
                                  acc)
                          acc)))))

(defthm subst-candidates-when-not-consp
  (implies (not (consp literal-nodenums))
           (equal (subst-candidates literal-nodenums dag-array dag-len lim acc)
                  acc))
  :hints (("Goal" :in-theory (enable subst-candidates))))

(defthm subst-candidate-listp-of-subst-candidates
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (subst-candidate-listp acc))
           (subst-candidate-listp (subst-candidates literal-nodenums dag-array dag-len lim acc)))
  :hints (("Goal" :in-theory (e/d (subst-candidates subst-candidatep subst-candidate-listp)
                                  ()))))

(defthm all-<-of-strip-cars-of-subst-candidates
  (implies (and (all-< literal-nodenums dag-len)
                (nat-listp literal-nodenums)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (all-< (strip-cars acc)
                       dag-len))
           (all-< (strip-cars (subst-candidates literal-nodenums dag-array dag-len lim acc))
                  dag-len))
  :hints (("Goal" :in-theory (enable subst-candidates))))

(defthmd subsetp-equal-of-strip-caddrs-of-subst-candidates-helper
  (subsetp-equal (strip-caddrs (subst-candidates literal-nodenums dag-array dag-len lim acc))
                 (append literal-nodenums (strip-caddrs acc)))
  :hints (("Goal" :in-theory (e/d (STRIP-CADDRS subst-candidates) (CHECK-FOR-VAR-SUBST-LITERAL2)))))

(local
 (defthm subsetp-equal-of-strip-caddrs-of-subst-candidates
  (subsetp-equal (strip-caddrs (subst-candidates literal-nodenums dag-array dag-len lim nil))
                 literal-nodenums)
  :hints (("Goal" :use (:instance subsetp-equal-of-strip-caddrs-of-subst-candidates-helper (acc nil))
           :in-theory (disable subsetp-equal-of-strip-caddrs-of-subst-candidates-helper)))))

;very slow
(defthm <-of-largest-non-quotep-of-strip-cadrs-of-subst-candidates
  (implies (and (all-< literal-nodenums dag-len)
                (nat-listp literal-nodenums)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< (largest-non-quotep (strip-cadrs acc)) dag-len))
           (< (largest-non-quotep (strip-cadrs (subst-candidates literal-nodenums dag-array dag-len lim acc)))
              dag-len))
  :hints (("Goal" :in-theory (enable subst-candidates strip-cadrs
                                     largest-non-quotep ;expensive
                                     check-for-var-subst-literal2
                                     find-var-and-expr-to-subst2))))

;similar to the above
(defthm all-dargp-less-than-of-strip-cadrs-of-subst-candidates
  (implies (and (all-< literal-nodenums dag-len)
                (nat-listp literal-nodenums)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (all-dargp-less-than (strip-cadrs acc) dag-len))
           (all-dargp-less-than (strip-cadrs (subst-candidates literal-nodenums dag-array dag-len lim acc))
                               dag-len))
  :hints (("Goal" :in-theory (enable subst-candidates strip-cadrs largest-non-quotep check-for-var-subst-literal2
                                     find-var-and-expr-to-subst2
                                     NATP-OF-+-OF-1))))


;; Maps each node of a candidate var to the sorted lis of the nodenums of the
;; candidates on which it depends.  We say a candidate var X depends on another
;; candidate var Y when the expression to be put in for to X (according to a
;; literal that equates it to X) mentions Y.
(def-typed-acl2-array2 candidate-deps-arrayp
  (and (nat-listp val)
       (no-duplicatesp-equal val)
       (sortedp-<= val)))

(defthm <=-of-maxelem-of-strip-cars-of-cdr
  (implies (consp (cdr x))
           (<= (maxelem (strip-cars (cdr x)))
               (maxelem (strip-cars x))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable maxelem strip-cars))))

;; Marks the nodenum of each (candidate) var as depending on itself, unless it
;; is too large to be relevant.  This initializes the dependency calculation.
(defund mark-all-relevant-vars (subst-candidates max-relevant-nodenum candidate-deps-array)
  (declare (xargs :guard (and (subst-candidate-listp subst-candidates)
                              (natp max-relevant-nodenum)
                              (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                              (equal (alen1 'candidate-deps-array candidate-deps-array)
                                     (+ 1 max-relevant-nodenum)))))
  (if (endp subst-candidates)
      candidate-deps-array
    (let* ((candidate (first subst-candidates))
           (var-nodenum (car candidate)))
      (mark-all-relevant-vars (rest subst-candidates)
                              max-relevant-nodenum
                              (if (<= var-nodenum max-relevant-nodenum)
                                  ;; Mark the nodenum of the var as depending on itself:
                                  (aset1 'candidate-deps-array candidate-deps-array var-nodenum (list var-nodenum))
                                ;; This var nodenum is larger that all equated things, so none of them can depend on it:
                                candidate-deps-array)))))

(defthm alen1-of-mark-all-relevant-vars
  (implies (subst-candidate-listp subst-candidates)
           (equal (alen1 'candidate-deps-array (mark-all-relevant-vars subst-candidates max-relevant-nodenum candidate-deps-array))
                  (alen1 'candidate-deps-array candidate-deps-array)))
  :hints (("Goal" :in-theory (enable mark-all-relevant-vars))))

(defthm candidate-deps-arrayp-of-mark-all-relevant-vars
  (implies (and (subst-candidate-listp subst-candidates)
                (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (equal (alen1 'candidate-deps-array candidate-deps-array)
                       (+ 1 max-relevant-nodenum)))
           (candidate-deps-arrayp 'candidate-deps-array (mark-all-relevant-vars subst-candidates max-relevant-nodenum candidate-deps-array)))
  :hints ( ;("subgoal *1/4" :cases ((consp (CDR SUBST-CANDIDATES))))
          ("Goal" :do-not '(generalize eliminate-destructors) :in-theory (enable mark-all-relevant-vars STRIP-CARS))))

;; Merges the deps for all the ARGS into ACC, avoiding duplicates.
(defund merge-deps-for-args (args candidate-deps-array
                                  acc ; should be sorted
                                  )
  (declare (xargs :guard (and (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                              (all-dargp-less-than args (alen1 'candidate-deps-array candidate-deps-array))
                              (true-listp args)
                              (nat-listp acc))))
  (if (endp args)
      acc
    (let ((arg (first args)))
      (if (consp arg) ;check for quotep
          (merge-deps-for-args (rest args) candidate-deps-array acc)
        (let ((candidates-arg-depends-on (aref1 'candidate-deps-array candidate-deps-array arg)))
          (merge-deps-for-args (rest args)
                               candidate-deps-array
                               (merge-<-and-remove-dups candidates-arg-depends-on acc)))))))

(defthm nat-listp-of-merge-deps-for-args
  (implies (and (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (all-dargp-less-than args (alen1 'candidate-deps-array candidate-deps-array))
                (true-listp args)
                (nat-listp acc))
           (nat-listp (merge-deps-for-args args candidate-deps-array acc)))
  :hints (("Goal" :in-theory (enable merge-deps-for-args))))

(defthm true-listp-of-merge-deps-for-args
  (implies (and (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (all-dargp-less-than args (alen1 'candidate-deps-array candidate-deps-array))
                (true-listp args)
                (nat-listp acc))
           (true-listp (merge-deps-for-args args candidate-deps-array acc)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable merge-deps-for-args))))

(defthm sortedp-<=-of-merge-deps-for-args
  (implies (and (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (all-dargp-less-than args (alen1 'candidate-deps-array candidate-deps-array))
                (true-listp args)
                (nat-listp acc)
                (sortedp-<= acc))
           (sortedp-<= (merge-deps-for-args args candidate-deps-array acc)))
  :hints (("Goal" :in-theory (enable merge-deps-for-args))))

(defthm no-duplicatesp-equal-of-merge-deps-for-args
  (implies (and (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (all-dargp-less-than args (alen1 'candidate-deps-array candidate-deps-array))
                (true-listp args)
                (nat-listp acc)
                (sortedp-<= acc)
                (no-duplicatesp-equal acc))
           (no-duplicatesp-equal (merge-deps-for-args args candidate-deps-array acc)))
  :hints (("Goal" :in-theory (enable merge-deps-for-args
                                     all-rationalp-when-nat-listp))))

;; Helps compute the set of candidate vars on which every node in the DAG depends.
;; Returns the candidate-deps-array
(defund populate-candidate-deps-array-aux (n max candidate-deps-array dag-array dag-len)
  (declare (xargs :guard (and (natp n)
                              (integerp max)
                              (<= -1 max)
                              (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                              (< max (alen1 'candidate-deps-array candidate-deps-array))
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< max dag-len))
                  :measure (nfix (+ 1 (- max n)))
                  :hints (("Goal" :in-theory (enable natp)))))
  (if (or (not (mbt (natp n)))
          (not (mbt (integerp max)))
          (< max n))
      candidate-deps-array
    (let* ((expr (aref1 'dag-array dag-array n)))
      (if (or (variablep expr) ;; variable nodes that are candidates are already marked, other vars are unmarked
              (fquotep expr))
          (populate-candidate-deps-array-aux (+ 1 n) max candidate-deps-array dag-array dag-len)
        ;; it's a function call, so compute the set of vars on which the args depend
        (let* ((candidates-node-depends-on (merge-deps-for-args (dargs expr) candidate-deps-array nil))
               (candidate-deps-array (aset1 'candidate-deps-array candidate-deps-array n candidates-node-depends-on)))
          (populate-candidate-deps-array-aux (+ 1 n) max candidate-deps-array dag-array dag-len))))))

(defthm candidate-deps-arrayp-of-populate-candidate-deps-array-aux
  (implies (and (natp n)
                ;;(natp max)
                (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (< max (alen1 'candidate-deps-array candidate-deps-array))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< max dag-len))
           (candidate-deps-arrayp 'candidate-deps-array (populate-candidate-deps-array-aux n max candidate-deps-array dag-array dag-len)))
  :hints (("Goal" :in-theory (enable populate-candidate-deps-array-aux))))

(defthm alen1-of-populate-candidate-deps-array-aux
  (implies (and (natp n)
                (natp max)
                (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (< max (alen1 'candidate-deps-array candidate-deps-array))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< max dag-len))
           (equal (alen1 'candidate-deps-array (populate-candidate-deps-array-aux n max candidate-deps-array dag-array dag-len))
                  (alen1 'candidate-deps-array candidate-deps-array)))
  :hints (("Goal" :in-theory (enable populate-candidate-deps-array-aux))))

;; Computes, for each node in the DAG (up through the largest node that is an equated-thing in the SUBST-CANDIDATES), the
;; set of candidate vars (actually their nodenums) on which the node depends.
;; Returns the candidate-deps-array.
(defund populate-candidate-deps-array (subst-candidates dag-array dag-len)
  (declare (xargs :guard (and (subst-candidate-listp subst-candidates)
                              (not (all-consp (strip-cadrs subst-candidates))) ; these is at least one equated-thing that's a nodenum
                              (consp subst-candidates)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (or (endp subst-candidates)
                                  (<= (maxelem (strip-cars subst-candidates))
                                      (+ -1 dag-len)))
                              (< (largest-non-quotep (strip-cadrs subst-candidates))
                                 dag-len))
                  :guard-hints (("Goal" :in-theory (enable all->=-len-of-2-when-subst-candidate-listp
                                                           ALL-INTEGERP-WHEN-NAT-LISTP)))))
  (let* (;(max-var-nodenum (maxelem (strip-cars subst-candidates)))
         (max-equated-thing-nodenum (largest-non-quotep (strip-cadrs subst-candidates))) ;the equated-things are what we look up in the deps array
         (candidate-deps-array (make-empty-array 'candidate-deps-array (+ 1 max-equated-thing-nodenum)))
         (candidate-deps-array (mark-all-relevant-vars subst-candidates max-equated-thing-nodenum candidate-deps-array)))
    (populate-candidate-deps-array-aux 0 max-equated-thing-nodenum candidate-deps-array dag-array dag-len)))

(defthm candidate-deps-arrayp-of-populate-candidate-deps-array
  (implies (and (subst-candidate-listp subst-candidates)
                (consp subst-candidates)
                (not (all-consp (strip-cadrs subst-candidates)))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (or (endp subst-candidates)
                    (<= (maxelem (strip-cars subst-candidates))
                        (+ -1 dag-len)))
                (< (largest-non-quotep (strip-cadrs subst-candidates))
                   dag-len))
           (candidate-deps-arrayp 'candidate-deps-array (populate-candidate-deps-array subst-candidates dag-array dag-len)))
  :hints (("Goal" :in-theory (enable populate-candidate-deps-array))))

(local
 (defthm all-myquotep-becomes-all-consp-when-all-dargp
   (implies (all-dargp items)
            (equal (all-myquotep items)
                   (all-consp items)))
   :hints (("Goal" :in-theory (enable all-myquotep all-consp all-dargp)))))

(defthm alen1-of-populate-candidate-deps-array
  (implies (and (subst-candidate-listp subst-candidates)
                (consp subst-candidates)
                (not (all-consp (strip-cadrs subst-candidates)))
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (or (endp subst-candidates)
                    (<= (maxelem (strip-cars subst-candidates))
                        (+ -1 dag-len)))
                (< (largest-non-quotep (strip-cadrs subst-candidates))
                   dag-len))
           (equal (alen1 'candidate-deps-array (populate-candidate-deps-array subst-candidates dag-array dag-len))
                  (+ 1 (largest-non-quotep (strip-cadrs subst-candidates)))))
  :hints (("Goal" :in-theory (enable populate-candidate-deps-array))))


(local
 (defthmd true-list-when-nat-listp
   (implies (nat-listp x)
            (true-listp x))))

(local (in-theory (disable MEMBER-EQUAL NAT-LISTP STRIP-CADRS))) ;prevent inductions

(local
 (defthm <-of-cadr-of-car-when-ALL-DARGP-LESS-THAN-of-strip-cadrs
   (IMPLIES (AND (ALL-DARGP-LESS-THAN (STRIP-CADRS SUBST-CANDIDATES)
                                      bound)
                 (NOT (CONSP (CADR (CAR SUBST-CANDIDATES))))
                 (consp SUBST-CANDIDATES))
            (< (CADR (CAR SUBST-CANDIDATES))
               bound))
   :hints (("Goal" :in-theory (enable STRIP-CADRS)))))

(local
 ;; to expose the cdr to other rules
 (defthm strip-cadrs-of-cdr
   (equal (strip-cadrs (cdr x))
          (cdr (strip-cadrs x)))
   :hints (("Goal" :in-theory (enable strip-cadrs)))))

(defun memberp-assuming-sorted-<= (a x)
  (declare (xargs :guard (and (rationalp a)
                              (rational-listp x)
                              (sortedp-<= x))))
  (if (atom x)
      nil
    (let ((x0 (car x)))
      (if (= a x0)
          t
        (if (< a x0)
            ;; since x is sorted, a cannot appear in it
            nil
          ;; we know that a>x0.
          ;; keep looking:
          (memberp-assuming-sorted-<= a (rest x)))))))

(defun disjointp-assuming-sorted-<= (x y)
  (declare (xargs :guard (and (rational-listp x)
                              (sortedp-<= x)
                              (rational-listp y)
                              (sortedp-<= y))
                  :measure (+ (len x)
                              (len y))))
  (if (or (atom x)
          (atom y))
      t
    (let ((x0 (car x))
          (y0 (car y)))
      (if (= x0 y0)
          nil ;not disjoint
        (if (< x0 y0)
            ;; since y is sorted, (car x) cannot be in y, so we skip it:
            (disjointp-assuming-sorted-<= (rest x) y)
          ;; We know (car y) < (car x).
          ;; since x is sorted, (car y) cannot be in x, so we skip it:
          (disjointp-assuming-sorted-<= x (rest y)))))))

;; Returns a list of subst-candidates suitable for simultaneous checking (no var in the set depends on any other vars in the set, or on itself).
;; TODO: Stop once we have a nice chunk of vars to substitute (100?).
;; TODO: Can we mark vars to avoid in an array of bits, to avoid operations on sorted lists?
(defund find-simultaneous-subst-candidates (subst-candidates
                                            candidate-deps-array ;tells us what vars the equated-nodenums depend on
                                            subst-candidates-acc ; candidates we have already decided to added to the set
                                            nodenums-of-vars-already-added ;var nodenums of the candidates in subst-candidates-acc, sorted
                                            nodenums-of-vars-to-avoid ;all the vars on which the candidates in subst-candidates-acc depend, sorted
                                            )
  (declare (xargs :guard (and (subst-candidate-listp subst-candidates)
                              (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                              (all-dargp-less-than (strip-cadrs subst-candidates) (alen1 'candidate-deps-array candidate-deps-array))
                              (nat-listp nodenums-of-vars-already-added)
                              (sortedp-<= nodenums-of-vars-already-added)
                              (nat-listp nodenums-of-vars-to-avoid)
                              (sortedp-<= nodenums-of-vars-to-avoid))
                  :guard-hints (("Goal" :do-not '(generalize eliminate-destructors)
                                 :in-theory (e/d (true-list-when-nat-listp
                                                  integerp-when-natp
                                                  subst-candidatep-of-car
                                                  natp-of-car-when-subst-candidatep
                                                  ALL->=-LEN-of-2-when-SUBST-CANDIDATE-LISTP
                                                  consp-when-subst-candidatep
                                                  consp-of-cdr-when-subst-candidatep
                                                  natp-of-cadr-when-subst-candidatep
                                                  <=-of-0-when-0-natp
                                                  rational-listp-when-nat-listp
                                                  all-rationalp-when-all-natp)
                                                 (natp))))))
  (if (endp subst-candidates)
      subst-candidates-acc
    (let* ((subst-candidate (first subst-candidates))
           (this-var-nodenum (first subst-candidate))
           (equated-nodenum-or-constant (second subst-candidate))
           ;; sorted:
           (nodenums-this-var-depends-on (if (consp equated-nodenum-or-constant) ;check for quotep
                                             nil
                                           (aref1 'candidate-deps-array candidate-deps-array equated-nodenum-or-constant))))
      (if (and
           ;; Makes sure no already-selected candidate depends on this var:
           (not (memberp-assuming-sorted-<= this-var-nodenum nodenums-of-vars-to-avoid))
           ;; Makes sure this var doesn't depend on any of the already-selected candidates:
           (disjointp-assuming-sorted-<= nodenums-this-var-depends-on nodenums-of-vars-already-added)
           ;; Makes sure the var doesn't depend on itself (tested last because it's rare):
           (not (memberp-assuming-sorted-<= this-var-nodenum nodenums-this-var-depends-on)))
          ;; Add this candidate:
          (find-simultaneous-subst-candidates (rest subst-candidates)
                                              candidate-deps-array
                                              (cons subst-candidate subst-candidates-acc)
                                              ;; todo: can dups even occur? maybe if a var is equated to 2 things?
                                              (merge-<-and-remove-dups (list this-var-nodenum) nodenums-of-vars-already-added)
                                              (merge-<-and-remove-dups nodenums-this-var-depends-on nodenums-of-vars-to-avoid))
        ;; Don't add this candidate:
        (find-simultaneous-subst-candidates (rest subst-candidates)
                                            candidate-deps-array
                                            subst-candidates-acc
                                            nodenums-of-vars-already-added
                                            nodenums-of-vars-to-avoid)))))

(defthm subst-candidate-listp-of-find-simultaneous-subst-candidates
  (implies (and (subst-candidate-listp subst-candidates)
                (subst-candidate-listp subst-candidates-acc))
           (subst-candidate-listp (find-simultaneous-subst-candidates subst-candidates candidate-deps-array subst-candidates-acc nodenums-of-vars-already-added nodenums-of-vars-to-avoid)))
  :hints (("Goal" :in-theory (enable find-simultaneous-subst-candidates
                                     len-of-cadr-when-subst-candidatep
                                     ))))

(defthm all-dargp-less-than-of-strip-cadrs-of-find-simultaneous-subst-candidates
  (implies (and (all-dargp-less-than (strip-cadrs subst-candidates) bound)
                (all-dargp-less-than (strip-cadrs subst-candidates-acc) bound))
           (all-dargp-less-than (strip-cadrs (find-simultaneous-subst-candidates subst-candidates candidate-deps-array subst-candidates-acc nodenums-of-vars-already-added nodenums-of-vars-to-avoid))
                                bound))
  :hints (("Goal" :in-theory (enable find-simultaneous-subst-candidates
                                     len-of-cadr-when-subst-candidatep
                                     STRIP-CADRS
                                     ))))

(defthm SUBSETP-EQUAL-of-strip-caddrs-of-find-simultaneous-subst-candidates
  (implies (and (subsetp-equal (strip-caddrs subst-candidates) set)
                (subsetp-equal (strip-caddrs subst-candidates-acc) set))
           (SUBSETP-EQUAL (strip-caddrs (find-simultaneous-subst-candidates subst-candidates candidate-deps-array subst-candidates-acc nodenums-of-vars-already-added nodenums-of-vars-to-avoid))
                          set))
  :hints (("Goal" :in-theory (enable find-simultaneous-subst-candidates))))

;; Drops any subst-candidates whose var nodes are greater than max-literal-nodenum
(defund drop-irrelevant-subst-candidates (subst-candidates max-literal-nodenum acc)
  (declare (xargs :guard (and (subst-candidate-listp subst-candidates)
                              (natp max-literal-nodenum)
                              (subst-candidate-listp acc))))
  (if (endp subst-candidates)
      acc ;(reverse-list acc)
    (let* ((subst-candidate (first subst-candidates))
           (nodenum-of-var (first subst-candidate)))
      (if (< max-literal-nodenum nodenum-of-var)
          ;; Drop it:
          (drop-irrelevant-subst-candidates (rest subst-candidates) max-literal-nodenum acc)
        ;; Keep it:
        (drop-irrelevant-subst-candidates (rest subst-candidates) max-literal-nodenum (cons subst-candidate acc))
        ))))

(defthm subst-candidate-listp-of-drop-irrelevant-subst-candidates
  (implies (and (subst-candidate-listp subst-candidates)
                (subst-candidate-listp acc))
           (subst-candidate-listp (drop-irrelevant-subst-candidates subst-candidates max-literal-nodenum acc)))
  :hints (("Goal" :in-theory (enable drop-irrelevant-subst-candidates))))

(defthm all-<=-of-strip-cars-of-drop-irrelevant-subst-candidates
  (implies (and (subst-candidate-listp subst-candidates)
                (subst-candidate-listp acc)
                (all-<= (strip-cars acc) max-literal-nodenum))
           (all-<= (strip-cars (drop-irrelevant-subst-candidates subst-candidates max-literal-nodenum acc))
                   max-literal-nodenum))
  :hints (("Goal" :in-theory (enable drop-irrelevant-subst-candidates))))

;drop?
(defthm all-<-of-strip-cars-of-drop-irrelevant-subst-candidates
  (implies (and (all-< (strip-cars subst-candidates) bound)
                (all-< (strip-cars acc) bound))
           (all-< (strip-cars (drop-irrelevant-subst-candidates subst-candidates max-literal-nodenum acc)) bound))
  :hints (("Goal" :in-theory (enable drop-irrelevant-subst-candidates))))

(defthm all-<-of-strip-cars-of-drop-irrelevant-subst-candidates-2
  (implies (and (< max-literal-nodenum bound)
                (natp bound)
                (natp max-literal-nodenum)
                (all-< (strip-cars acc) bound))
           (all-< (strip-cars (drop-irrelevant-subst-candidates subst-candidates max-literal-nodenum acc))
                  bound))
  :hints (("Goal" :in-theory (enable drop-irrelevant-subst-candidates))))

(defthm all-dargp-less-than-of-strip-cadrs-of-drop-irrelevant-subst-candidates
  (implies (and (subst-candidate-listp subst-candidates)
                ;(subst-candidate-listp acc)
                ;(all-<= (strip-cars acc) max-literal-nodenum)
                (all-dargp-less-than (strip-cadrs subst-candidates) bound)
                (all-dargp-less-than (strip-cadrs acc) bound))
           (all-dargp-less-than (strip-cadrs (drop-irrelevant-subst-candidates subst-candidates max-literal-nodenum acc))
                                bound))
  :hints (("Goal" :in-theory (enable drop-irrelevant-subst-candidates STRIP-CADRS))))

;; Update translation-array to indicate, for each subst-candidate, that its var is to be replaced by the thing it is equal to:
(defund mark-replacements (subst-candidates translation-array)
  (declare (xargs :guard (and (subst-candidate-listp subst-candidates)
                              (array1p 'translation-array translation-array)
                              (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                              (all-< (strip-cars subst-candidates) (alen1 'translation-array translation-array)))
                  :guard-hints (("Goal" :in-theory (enable dargp-of-cadr-when-subst-candidatep)))
                  ))
  (if (endp subst-candidates)
      translation-array
    (let* ((subst-candidate (first subst-candidates))
           (nodenum-of-var (first subst-candidate))
           (equated-nodenum-or-constant (second subst-candidate)))
      (mark-replacements (rest subst-candidates)
                         (aset1 'translation-array translation-array nodenum-of-var equated-nodenum-or-constant)))))

(defthm array1p-of-mark-replacements
  (implies (and (subst-candidate-listp subst-candidates)
                (array1p 'translation-array translation-array)
                ;(translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< (strip-cars subst-candidates) (alen1 'translation-array translation-array)))
           (array1p 'translation-array (mark-replacements subst-candidates translation-array)))
  :hints (("Goal" :in-theory (enable mark-replacements natp-of-car-when-subst-candidatep))))

(defthm alen1-of-mark-replacements
  (implies (and (subst-candidate-listp subst-candidates)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< (strip-cars subst-candidates) (alen1 'translation-array translation-array)))
           (equal (alen1 'translation-array (mark-replacements subst-candidates translation-array))
                  (alen1 'translation-array translation-array)))
  :hints (("Goal" :in-theory (enable mark-replacements
                                     natp-of-car-when-subst-candidatep
                                     dargp-of-cadr-when-subst-candidatep))))

(defthm translation-arrayp-aux-of-mark-replacements
  (implies (and (subst-candidate-listp subst-candidates)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< (strip-cars subst-candidates) (alen1 'translation-array translation-array)))
           (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) (mark-replacements subst-candidates translation-array)))
  :hints (("Goal" :in-theory (enable mark-replacements
                                     dargp-of-cadr-when-subst-candidatep
                                     ))))

(defthm translation-arrayp-aux-of-mark-replacements-gen
  (implies (and (<= TOP-NODENUM-TO-CHECK (+ -1 (alen1 'translation-array translation-array)))
                (natp TOP-NODENUM-TO-CHECK)
                (subst-candidate-listp subst-candidates)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (all-< (strip-cars subst-candidates) (alen1 'translation-array translation-array)))
           (translation-arrayp-aux TOP-NODENUM-TO-CHECK (mark-replacements subst-candidates translation-array)))
  :hints (("Goal" :in-theory (enable mark-replacements dargp-of-cadr-when-subst-candidatep))))

(defthm dargp-less-than-of-cadr-of-car-when-all-dargp-less-than-of-strip-cadrs
  (implies (and (all-dargp-less-than (strip-cadrs x) bound)
                (consp x))
           (dargp-less-than (cadr (car x)) bound))
  :hints (("Goal" :in-theory (enable all-dargp-less-than strip-cadrs))))

(defthm <-of-car-of-car-when-all-<-of-strip-cars
  (implies (and (all-< (strip-cars x) bound)
                (consp x))
           (< (car (car x)) bound))
  :hints (("Goal" :in-theory (enable all-< strip-cars))))

(defthm bounded-translation-arrayp-aux-of-mark-replacements
  (implies (and (all-dargp-less-than (strip-cadrs subst-candidates) bound)
                (subst-candidate-listp subst-candidates)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array bound)
                (all-< (strip-cars subst-candidates) (alen1 'translation-array translation-array))
                (all-< (strip-cars subst-candidates) bound))
           (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) (mark-replacements subst-candidates translation-array) bound))
  :hints (("Goal" :in-theory (enable mark-replacements dargp-of-cadr-when-subst-candidatep))))

(defthm bounded-translation-arrayp-aux-of-mark-replacements-gen
  (implies (and (<= top-nodenum-to-check (+ -1 (alen1 'translation-array translation-array)))
                (natp top-nodenum-to-check)
                (all-dargp-less-than (strip-cadrs subst-candidates) bound)
                (subst-candidate-listp subst-candidates)
                (array1p 'translation-array translation-array)
                (translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array)
                (bounded-translation-arrayp-aux (+ -1 (alen1 'translation-array translation-array)) translation-array bound)
                (all-< (strip-cars subst-candidates) (alen1 'translation-array translation-array))
                (all-< (strip-cars subst-candidates) bound))
           (bounded-translation-arrayp-aux top-nodenum-to-check (mark-replacements subst-candidates translation-array) bound))
  :hints (("Goal" :in-theory (enable mark-replacements dargp-of-cadr-when-subst-candidatep))))


;;;
;;; substitute-var-set
;;;

;; Try to apply a simultaneous set of variable substitutioms.  Uses literals that are each a (negated) equality involving a variable (recall that a literal can be safely assumed false when rewriting other literals).
;; Requires that the variable is equated to some term not involving itself (to prevent loops).
;; Such equalities are used to substitute in all the other literals.  The literals representing the equalities are all dropped, eliminating those variables from the DAG.
;; Simutaneous substitutions are attempted for a set of subst candidates where none of the vars replaced is equated to a subdag that mentions any of the other vars.
;; Returns (mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; Doesn't change any existing nodes in the dag (just builds new ones).
(defund substitute-var-set (literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len))
                  ;; clean up:
                  :guard-hints (("Goal" :in-theory (e/d (;car-becomes-nth-of-0
                                                         <-of-nth-when-all-<
                                                         ;;check-for-var-subst-literal2
                                                         find-var-and-expr-to-subst2
                                                         ensure-substitutable-var2
                                                         consp-of-cdr
                                                         integerp-when-dargp
                                                         <=-of-0-when-dargp
                                                         <-when-dargp-less-than
                                                         ALL->=-LEN-of-3-when-SUBST-CANDIDATE-LISTP
                                                         ALL->=-LEN-of-2-when-SUBST-CANDIDATE-LISTP
                                                         <-OF-+-OF-1-WHEN-INTEGERS
                                                         all-integerp-when-nat-listp
                                                         NATP-OF-+-OF-1
                                                         ACL2-NUMBERP-WHEN-NATP)
                                                        (natp
                                                         ;;cons-nth-0-nth-1 cons-of-nth-and-nth-plus-1 ;todo: why do these cause mv-nths to show up in appropriate places?
                                                         dargp-less-than
                                                         dargp-less-than-when-not-consp-cheap))))))
  (let ((subst-candidates (subst-candidates literal-nodenums dag-array dag-len 300 nil))) ;; limit for now -- todo: what if all of the 500 have self loops?
    (if (not subst-candidates)
        ;; No change:
        (mv (erp-nil) nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
      (b* (;(- (cw "  ~x0 subst candidates.~%" (len subst-candidates)))
           (num-candidates (len subst-candidates))
           (subst-candidates (if (all-consp (strip-cadrs subst-candidates)) ;check whether all the equated things are constants ;todo optimize
                                 ;; All vars are equated to constants, so we don't need the deps array and can substitute them all at once:
                                 subst-candidates
                               (let ( ;; Find a set of candidates that can be substituted together (may find none due to self deps)
                                     (candidate-deps-array (populate-candidate-deps-array subst-candidates dag-array dag-len)))
                                 (find-simultaneous-subst-candidates subst-candidates candidate-deps-array nil nil nil)))))
        (if (not subst-candidates)
            ;; No change:
            (prog2$ (cw "  No candidates are suitable for substitution.~%")
                    (mv (erp-nil) nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
          (b* ((- (cw " (Applying ~x0 substitutions from ~x1 candidates.~%" (len subst-candidates) num-candidates)) ;todo: print them?
               ;; (and print (cw "~%(Using ~x0 to replace ~x1, which is ~x2.~%" literal-nodenum var
               ;;                          (if (consp nodenum-or-quotep-to-put-in)
               ;;                              nodenum-or-quotep-to-put-in
               ;;                            (aref1 'dag-array dag-array nodenum-or-quotep-to-put-in))))
               ;; Remove the literals for any equalities we using to substitute (todo: make use of the fact that each item appears only once?):
               ;; todo: optimize (avoid the strip-caddrs, maybe even sort?):
               (literal-nodenums (set-difference-equal ;todo: optimize for ints?
                                  literal-nodenums (strip-caddrs subst-candidates)))
               ((when (not literal-nodenums))
                (cw "NOTE: All literals dropped during substitution.  Clause is unprovable.")
                (mv (erp-nil) nil t nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               (sorted-literal-nodenums (merge-sort-< literal-nodenums)) ;; todo: somehow avoid doing this sorting over and over?  keep the list sorted?
               (max-literal-nodenum (car (last sorted-literal-nodenums)))
               ;; Drop any candidate for which the var to be replaced does not appear in any literal (needed since we size the array according to max-literal-nodenum) (todo: when exactly is the best time to deal with this?)
               (subst-candidates (drop-irrelevant-subst-candidates subst-candidates max-literal-nodenum nil))
               (translation-array (make-empty-array 'translation-array (+ 1 max-literal-nodenum)))
               ;; Mark all the nodenums to be replaced:
               (translation-array (mark-replacements subst-candidates translation-array))
               ;; Rebuild all the literals, and their supporters, with the substitution applied:
               ((mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                ;; generalize this name, since now there are several substs:
                (rebuild-nodes-with-var-subst sorted-literal-nodenums ;; initial worklist
                                              translation-array
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               ((when erp) (mv erp nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               ;; Look up the possibly-new nodes that represent the remaining literals:
               ((mv provedp changed-literal-nodenums unchanged-literal-nodenums)
                (translate-literals literal-nodenums ;; could use sorted-literal-nodenums instead
                                    translation-array
                                    nil nil))
               ((when provedp)
                (mv (erp-nil)
                    t ; provedp
                    t ; changep
                    nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
               ;; We put the changed nodes first, in the hope that we will use them to
               ;; substitute next, creating a slightly larger term, and so on.  The
               ;; unchanged-literal-nodenums here got reversed wrt the input, so if
               ;; we had a bad ordering last time, we may have a good ordering this
               ;; time:
               (new-literal-nodenums (append changed-literal-nodenums unchanged-literal-nodenums))
               ;; todo: avoid the call of len (compute it during the pass through the literals above?):
               ;; Close paren matched the open paren printed above:
               (- (and print (cw "  ~x0 literals left, dag len is ~x1)~%" (len new-literal-nodenums) dag-len)))
               )
            (mv (erp-nil)
                nil ; provedp
                t ;changep
                new-literal-nodenums
                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))))

(defthm len-of-set-difference-equal
  (<= (len (set-difference-equal x y))
      (len x))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm len-of-set-difference-equal-linear
  (<= (len (set-difference-equal x y))
      (len x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm equal-of-len-of-set-difference-equal-and-len-same
  (equal (equal (len (set-difference-equal x y))
                (len x))
         (not (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal intersection-equal))))

(defthm len-of-mv-nth-3-of-substitute-var-set
  (implies (and ;(consp literal-nodenums)
                (mv-nth 2 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
           (< (len (mv-nth 3 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
              (len literal-nodenums)))
  :hints (("Goal" :in-theory (enable substitute-var-set
                                     intersection-equal-when-subsetp-equal-iff))))

(defthm len-of-mv-nth-3-of-substitute-var-set-gen
  (implies (and ;(consp literal-nodenums)
            (<= (len literal-nodenums) bound)
                (mv-nth 2 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
           (< (len (mv-nth 3 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
              bound))
  :hints (("Goal" :in-theory (enable substitute-var-set
                                     intersection-equal-when-subsetp-equal-iff))))

(defthm mv-nth-3-of-substitute-var-set-when-not-consp
  (implies (not (consp literal-nodenums))
           (equal (mv-nth 3 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
                  literal-nodenums))
  :hints (("Goal" :in-theory (enable substitute-var-set))))

;;for the def-dag-builder-theorems just below (todo: should not be needed?):
(local (in-theory (enable check-for-var-subst-literal2 consp-of-cdr
                          ALL-<-OF-+-OF-1
                          ;;car-becomes-nth-of-0
                          <-of-nth-when-all-<
                          ;;check-for-var-subst-literal2
                          find-var-and-expr-to-subst2
                          ensure-substitutable-var2
                          consp-of-cdr
                          integerp-when-dargp
                          <=-of-0-when-dargp
                          <-when-dargp-less-than
                          ALL->=-LEN-of-3-when-SUBST-CANDIDATE-LISTP
                          ALL->=-LEN-of-2-when-SUBST-CANDIDATE-LISTP
                          <-OF-+-OF-1-WHEN-INTEGERS
                          NATP-OF-+-OF-1
                          ACL2-NUMBERP-WHEN-NATP)))

(def-dag-builder-theorems
  (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)
  (mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((nat-listp literal-nodenums)
         (all-< literal-nodenums dag-len))
  :recursivep nil
  ;; TODO: Why doesn't this work without the in-theory event above?
  ;; :hints (("Goal" :in-theory (enable substitute-var-set
  ;;                                    check-for-var-subst-literal2)))
  )

;; (defthm <=-of-mv-nth-5-of-substitute-var-set
;;   (implies (and (mv-nth 2 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
;;                 (subsetp-equal literal-nodenums))
;;            (<= (mv-nth 5 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
;;                2147483646))
;;   :hints (("Goal" :in-theory (enable SUBSTITUTE-VAR-SET))))

(defthm nat-listp-of-mv-nth-3-of-substitute-var-set
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len))
           (nat-listp (mv-nth 3 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))))
  :hints (("Goal" :in-theory (enable substitute-var-set))))

(defthm true-listp-of-mv-nth-3-of-substitute-var-set
  (implies (true-listp literal-nodenums)
           (true-listp (mv-nth 3 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable substitute-var-set))))

(defthm all-<-of-mv-nth-3-of-substitute-var-set
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (not (mv-nth 0 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print)))
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len))
           (all-< (mv-nth 3 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
                  (mv-nth 5 (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))))
  :hints (("Goal" :in-theory (enable substitute-var-set))))

;; Repeatedly get rid of sets of vars by substitution.
;; Returns (mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;; Doesn't change any nodes if prover-depth > 0.
(defund substitute-vars2 (literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth
                                           initial-dag-len ;; only used for deciding when to crunch
                                           changep-acc)
  (declare (xargs :guard (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len)
                              (natp prover-depth)
                              (posp initial-dag-len)
                              (booleanp changep-acc))
                  :measure (len literal-nodenums)
                  :guard-hints (("Goal" :in-theory (enable rationalp-when-natp)))))
  (b* ( ;; Always crunch if we can.  This is important for performance, since populate-candidate-deps-array is expensive and works best if there are no extra nodes in the dag.
       (crunchp (and (= prover-depth 0) ;; can't crunch if prover-depth > 0 since that would change existing nodes
                     (consp literal-nodenums) ;;can't crunch if no nodenums (can this happen?)
                     ))
       ((mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (maybe-crunch-dag-array2 crunchp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ((when erp)
        (mv erp nil nil literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ;; Try to subst a var.  TODO: Allow this to evaluate ground terms that arise when substituting.
       ((mv erp provedp changep literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (substitute-var-set literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print))
       ((when erp) (mv erp nil changep-acc literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       ((when provedp) (mv (erp-nil) t t literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
    (if (or (not changep)
            (endp literal-nodenums) ;todo: think about this
            )
        ;; No more vars to susbt:
        (mv (erp-nil)
            nil
            changep-acc
            literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
      (b* (((mv erp literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (if (and (= 0 prover-depth)
                     t ;; (> (/ dag-len initial-dag-len)
                     ;;  ;; todo: what is the best threshold ratio to use here?:
                     ;;  10)
                     ) ;; OLD: crunching is less important now that we substitute first with lits that were just rebuilt
                ;; Crunch the dag:
                (b* ((- (cw " (Crunching: ...")) ;paren closed below
                     ((mv dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist literal-nodenums)
                      (crunch-dag-array2-with-indices 'dag-array dag-array dag-len 'dag-parent-array literal-nodenums))
                     ;; TODO: Prove that this can't happen.  Need to know that
                     ;; build-reduced-nodes maps all of the literal-nodenums to
                     ;; nodenums (not constants -- currently)
                     ((when (not (and (rational-listp literal-nodenums) ;todo: using nat-listp here didn't work
                                      (all-< literal-nodenums dag-len))))
                      (er hard? 'substitute-vars2 "Bad nodenum after crunching.")
                      (mv (erp-t) literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                     (- (cw "Done (new dag-len: ~x0).)~%" dag-len)))
                  (mv (erp-nil) literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
              ;; No change:
              (mv (erp-nil) literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
           ((when erp) (mv erp nil changep-acc literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
        ;; At least one var was substituted away, so keep going
        (substitute-vars2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth initial-dag-len t)))))

(defthm substitute-vars2-return-type
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp prover-depth)
                (natp num)
                (booleanp changep-acc))
           (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (substitute-vars2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth initial-dag-len changep-acc)
             (implies (not erp)
                      (and (booleanp changep)
                           (booleanp provedp)
                           (nat-listp new-literal-nodenums)
                           (all-natp new-literal-nodenums) ;follows from the above
                           (true-listp new-literal-nodenums) ;follows from the above
                           (all-< new-literal-nodenums new-dag-len)
                           (wf-dagp 'dag-array new-dag-array new-dag-len 'dag-parent-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                           (implies (< 0 prover-depth)
                                    (<= dag-len new-dag-len))))))
  :hints (("Goal" :in-theory (enable substitute-vars2))))

(defthm substitute-vars2-return-type-corollary
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp prover-depth)
                (natp num)
                (booleanp changep-acc))
           (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (substitute-vars2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth initial-dag-len changep-acc)
             (declare (ignore provedp changep new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (implies (not erp)
                      (implies (< 0 prover-depth)
                               (<= dag-len new-dag-len)))))
  :rule-classes :linear
  :hints (("Goal" :use (substitute-vars2-return-type)
           :in-theory (disable substitute-vars2-return-type))))

(defthm substitute-vars2-return-type-2
  (implies (true-listp literal-nodenums)
           (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (substitute-vars2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth initial-dag-len changep-acc)
             (declare (ignore erp provedp changep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (true-listp new-literal-nodenums)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable substitute-vars2))))

(defthm substitute-vars2-return-type-3
  (implies (and (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (natp prover-depth)
                (natp num)
                (booleanp changep-acc))
           (mv-let (erp provedp changep new-literal-nodenums new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (substitute-vars2 literal-nodenums dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist print prover-depth initial-dag-len changep-acc)
             (declare (ignore provedp changep new-literal-nodenums new-dag-array new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (implies (not erp)
                      (natp new-dag-len))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (substitute-vars2) (natp)))))
