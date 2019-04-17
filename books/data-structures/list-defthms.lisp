; lists-defthms.lisp -- theorems about functions in the theory of lists
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com)
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

; Includes tweaks made by Mihir Mehta 4/2019 for a change to the
; definition of take.

(in-package "ACL2")
(include-book "list-defuns")

;; We need this much arithmetic to get some of the following
;; theorems proved, e.g., put-seg-non-recursive, len-nthcdr.

(local (include-book "arithmetic/equalities" :dir :system))

; ------------------------------------------------------------
; Equality Trichotomy
; ------------------------------------------------------------

; Rewrite the EQL and EQ versions of various functions to
; the EQUAL version. This way, we can build one set of rules about
; the EQUAL functions.

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm member->member-equal
;   (equal (member x l)
;        (member-equal x l)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm member-eq->member-equal
;   (equal (member-eq x l)
;          (member-equal x l)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm remove->remove-equal
;   (equal (remove x l)
;        (remove-equal x l)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm remove-eq->remove-equal
;   (equal (remove-eq x l)
;          (remove-equal x l)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm remove-duplicates-eql->remove-duplicates-equal
;   (equal (remove-duplicates-eql l)
;          (remove-duplicates-equal l)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm remove-duplicates->remove-duplicates-equal
;   (implies (true-listp l)
;            (equal (remove-duplicates l)
;                   (remove-duplicates-equal l))))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm remove-duplicates-eq->remove-duplicates-equal
;   (equal (remove-duplicates-eq l)
;          (remove-duplicates-equal l)))

(defthm initial-sublistp->initial-sublistp-equal
  (equal (initial-sublistp a b)
         (initial-sublistp-equal a b)))

(defthm initial-sublistp-eq->initial-sublistp-equal
  (equal (initial-sublistp-eq a b)
         (initial-sublistp-equal a b)))

(defthm memberp->memberp-equal
  (equal (memberp x l)
         (memberp-equal x l)))

(defthm memberp-eq->memberp-equal
  (equal (memberp-eq x l)
         (memberp-equal x l)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm no-duplicatesp->no-duplicatesp-equal
;   (iff (no-duplicatesp l)
;        (no-duplicatesp-equal l)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm no-duplicatesp-eq->no-duplicatesp-equal
;   (iff (no-duplicatesp-eq l)
;        (no-duplicatesp-equal l)))

(local
 (defthm occurrences-ac->occurrences-equal-ac
   (equal (occurrences-ac x l ac)
          (occurrences-equal-ac x l ac))))

(defthm occurrences->occurrences-equal
  (equal (occurrences x l)
         (occurrences-equal x l)))

(local
 (defthm occurrences-eq-ac->occurrences-equal-ac
   (equal (occurrences-eq-ac x l ac)
          (occurrences-equal-ac x l ac))))

(defthm occurrences-eq->occurrences-equal
  (equal (occurrences-eq x l)
         (occurrences-equal x l)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (local
;  (defthm position-ac->position-equal-ac
;    (equal (position-ac x l ac)
;           (position-equal-ac x l ac))))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm position->position-equal
;   (equal (position x l)
;          (position-equal x l)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (local
;  (defthm position-eq-ac->position-equal-ac
;    (equal (position-eq-ac x l ac)
;           (position-equal-ac x l ac))))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm position-eq->position-equal
;   (implies (true-listp l)
;            (equal (position-eq x l)
;                   (position-equal x l))))

; ------------------------------------------------------------
; CONSP type prescription and rewrite lemmas
; ------------------------------------------------------------

(defthm consp-append
  (equal (consp (append a b))
         (or (consp a)
             (consp b)))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
                       (implies (consp a)
                                (consp (append a b))))
   (:type-prescription :corollary
                       (implies (consp b)
                                (consp (append a b))))))

(defthm consp-revappend
  (equal (consp (revappend a b))
         (or (consp a)
             (consp b)))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
                       (implies (consp a)
                                (consp (revappend a b))))
   (:type-prescription :corollary
                       (implies (consp b)
                                (consp (revappend a b))))))

(defthm consp-reverse
  (equal (consp (reverse a))
         (consp a))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
                       (implies (consp a)
                                (consp (reverse a))))))

(local
 (defthm consp-first-n-ac
   (equal (consp (first-n-ac i l ac))
          (if (zp i) (consp ac) t))
   :rule-classes ((:rewrite)
                  (:type-prescription :corollary
                                      (implies (or (not (zp i))
                                                   (consp ac))
                                               (consp (first-n-ac i l ac)))))
   :hints (("Goal" :induct (first-n-ac i l ac)))))

(local
 (defthm consp-take
   (equal (consp (take n l))
          (not (zp n)))
   :rule-classes ((:rewrite)
                  (:type-prescription :corollary
                                      (implies (not (zp n))
                                               (consp (take n l)))))))

(defthm consp-butlast
; Changed for ACL2 Version 5.1 by Matt Kaufmann, due to change in the
; definition of butlast (which applies nfix to n).
  (equal (consp (butlast lst n))
         (not (zp (- (len lst) (nfix n)))))
  :rule-classes ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (and (natp n)
                                (not (zp (- (len lst) n))))
                           (consp (butlast lst n)))))
  :hints (("Goal" :do-not-induct t)))

(defthm consp-firstn
  (equal (consp (firstn n l))
         (and (not (zp n))
              (consp l)))
  :hints (("Goal" :expand (firstn n l)))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
                       (implies (and (not (zp n))
                                     (consp l))
                                (consp (firstn n l))))))

(defthm consp-last
  (equal (consp (last l))
         (consp l))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary
                                     (implies (consp l)
                                              (consp (last l))))))

(defthm consp-make-list-ac
  (equal (consp (make-list-ac n val ac))
         (or (not (zp n))
             (consp ac)))
  :hints (("Goal" :expand (make-list-ac n val ac)))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
    (implies (and (not (zp n))
                  (consp ac))
             (consp (make-list-ac n val ac))))))

(defthm consp-member-equal
  (or (consp (member-equal x l))
      (equal (member-equal x l) nil))
  :rule-classes ((:type-prescription)
                 (:rewrite :corollary
                           (iff (not (consp (member-equal x l)))
                                (equal (member-equal x l) nil)))))

(local
 (defthm nthcdr-nil
   (implies (and (integerp n)
                 (<= 0 n))
            (not (nthcdr n nil)))))

(defthm consp-nthcdr
  (iff (consp (nthcdr n l))
       (< (nfix n) (len l)))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
                       (implies (< (nfix n) (len l))
                                (consp (nthcdr n l))))))

(defthm consp-nth-seg
  (implies (<= (+ i j) (len l))
           (equal (consp (nth-seg i j l))
                  (and (consp l)
                       (not (zp j)))))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
                       (implies (and (consp l)
                                     (not (zp j))
                                     (<= (+ i j) (len l)))
                                (consp (nth-seg i j l))))))

(defthm consp-put-nth
  (equal (consp (put-nth n v l))
         (consp l))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
                       (implies (consp l)
                                (consp (put-nth n v l))))))

(defthm consp-put-seg
  (equal (consp (put-seg i seg l))
         (consp l))
  :rule-classes ((:rewrite)
   (:type-prescription :corollary
                       (implies (consp l)
                                (consp (put-seg i seg l))))))

(defthm consp-subseq
  (implies (and (true-listp list)
                (integerp start)
                (<= 0 start)
                (or (null end)
                    (and (integerp end)
                         (<= 0 end))))
           (iff (consp (subseq list start end))
                (< start (if (null end)
                             (len list)
                           end))))
  :hints (("Goal" :do-not-induct t :in-theory (disable take))))

;; UPDATE-NTH is always a CONS

; ------------------------------------------------------------
; TRUE-LISTP type prescription and rewrite rules
; ------------------------------------------------------------

(defthm true-listp-append-rewrite
  (equal (true-listp (append a b))
         (true-listp b))
  :rule-classes ((:rewrite)

; Jared removed this corollary because (1) it's slow, and (2) there's an identical
; rule that is built into ACL2, TRUE-LISTP-APPEND.
;;               (:type-prescription :corollary
;;                                   (implies (true-listp b)
;;                                            (true-listp (append a b))))
  ))

(defthm true-listp-revappend
  (equal (true-listp (revappend a b))
         (true-listp b))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
                       (implies (true-listp b)
                                (true-listp (revappend a b))))))

(defthm true-listp-reverse
  (implies (listp a)
           (true-listp (reverse a)))
  :rule-classes (:type-prescription))

; Matt K. mod: The following two lemmas are now type-prescription rules built
; into ACL2.  So these are now only rewrite rules.

(local
   (defthm true-listp-first-n-ac-rewrite
     (implies (true-listp ac)
              (true-listp (first-n-ac i l ac)))
     :rule-classes (:rewrite) ; Matt K. mod, explained above
     :hints (("Goal" :induct (first-n-ac i l ac)))))

(local
 (defthm true-listp-take-rewrite
   (true-listp (take n l))
   :rule-classes (:rewrite))) ; Matt K. mod, explained above

(defthm true-listp-butlast
    (true-listp (butlast lst n))
    :rule-classes (:rewrite :type-prescription))

; FIRSTN is always a true list

(defthm true-listp-last
  (equal (true-listp (last l))
         (true-listp l))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
                       (implies (true-listp l)
                                (true-listp (last l))))))

(defthm true-listp-make-list-ac
  (equal (true-listp (make-list-ac n val ac))
         (true-listp ac))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
    (implies (true-listp ac)
             (true-listp (make-list-ac n val ac))))))

(defthm true-listp-member-equal
  (implies (true-listp l)
           (true-listp (member-equal x l)))
  :rule-classes (:rewrite :type-prescription))

(defthm true-listp-nthcdr
  (implies (true-listp l)
           (true-listp (nthcdr n l)))
  :hints (("Goal" :induct (nthcdr n l)))
  :rule-classes (:rewrite :type-prescription))

(defthm true-listp-put-nth
  (implies
   (true-listp l)
   (true-listp (put-nth n v l)))
  :rule-classes (:rewrite :type-prescription))

(defthm true-listp-put-seg
  (implies (true-listp l)
           (true-listp (put-seg i seg l)))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthm true-listp-subseq-list
   (true-listp (subseq-list lst start end))
   :hints (("Goal" :do-not-induct t :in-theory (disable take)))
   :rule-classes (:rewrite :type-prescription)))

(defthm true-listp-subseq
  (implies (true-listp seq)
           (true-listp (subseq seq start end)))
  :hints (("Goal" :do-not-induct t :in-theory (disable subseq-list)))
  :rule-classes (:rewrite :type-prescription))

;; true-listp-update-nth already exists

; ------------------------------------------------------------
; NATURALP type prescription rules
; ------------------------------------------------------------

(local
   (defthm naturalp-occurrences-equal-ac
     (implies (and (integerp acc) (<= 0 acc))
              (and (integerp (occurrences-equal-ac item lst acc))
                   (<= 0 (occurrences-equal-ac item lst acc))))))

(defthm naturalp-occurrences-equal
    (and (integerp (occurrences-equal item lst))
         (<= 0 (occurrences-equal item lst)))
    :rule-classes (:rewrite :type-prescription))

(local
   (defthm naturalp-position-equal-ac
     (implies (and (integerp acc)
                   (<= 0 acc)
                   (member-equal item lst))
              (and (integerp (position-equal-ac item lst acc))
                   (<= 0 (position-equal-ac item lst acc))))))

(defthm naturalp-position-equal
    (implies (member-equal item lst)
             (and (integerp (position-equal item lst))
                  (<= 0 (position-equal item lst))))
    :rule-classes (:rewrite :type-prescription))

; ------------------------------------------------------------
; Some support lemmas
; We use these lemmas to define non-recursive forms for some
; recursive functions. These non-recursive forms are easier to
; reason about at times.                                        ;
; ------------------------------------------------------------

(local
 (defthm nth-seg-non-recursive
   (equal (nth-seg i j l)
          (firstn j (nthcdr i l)))))

(local
 (defthm put-seg-non-recursive
   (implies (and (true-listp l)
                 (integerp i)
                 (>= i 0))
            (equal (put-seg i seg l)
                   (append (firstn i l)
                           (firstn (nfix (- (len l) i)) seg)
                           (nthcdr (+ i (min (nfix (- (len l) i)) (len seg)))
                                   l))))
   :hints (("Goal" :induct (put-seg i seg l)))))

(local
 (in-theory (disable nth-seg-non-recursive
                     put-seg-non-recursive)))

; ------------------------------------------------------------
; LEN
; ------------------------------------------------------------

(defthm positive-len-fwd-to-consp
  (implies (< 0 (len l))
           (consp l))
  :rule-classes :forward-chaining)


(defthm len-append
  (equal (len (append a b))
         (+ (len a) (len b))))

(defthm len-revappend
  (equal (len (revappend a b))
         (+ (len a) (len b))))

(defthm len-reverse
  (equal (len (reverse a)) (len a)))

(local
   (defthm len-first-n-ac
     (equal (len (first-n-ac n l ac))
            (+ (nfix n) (len ac)))
     :hints (("Goal" :induct (first-n-ac n l ac)))))

(local
 (defthm len-take
   (equal (len (take n l)) (nfix n))))

(defthm len-butlast
  (implies (and (integerp n) (<= 0 n))
           (equal (len (butlast lst n))
                  (if (<= (len lst) n)
                      0
                    (- (len lst) n))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable take))))

(defthm len-firstn
  (equal (len (firstn n l))
         (if (<= (nfix n) (len l))
             (nfix n)
             (len l)))
  :hints (("Goal" :induct (firstn n l))))

(defthm len-last
  (equal (len (last l))
         (if (consp l)
             1
             0))
  :hints (("Goal" :induct (last l))))

(defthm len-make-list-ac
  (equal (len (make-list-ac n val ac))
         (+ (nfix n) (len ac)))
  :hints (("Goal" :induct (make-list-ac n val ac))))

(defthm len-member-equal
  (not (< (len l) (len (member-equal x l))))
  :rule-classes (:rewrite :linear))

(defthm len-nthcdr
  (equal (len (nthcdr n l))
         (if (<= (nfix n) (len l))
             (- (len l) (nfix n))
             0))
  :hints (("Goal" :induct (nthcdr n l))))

(defthm len-nth-seg
  (implies (<= (+ i j) (len l))
           (equal (len (nth-seg i j l))
                  (min (nfix j) (max (- (len l) (nfix i)) 0))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       (set-difference-theories
                        (current-theory :here)
                        '((:definition nth-seg)))
                       '(nth-seg-non-recursive)))))

(defthm len-put-nth
  (equal (len (put-nth n v l))
         (len l)))

(defthm len-put-seg
  (implies (and (integerp i)
                (not (< i 0)))
           (equal (len (put-seg i seg l))
                  (len l))))

(local
   (defthm occurrences-equal-ac+1
     (implies (acl2-numberp ac)
              (equal (occurrences-equal-ac x l (+ 1 ac))
                     (+ 1 (occurrences-equal-ac x l ac))))))

(local (in-theory (disable occurrences-equal-ac+1)))

(local
   (defthm len-remove-equal-ac
     (implies (acl2-numberp ac)
              (equal (len (remove-equal x l))
                     (+ ac (- (len l) (occurrences-equal-ac x l ac)))))
     :rule-classes nil
     :hints (("Goal" :induct (remove-equal x l)
              :in-theory (enable occurrences-equal-ac+1))
             ("Subgoal *1/2'''" :expand ((OCCURRENCES-EQUAL-AC L1 (CONS L1 L2) AC))))))

(defthm len-remove-equal
    (equal (len (remove-equal x l))
           (- (len l) (occurrences-equal x l)))
    :hints (("Goal" :do-not-induct t
             :use ((:instance len-remove-equal-ac (ac 0))))))

(defthm len-subseq
  (implies (and (true-listp l)
                (integerp start) (<= 0 start)
                (or (and (integerp end) (<= start end))
                    (null end)))
           (equal (len (subseq l start end))
                  (if (null end)
                      (len (nthcdr start l))
                    (- (Nfix end) (nfix start)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable take))))

(defthm len-update-nth1
  (equal (len (update-nth n val l))
         (if (< (nfix n) (len l))
             (len l)
           (+ 1 (nfix n))))
  :hints (("Goal" :induct (update-nth n val l))))

; ------------------------------------------------------------
; LEN inequalities
; ------------------------------------------------------------

(local
   (defthm leq-occurrences-equal-ac-len
     (implies (acl2-numberp ac)
              (not (< (+ (len l) ac) (occurrences-equal-ac x l ac))))
     :rule-classes nil))

(defthm leq-occurrences-equal-len
    (not (< (len l) (occurrences-equal x l)))
    :rule-classes (:rewrite :linear)
    :hints (("Goal" :do-not-induct t
             :use ((:instance leq-occurrences-equal-ac-len (ac 0))))))

(local
   (defthm leq-position-equal-ac-len
     (implies (and (acl2-numberp ac) (member-equal x l))
              (not (< (+ (len l) ac) (position-equal-ac x l ac))))
     :rule-classes nil))

(defthm leq-position-equal-len
    (implies (member-equal x l)
             (not (< (len l) (position-equal x l))))
    :rule-classes (:rewrite :linear)
    :hints (("Goal" :do-not-induct t
             :use ((:instance leq-position-equal-ac-len (ac 0))))))

; ------------------------------------------------------------
; APPEND facts
; ------------------------------------------------------------

; The normal rewriting strategy is to pull APPEND outside of other
; list operations. So we don't have many rules for dealing with other
; operations are args to append.

(defthm append-right-id
  (implies (true-listp a)
           (equal (append a nil)
                  a)))

(defthm associativity-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm append-firstn-nthcdr
  (implies (true-listp l)
           (equal (append (firstn n l) (nthcdr n l)) l)))

; ------------------------------------------------------------
; REVAPPEND, REVERSE
; ------------------------------------------------------------

(defthm revappend-binary-append
  (equal (revappend (binary-append a b) c)
         (revappend b (revappend a c))))

(defthm binary-append-revappend
  (equal (binary-append (revappend a b) c)
         (revappend a (binary-append b c))))

(defthm reverse-append
  (implies (and (listp a)
                (listp b))
           (equal (reverse (append a b))
                  (append (reverse b) (reverse a))))
  :hints (("Goal" :do-not-induct t)))


(defthm revappend-revappend
  (equal (revappend (revappend a b) c)
         (revappend b (binary-append a c))))

(defthm reverse-reverse
  (implies (true-listp l)
           (equal (reverse (reverse l)) l))
  :hints (("Goal" :do-not-induct t)))

; ------------------------------------------------------------
; BUTLAST
; ------------------------------------------------------------

(local
   (defthm first-n-ac-len
     (implies (and (true-listp ac)
                   (true-listp l)
                   (eql (len l) n))
              (equal (first-n-ac n l ac)
                     (revappend ac l)))
     :hints (("Goal" :induct t))))

(local
 (defthm take-len
    (implies (true-listp l)
             (equal (take (len l) l) l))))

(local
   (defthm first-n-ac-append1
     (implies (<= n (len a))
              (equal (first-n-ac n (append a b) ac)
                     (first-n-ac n a ac)))
     :hints (("Goal" :induct (first-n-ac n a ac))))   )

(local
 (defthm take-append1
   (implies (<= n (len a))
            (equal (take n (append a b))
                   (take n a)))))


(defthm butlast-append1-crock
    (IMPLIES (and (TRUE-LISTP A)
                  (<= (+ (LEN A) i) i))
             (EQUAL NIL A))
    :rule-classes nil)


(defthm butlast-append1
    (implies (true-listp a)
             (equal (butlast (append a b) (len b))
                    a))
    :hints (("Goal" :do-not-induct t
             :use ((:instance butlast-append1-crock (i (len b))))
             :in-theory (disable take))))


; ------------------------------------------------------------
; FIRSTN
; ------------------------------------------------------------

(defthm firstn-with-large-index
  (implies (and (<= (len l) (nfix n))
                (true-listp l))
           (equal (firstn n l) l)))

(defthm firstn-append
  (equal (firstn n (append a b))
         (if (<= (nfix n) (len a))
             (firstn n a)
             (append a (firstn (- n (len a)) b)))))

(defthm firstn-firstn
  (equal (firstn i (firstn j l))
         (if (< (nfix i) (nfix j))
             (firstn i l)
             (firstn j l))))

(defthm firstn-make-list-ac
  (equal (firstn i (make-list-ac j v ac))
         (if (< (nfix i) (nfix j))
             (make-list-ac i v nil)
             (make-list-ac j v (firstn (- i (nfix j)) ac)))))

(local
   (defthm firstn-cons
     (equal (firstn n (cons a l))
            (if (zp n)
                nil
              (cons a (firstn (1- n) l))))))

(defthm firstn-put-nth
    (equal (firstn i (put-nth j v l))
           (if (<= (nfix i) (nfix j))
               (firstn i l)
             (put-nth j v (firstn i l))))
    :rule-classes
    ((:rewrite :corollary
               (implies (<= (nfix i) (nfix j))
                        (equal (firstn i (put-nth j v l))
                               (firstn i l))))))

; ------------------------------------------------------------
; MEMBER
; ------------------------------------------------------------

(defthm member-equal-append
  (iff (member-equal x (append a b))
       (or (member-equal x a)
           (member-equal x b))))

(defthm member-equal-make-list-ac-instance
  (implies (not (zp n))
           (member-equal x (make-list-ac n x ac)))
  :hints (("Goal" :induct (make-list-ac n x ac))))

(defthm consp-member-equal-make-list-ac
  (implies (not (zp n))
           (consp (member-equal x (make-list-ac n x ac))))
  :hints (("Goal" :induct (make-list-ac n x ac))))

(defthm member-equal-make-list-ac
  (implies (not (member-equal x ac))
           (iff (member-equal x (make-list-ac n y ac))
                (and (not (zp n))
                     (equal x y)))))

(defthm member-equal-car-last
  (implies (consp l)
           (member-equal (car (last l)) l)))

(defthm member-equal-nth
  (implies (< (nfix n) (len l))
           (member-equal (nth n l) l))
  :hints (("Goal" :in-theory (enable nth))))

(defthm member-equal-put-nth
  (implies (< (nfix n) (len l))
           (member-equal x (put-nth n x l))))

(defthm consp-member-equal-remove-equal
  (iff (consp (member-equal x (remove-equal y l)))
       (if (equal x y)
           nil
         (consp (member-equal x l))))
  :hints (("Goal" :induct (remove-equal y l))))

(defthm member-equal-remove-equal
  (iff (member-equal x (remove-equal y l))
       (if (equal x y)
           nil
           (member-equal x l))))

(defthm consp-member-equal-remove-duplicates-equal
  (iff (consp(member-equal x (remove-duplicates-equal l)))
       (consp(member-equal x l)))
  :hints (("Goal" :induct (remove-duplicates-equal l))))

(defthm member-equal-remove-duplicates-equal
  (iff (member-equal x (remove-duplicates-equal l))
       (member-equal x l)))

(defthm member-equal-revappend
  (iff (member-equal x (revappend a b))
       (or (member-equal x a)
           (member-equal x b)))
  :hints (("Goal" :induct (revappend a b))))

(defthm member-equal-reverse
  (iff (member-equal x (reverse l))
       (member-equal x l)))

(defthm member-equal-update-nth
  (member-equal x (update-nth n x l)))

; ------------------------------------------------------------
; MEMBERP
; ------------------------------------------------------------

(defthm memberp-equal-append
  (iff (memberp-equal x (append a b))
       (or (memberp-equal x a)
           (memberp-equal x b))))

(defthm memberp-equal-make-list-ac
  (implies (not (memberp-equal x ac))
           (iff (memberp-equal x (make-list-ac n y ac))
                (and (not (zp n))
                     (equal x y)))))

(defthm memberp-equal-car-last
  (implies (consp l)
           (memberp-equal (car (last l)) l)))

(defthm memberp-equal-nth
  (implies (< (nfix n) (len l))
           (memberp-equal (nth n l) l))
  :hints (("Goal" :in-theory (enable nth))))

(defthm memberp-equal-put-nth
  (implies (< (nfix n) (len l))
           (memberp-equal x (put-nth n x l))))

(defthm memberp-equal-remove-equal
  (iff (memberp-equal x (remove-equal y l))
       (if (equal x y)
           nil
           (memberp-equal x l))))

(defthm memberp-equal-remove-duplicates-equal
  (iff (memberp-equal x (remove-duplicates-equal l))
       (memberp-equal x l)))

(defthm memberp-equal-revappend
  (iff (memberp-equal x (revappend a b))
       (or (memberp-equal x a)
           (memberp-equal x b)))
  :hints (("Goal" :induct (revappend a b))))

(defthm consp-member-equal-revappend
  (iff (consp (member-equal x (revappend a b)))
       (or (consp (member-equal x a))
           (consp (member-equal x b))))
  :hints (("Goal" :induct (revappend a b))))

(defthm memberp-equal-reverse
  (iff (memberp-equal x (reverse l))
       (memberp-equal x l))
  :hints (("Goal" :do-not-induct t)))

(defthm memberp-equal-update-nth
  (memberp-equal x (update-nth n x l)))

; ------------------------------------------------------------
; INITIAL-SUBLISTP-EQUAL
; ------------------------------------------------------------

(defthm initial-sublistp-equal-reflexive
  (initial-sublistp-equal l l))

(defthm initial-sublistp-equal-nil
  (initial-sublistp-equal nil l))


; ------------------------------------------------------------
; NO-DUPLICATESP-EQUAL
; ------------------------------------------------------------

(defthm no-duplicatesp-equal-remove-duplicates-equal
  (no-duplicatesp-equal (remove-duplicates-equal l))
  :hints (("Goal" :induct (remove-duplicates-equal l))))

; ------------------------------------------------------------
; NTH
; ------------------------------------------------------------

(defthm nth-of-nil
  (equal (nth n nil) nil))

(defthm nth-with-large-index
  (implies (<= (len l) (nfix n))
           (equal (nth n l) nil)))

(defthm nth-append
  (equal (nth n (append a b))
         (if (< (nfix n) (len a))
             (nth n a)
             (nth (- (nfix n) (len a)) b))))

(defthm nth-revappend
  (equal (nth n (revappend a b))
         (if (< (nfix n) (len a))
             (nth (- (len a) (1+ (nfix n))) a)
           (nth (- (nfix n) (len a)) b)))
  :hints (("Goal" :induct (revappend a b))))

(defthm nth-reverse
  (implies (and (integerp n)
                (<= 0 n))
           (equal (nth n (reverse a))
                  (if (< n (len a))
                      (nth (- (len a) (1+ n)) a)
                    nil))))

;; In the following event we show how NTH interacts with TAKE, BUTLAST
;; and SUBSEQ. The proof strategy is to rewrite the basic FIRST-N-AC
;; term into one involving REVAPPEND and a version of firstn called
;; XFIRSTN.


(defun xfirstn (n l)
  (declare (xargs :guard (and (integerp n)
                              (<= 0 n)
                              (true-listp l))))
  (cond ((zp n) nil)
        (t (cons (car l) (xfirstn (1- n) (cdr l))))))

(defthm len-xfirstn
  (equal (len (xfirstn n x))
         (nfix n)))

(defthm nth-xfirstn
  (equal (nth i (xfirstn n l))
         (if (<= (nfix n) (len l))
             (if (< (nfix i) (nfix n))
                 (nth i l)
               nil)
           (if (< (nfix i) (len l))
               (nth i l)
             nil))))


(defthm first-n-ac-non-recursive
  (implies (true-listp ac)
           (equal (first-n-ac n l ac)
                  (revappend ac (xfirstn n l)))))

(defthmd take-is-xfirstn
  (equal (take n l)
         (xfirstn n l)))

(local (in-theory (enable take-is-xfirstn)))
(local (in-theory (disable take)))

(defthm nth-take
  (equal (nth i (take n l))
         (if (<= (nfix n) (len l))
             (if (< (nfix i) (nfix n))
                 (nth i l)
               nil)
           (if (< (nfix i) (len l))
               (nth i l)
             nil)))
  :hints (("Goal" :do-not-induct t)))

(defthm nth-butlast
    (implies (and (integerp i)
                  (<= 0 i)
                  (integerp n)
                  (<= 0 n))
             (equal (nth i (butlast l n))
                    (if (< i (- (len l) n))
                        (nth i l)
                      nil)))
    :hints (("Goal" :do-not-induct t

; Apologia: The following hint was not necessary until we fixed the
; controller-alist problem in Version 2.4.  The author of this book
; has the lemma nth-revappend just waiting for the unexpanded version
; of (revappend (list ...) ...) but because of the controller-alist
; fix, we now open that revappend up.

             :in-theory (disable revappend))))

(defthm car-nthcdr
  (equal (car (nthcdr n l))
         (nth n l)))

(defthmd cdr-over-nthcdr
  (equal (cdr (nthcdr n l))
         (nthcdr n (cdr l))))

(local (in-theory (enable cdr-over-nthcdr)))

(defthm nth-nthcdr
  (equal (nth i (nthcdr j l))
         (nth (+ (nfix j) (nfix i)) l)))

(defthm nth-subseq
    (implies (and (true-listp l)
                  (integerp start) (<= 0 start)
                  (or (and (integerp end) (<= start end))
                      (null end))
                  (integerp n)
                  (<= 0 n))
             (equal (nth n (subseq l start end))
                    (if (null end)
                        (nth n (nthcdr start l))
                      (nth n (take (- end start) (nthcdr start l))))))
    :hints (("Goal" :do-not-induct t

; Apologia:  See nth-butlast.

             :in-theory (disable revappend))))


(defthm nth-firstn
  (equal (nth i (firstn j l))
         (if (< (nfix i) (nfix j))
             (nth i l)
             nil))
  :hints (("Goal" :induct (and (nth i (firstn j l))
                               (nth i l)
                               (firstn j l)))))

(defthm nth-make-list-ac
  (equal (nth i (make-list-ac j val ac))
         (if (< (nfix i) (nfix j))
             val
             (nth (- i (nfix j)) ac)))
  :hints (("Goal" :induct (make-list-ac j val ac))))




(defthm nth-nth-seg
  (equal (nth n (nth-seg i j l))
         (if (< (nfix n) (nfix j))
             (nth (+ (nfix i) (nfix n)) l)
             nil))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       (set-difference-theories
                        (current-theory :here)
                        '((:definition nth-seg)))
                       '(nth-seg-non-recursive)))))


(defthm nth-put-nth
  (equal (nth i (put-nth j v l))
         (if (< (nfix i) (len l))
             (if (equal (nfix i) (nfix j))
                 v
                 (nth i l))
             (nth i l))))

(local
   (defthm nth-put-seg-helper-1
     (implies (and (integerp i)
                   (integerp n)
                   (< (len l) i)
                   (not (< n (len l))))
              (not (nth (+ i n (- (len l))) l)))
     :hints (("Goal" :use (:instance nth-with-large-index
                                     (l l) (n (+ i n (- (len l)))))
              :in-theory (disable nth-with-large-index)))))

(defthm nth-put-seg
  (implies (and (integerp i)
                (not (< i 0)))
           (equal (nth n (put-seg i seg l))
                  (if (< (nfix n) i)
                      (nth n l)
                      (if (< (nfix n)
                             (+ i (min (max (- (len l) i) 0) (len seg))))
                          (nth (- (nfix n) i) seg)
                          (nth n l))))))

(local
   (defthm nth-position-equal-ac
     (implies (member-equal x l)
              (equal (nth (- (position-equal-ac x l ac) ac) l)
                     x))
     :rule-classes nil))

(defthm nth-position-equal
    (implies (member-equal x l)
             (equal (nth (position-equal x l) l)
                    x))
    :hints (("Goal" :use ((:instance nth-position-equal-ac (ac 0))))))

; There's an NTH-UPDATE-NTH in the base ACL2 theory.

; ------------------------------------------------------------
; NTHCDR
; ------------------------------------------------------------

(defthm nthcdr-with-large-index
  (implies (and (<= (len l) (nfix n))
                (true-listp l))
           (equal (nthcdr n l) nil)))

(defthm nthcdr-append
  (equal (nthcdr n (append a b))
         (if (<= (nfix n) (len a))
             (append (nthcdr n a) b)
             (nthcdr (- n (len a)) b))))

(defthm nthcdr-firstn
  (equal (nthcdr i (firstn j l))
         (if (<= (nfix j) (nfix i))
             nil
             (firstn (- (nfix j) (nfix i)) (nthcdr i l))))
  :hints (("Goal" :induct t)))

(defthm nthcdr-make-list-ac
  (equal (nthcdr i (make-list-ac j v ac))
         (if (<= (nfix j) (nfix i))
             (nthcdr (- (nfix i) (nfix j)) ac)
             (make-list-ac (- (nfix j) (nfix i)) v ac)))
  :hints (("Goal" :induct t
           :expand (make-list-ac (+ (- i) j) v ac))))

(defthm nthcdr-nthcdr
  (equal (nthcdr i (nthcdr j l))
         (nthcdr (+ (nfix j) (nfix i)) l)))

(defthm nthcdr-nth-seg
  (equal (nthcdr n (nth-seg i j l))
         (nth-seg (+ (nfix i) (nfix n)) (max (- (nfix j) (nfix n)) 0) l))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       (set-difference-theories
                        (current-theory :here)
                        '((:definition nth-seg)))
                       '(nth-seg-non-recursive)))))

(defthm nthcdr-put-nth
  (equal (nthcdr i (put-nth j v l))
         (if (< (nfix j) (nfix i))
             (nthcdr i l)
             (put-nth (- (nfix j) (nfix i)) v (nthcdr i l))))
  :hints (("Goal" :induct t))
  :rule-classes ((:rewrite :corollary
                           (implies (< (nfix j) (nfix i))
                                    (equal (nthcdr i (put-nth j v l))
                                           (nthcdr i l))))))

; ------------------------------------------------------------
; OCCURRENCES and POSITION helper lemmas
; ------------------------------------------------------------

;; Throughout the rest of this script, we'll take the strategy of
;; proving facts about OCCURRENCES by first proving the fact about XOCCURRENCES.

(local
 (defun xoccurrences-equal (x l)
   (declare (xargs :guard (and (true-listp l)
                               (or (symbolp x) (symbol-listp l)))))
   (cond ((endp l) 0)
         ((eql x (car l)) (1+ (xoccurrences-equal x (cdr l))))
         (t (xoccurrences-equal x (cdr l))))))

(local
 (defthm occurrences-equal-ac-equals-xoccurrences-equal
   (implies (integerp ac)
            (equal (occurrences-equal-ac x l ac)
                   (+ (xoccurrences-equal x l) ac)))))

;; Throughout the rest of this script, we'll take the strategy of
;; proving facts about POSITION by first proving the fact about XPOSITION.

(local
 (defun xposition-equal (x l)
   (declare (xargs :guard (and (true-listp l)
                               (or (symbolp x) (symbol-listp l)))))
   (cond ((endp l) nil)
         ((eq x (car l)) 0)
         (t (let ((N (xposition-equal x (cdr l))))
              (and n (1+ n)))))))

(local
 (defthm position-equal-ac-equals-xposition-equal1
   (implies (integerp ac)
            (iff (position-equal-ac x l ac)
                 (xposition-equal x l)))))

(local
 (defthm position-equal-ac-equals-xposition-equal2
   (implies (and (integerp ac)
                 (position-equal-ac x l ac))
            (equal (position-equal-ac x l ac)
                   (+ (xposition-equal x l) ac)))))

(local
 (defthm position-equal-ac-iff-member-equal
   (implies (integerp ac)
            (iff (position-equal-ac x l ac)
                 (member-equal x l)))))

; ------------------------------------------------------------
; OCCURRENCES
; ------------------------------------------------------------

(local
   (defthm equal-occurrences-equal-ac-zero
     (implies (and (not (member-equal x l))
                   (integerp acc))
              (equal (occurrences-equal-ac x l acc)
                     acc))))

(defthm equal-occurrences-equal-zero
  (implies (not (member-equal x l))
           (equal (occurrences-equal x l)
                  0)))
(local
 (defthm equal-occurrences-equal-ac-one
   (implies (and (member-equal x l)
                 (no-duplicatesp-equal l)
                 (integerp acc))
            (equal (occurrences-equal-ac x l acc) (+ acc 1)))))

(defthm equal-occurrences-equal-one
  (implies (and (member-equal x l)
                (no-duplicatesp-equal l))
           (equal (occurrences-equal x l) 1)))

(local
   (defthm xoccurrences-equal-append
     (implies (integerp ac)
              (equal (xoccurrences-equal x (append a b))
                     (+ (xoccurrences-equal x a)
                        (xoccurrences-equal x b))))))

(defthm occurrences-equal-append
    (equal (occurrences-equal x (append a b))
           (+ (occurrences-equal x a)
              (occurrences-equal x b))))

(local
   (defthm xoccurrences-equal-revappend
     (equal (xoccurrences-equal x (revappend a b))
            (+ (xoccurrences-equal x a)
               (xoccurrences-equal x b)))))

(defthm occurrences-equal-reverse
    (equal (occurrences-equal x (reverse a))
           (occurrences-equal x a)))

(local
   (defthm leq-xoccurrences-equal-firstn
     (<= (xoccurrences-equal x (firstn n l))
         (xoccurrences-equal x l))))

(defthm occurrences-equal-firstn
    (<= (occurrences-equal x (firstn n l))
        (occurrences-equal x l))
    :rule-classes :linear)

(local
   (defthm xoccurrences-equal-firstn-xposition-equal
     (implies (member-equal x l)
              (equal (xoccurrences-equal x (firstn (xposition-equal x l) l))
                     0))))

(defthm occurrences-equal-firstn-position-equal
    (implies (member-equal x l)
             (equal (occurrences-equal x (firstn (position-equal x l) l))
                    0))
    :hints (("Goal" :do-not-induct t)))

(local
   (defthm xoccurrences-equal-make-list-ac
     (equal (xoccurrences-equal x (make-list-ac n val ac))
            (if (eql x val)
                (+ (nfix n) (xoccurrences-equal x ac))
              (xoccurrences-equal x ac)))
     :hints (("Goal" :induct (make-list-ac n val ac)))))

(defthm occurrences-equal-make-list-ac
    (equal (occurrences-equal x (make-list-ac n val ac))
           (if (eql x val)
               (+ (nfix n) (occurrences-equal x ac))
             (occurrences-equal x ac)))
    :hints (("Goal" :do-not-induct t)))

(local
   (defthm xoccurrences-equal-member-equal
     (implies (member-equal x l)
              (equal (xoccurrences-equal x (member-equal x l))
                     (xoccurrences-equal x l)))))

(defthm occurrences-equal-member-equal
    (implies (member-equal x l)
             (equal (occurrences-equal x (member-equal x l))
                    (occurrences-equal x l))))

(local
   (defthm leq-xoccurrences-equal-nthcdr
     (<= (xoccurrences-equal x (nthcdr n l))
         (xoccurrences-equal x l))))

(defthm occurrences-equal-nthcdr
    (<= (occurrences-equal x (nthcdr n l))
        (occurrences-equal x l))
    :rule-classes :linear)

(local
   (defthm xoccurrences-equal-nthcdr-xposition-equal
     (implies (member-equal x l)
              (equal (xoccurrences-equal x (nthcdr (xposition-equal x l) l))
                     (xoccurrences-equal x l)))))

(defthm occurrences-equal-nthcdr-position-equal
    (implies (member-equal x l)
             (equal (occurrences-equal x (nthcdr (position-equal x l) l))
                    (occurrences-equal x l))))

(local
   (defthm xoccurrences-equal-put-nth
     (equal (xoccurrences-equal x (put-nth n v l))
            (if (< (nfix n) (len l))
                (if (equal x v)
                    (if (equal x (nth n l))
                        (xoccurrences-equal x l)
                      (1+ (xoccurrences-equal x l)))
                  (if (equal x (nth n l))
                      (1- (xoccurrences-equal x l))
                    (xoccurrences-equal x l)))
              (xoccurrences-equal x l)))
     :hints (("Goal" :induct (put-nth n v l)
              :in-theory (enable nth)))))

(defthm occurrences-equal-put-nth
    (equal (occurrences-equal x (put-nth n v l))
           (if (< (nfix n) (len l))
               (if (equal x v)
                   (if (equal x (nth n l))
                       (occurrences-equal x l)
                     (1+ (occurrences-equal x l)))
                 (if (equal x (nth n l))
                     (1- (occurrences-equal x l))
                   (occurrences-equal x l)))
             (occurrences-equal x l)))
    :hints (("Goal" :do-not-induct t)))

(local
   (defthm xoccurrences-equal-remove-equal
     (equal (xoccurrences-equal x (remove-equal y l))
            (if (equal x y)
                0
              (xoccurrences-equal x l)))
     :hints (("Goal" :induct (remove-equal y l)))))

(defthm occurrences-equal-remove-equal
    (equal (occurrences-equal x (remove-equal y l))
           (if (equal x y)
               0
             (occurrences-equal x l)))
    :hints (("Goal" :do-not-induct t)))

(local
   (defthm xoccurrences-equal-remove-duplicates-equal
     (<= (xoccurrences-equal x (remove-duplicates-equal l))
         1)))

(defthm occurrences-equal-remove-duplicates-equal
  (<= (occurrences-equal x (remove-duplicates-equal l))
      1)
  :rule-classes (:rewrite :linear))


; ------------------------------------------------------------
; POSITION
; ------------------------------------------------------------

(defthm position-equal-iff-member-equal
  (implies (not (stringp lst))
           (iff (position-equal item lst)
                (member-equal item lst)))
  :hints (("Goal" :do-not-induct t)))

(local
   (defthm xposition-equal-append
     (equal (xposition-equal x (append a b))
            (if (member-equal x a)
                (xposition-equal x a)
              (if (member-equal x b)
                  (+ (len a) (xposition-equal x b))
                nil)))))

(defthm position-equal-append
  (implies
   (not (stringp b))
   (equal (position-equal x (append a b))
          (if (member-equal x a)
              (position-equal x a)
            (if (member-equal x b)
                (+ (len a) (position-equal x b))
              nil))))
  :hints (("Goal" :do-not-induct t)))


; ------------------------------------------------------------
; PUT-NTH
; ------------------------------------------------------------

(defthm put-nth-with-large-index
  (implies (and (true-listp l)
                (<= (len l) (nfix n)))
           (equal (put-nth n v l) l)))

(defthm put-nth-append
  (equal (put-nth n v (append a b))
         (if (< (nfix n) (len a))
             (append (put-nth n v a) b)
             (append a (put-nth (- n (len a)) v b)))))

(local
   (defun put-nth-firstn-induction (i j l)
     (declare (xargs :guard (and (true-listp l)
                                 (integerp i) (<= 0 i)
                                 (integerp j) (<= 0 j))))
     (cond ((endp (firstn j l)) 0)
           ((zp i) 0)
           (t (put-nth-firstn-induction (1- i) (1- j) (cdr l))))))

(defthm put-nth-firstn
    (equal (put-nth i v (firstn j l))
           (if (< (nfix i) (nfix j))
               (firstn j (put-nth i v l))
             (firstn j l)))
    :hints (("Goal" :induct (put-nth-firstn-induction i j l))))

(defthm put-nth-nthcdr
  (equal (put-nth i v (nthcdr j l))
         (nthcdr j (put-nth (+ (nfix j) (nfix i)) v l)))
  :hints (("Goal" :induct t)))

(defthm put-nth-nth
  (implies (true-listp l)
           (equal (put-nth i (nth i l) l) l)))

(defthm put-nth-put-nth
  (equal (put-nth j b (put-nth i a l))
         (if (= (nfix i) (nfix j))
             (put-nth j b l)
             (put-nth i a (put-nth j b l))))
  :rule-classes
  ((:rewrite :corollary
             (implies (= (nfix i) (nfix j))
                      (equal (put-nth j b (put-nth i a l))
                             (put-nth j b l))))
   (:rewrite :corollary
             (implies (< (nfix i) (nfix j))
                      (equal (put-nth j b (put-nth i a l))
                             (put-nth i a (put-nth j b l)))))))

; ------------------------------------------------------------
; REMOVE
; ------------------------------------------------------------

(defthm remove-equal-non-member-equal
  (implies (and (true-listp l)
                (not (member-equal x l)))
           (equal (remove-equal x l) l)))

(defthm remove-equal-append
  (equal (remove-equal x (append a b))
         (append (remove-equal x a) (remove-equal x b))))

(defthm remove-equal-remove-equal
  (equal (remove-equal y (remove-equal x l))
         (if (equal x y)
             (remove-equal x l)
             (remove-equal x (remove-equal y l))))
  :rule-classes
  ((:rewrite :corollary
             (equal (remove-equal x (remove-equal x l))
                    (remove-equal x l)))))

; ------------------------------------------------------------
; UPDATE-NTH
; ------------------------------------------------------------

(defthm update-nth-append
  (equal (update-nth n v (append a b))
         (if (< (nfix n) (len a))
             (append (update-nth n v a) b)
             (append a (update-nth (- n (len a)) v b)))))

;; [Jared] strengthening this rule to agree with coi/nary/nth-rules.lisp
(defthm update-nth-nth
  (implies
   (< (nfix n) (len x))
   (equal (update-nth n (nth n x) x) x)))

;; (defthm update-nth-nth
;;   (implies (and (integerp n)
;;                 (<= 0 n)
;;                 (< n (len l)))
;;            (equal (update-nth n (nth n l) l)
;;                   l)))

(defthm update-nth-update-nth
  (equal (update-nth j b (update-nth i a l))
         (if (= (nfix i) (nfix j))
             (update-nth j b l)
           (update-nth i a (update-nth j b l))))
  :rule-classes
  ((:rewrite :corollary
    (implies (= (nfix i) (nfix j))
             (equal (update-nth j b (update-nth i a l))
                    (update-nth j b l))))
   (:rewrite :corollary
    (implies (not (= (nfix i) (nfix j)))
             (equal (update-nth j b (update-nth i a l))
                    (update-nth i a (update-nth j b l))))
    :loop-stopper ((j i)))))


(defthm true-listp-update-nth-rw
  (implies (true-listp x)
           (true-listp (update-nth n v x))))


; ------------------------------------------------------------
; RESIZE-LIST
; ------------------------------------------------------------

(encapsulate nil
  (local (defun my-induct (n m lst)
           (if (zp n)
               (list lst)
             (if (zp m)
                 nil
               (my-induct (- n 1) (- m 1)
                          (if (atom lst)
                              lst
                            (cdr lst)))))))

  (local (in-theory (enable nth)))

  (defthmd nth-of-resize-list-split
    (equal (nth n (resize-list lst m default-value))
           (let ((n (nfix n))
                 (m (nfix m)))
             (and (< n m)
                  (if (< n (len lst))
                      (nth n lst)
                    default-value))))
    :hints(("Goal"
            :expand (resize-list lst m default-value)
            :induct (my-induct n m lst)))))

(defthm nth-of-resize-list-preserved
  (implies (and (< (nfix n) (len lst))
                (< (nfix n) (nfix m)))
           (equal (nth n (resize-list lst m default-value))
                  (nth n lst)))
  :hints(("Goal" :in-theory (enable nth-of-resize-list-split))))

(defthm nth-of-resize-list-too-big
  (implies (<= (nfix m) (nfix n))
           (equal (nth n (resize-list lst m default-value))
                  nil))
  :hints(("Goal" :in-theory (enable nth-of-resize-list-split))))

(defthm nth-of-resize-list-newly-in-bounds
  (implies (and (<= (len lst) (nfix n))
                (< (nfix n) (nfix m)))
           (equal (nth n (resize-list lst m default-value))
                  default-value))
  :hints(("Goal" :in-theory (enable nth-of-resize-list-split))))


(defthm len-resize-list
  (equal (len (resize-list lst m default))
         (nfix m)))


; ------------------------------------------------------------
; MAKE-LIST-AC
; ------------------------------------------------------------

(defthm make-list-ac-redef
  (equal (make-list-ac n x acc)
         (if (zp n)
             acc
           (cons x (make-list-ac (1- n) x acc))))
  :rule-classes ((:definition :clique (make-list-ac)
                  :controller-alist ((make-list-ac t nil nil)))))

(defun countdown2-ind (n m)
  (if (zp m)
      n
    (countdown2-ind (nfix (1- (nfix n))) (1- m))))


(defthm resize-list-of-make-list-ac-same
  (equal (resize-list (make-list-ac n x nil) m x)
         (make-list-ac m x nil))
  :hints (("goal" :induct (countdown2-ind n m)
           :expand ((make-list-ac n x nil)))))

(defthm resize-list-when-empty
  (implies (atom lst)
           (equal (resize-list lst n x)
                  (make-list-ac n x nil))))

(defun make-list-ac-ind (n x acc)
  (if (zp n)
      acc
    (cons x (make-list-ac-ind (1- n) x acc))))

(defthm make-list-ac-induct
  t
  :rule-classes ((:induction :pattern (make-list-ac n x acc)
                  :scheme (make-list-ac-ind n x acc))))

(in-theory (disable butlast position position-eq position-equal
                    occurrences occurrences-eq occurrences-equal))
