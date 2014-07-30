; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "top")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Fast Assumptions System.
;;
;; We now introduce a cut-down version of our assumptions system where instead
;; of storing eqtraces, we only store the relevant terms.  It's actually quite
;; a bit easier to develop the fast-assms system than the full-blown assms,
;; because we can just introduce the notion of an FAST IMAGE and work from
;; that.
;;
;; The fast image of an assumptions structure is a similar structure where all
;; of the traces are gone and only the terms remain.  We basically only need to
;; develop fast analogues of all the assumptions-manipulating routines, and
;; then show that the image of each routine is the same as the fast-routine.
;;
;; This lets us "piggy back" on the proofs we've already done about the assms
;; system, and frees us from proving all manner of things (e.g., about sets
;; being mutually disjoint, etc.).  It's actually convenient to define our fast
;; version of eqsets so that it doesn't need a unique tail, etc.

(defaggregate rw.fast-eqset
  (head iffp tail)
  :require ((logic.termp-of-rw.fast-eqset->head      (logic.termp head))
            (booleanp-of-rw.fast-eqset->iffp         (booleanp iffp))
            (consp-of-rw.fast-eqset->tail            (consp tail))
            (true-listp-of-rw.fast-eqset->tail       (true-listp tail))
            (logic.term-listp-of-rw.fast-eqset->tail (logic.term-listp tail)))
  :legiblep nil)

(defthm equal-of-rw.fast-eqset-and-rw.fast-eqset
  (equal (equal (rw.fast-eqset head iffp tail)
                (rw.fast-eqset head2 iffp2 tail2))
         (and (equal head head2)
              (equal iffp iffp2)
              (equal tail tail2)))
  :hints(("Goal" :in-theory (enable rw.fast-eqset))))

(deflist rw.fast-eqset-listp (x)
  (rw.fast-eqsetp x)
  :elementp-of-nil nil)

(defprojection
  :list (rw.fast-eqset-list-heads x)
  :element (rw.fast-eqset->head x)
  :guard (rw.fast-eqset-listp x)
  :nil-preservingp t)

(defprojection
  :list (rw.fast-eqset-list-iffps x)
  :element (rw.fast-eqset->iffp x)
  :guard (rw.fast-eqset-listp x)
  :nil-preservingp t)

(defprojection
  :list (rw.fast-eqset-list-tails x)
  :element (rw.fast-eqset->tail x)
  :guard (rw.fast-eqset-listp x)
  :nil-preservingp t)




(defund rw.eqset-fast-image (x)
  (declare (xargs :guard (rw.eqsetp x)))
  (rw.fast-eqset (rw.eqset->head x)
                 (rw.eqset->iffp x)
                 (rw.eqtrace-list-rhses (rw.eqset->tail x))))

(defthm rw.eqset-fast-image-under-iff
  (iff (rw.eqset-fast-image x)
       t)
  :hints(("Goal" :in-theory (enable rw.eqset-fast-image))))

(defthm rw.eqset-fast-image-of-rw.eqset
  (equal (rw.eqset-fast-image (rw.eqset head iffp tail))
         (rw.fast-eqset head iffp (rw.eqtrace-list-rhses tail)))
  :hints(("Goal" :in-theory (enable rw.eqset-fast-image))))

(defthm rw.fast-eqsetp-of-rw.eqset-fast-image
  (implies (force (rw.eqsetp x))
           (equal (rw.fast-eqsetp (rw.eqset-fast-image x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqset-fast-image))))

(defthm rw.fast-eqset->head-of-rw.eqset-fast-image
  (equal (rw.fast-eqset->head (rw.eqset-fast-image x))
         (rw.eqset->head x))
  :hints(("Goal" :in-theory (enable rw.eqset-fast-image))))

(defthm rw.fast-eqset->iffp-of-rw.eqset-fast-image
  (equal (rw.fast-eqset->iffp (rw.eqset-fast-image x))
         (rw.eqset->iffp x))
  :hints(("Goal" :in-theory (enable rw.eqset-fast-image))))

(defthm rw.fast-eqset->tail-of-rw.eqset-fast-image
  (equal (rw.fast-eqset->tail (rw.eqset-fast-image x))
         (rw.eqtrace-list-rhses (rw.eqset->tail x)))
  :hints(("Goal" :in-theory (enable rw.eqset-fast-image))))




(defprojection :list (rw.eqset-list-fast-image x)
               :element (rw.eqset-fast-image x)
               :guard (rw.eqset-listp x))

(defthm rw.fast-eqset-listp-of-rw.eqset-list-fast-image
  (implies (force (rw.eqset-listp x))
           (equal (rw.fast-eqset-listp (rw.eqset-list-fast-image x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rw.fast-eqset-list-heads-of-rw.eqset-list-fast-image
  (equal (rw.fast-eqset-list-heads (rw.eqset-list-fast-image x))
         (rw.eqset-list-heads x))
  :hints(("Goal" :induct (cdr-induction x))))





(definlined rw.fast-eqtrace-contradictionp (iffp lhs rhs)
  (declare (xargs :guard (and (booleanp iffp)
                              (logic.termp lhs)
                              (logic.termp rhs))))
  (or (if iffp
          (and (equal lhs ''nil) (equal rhs ''t))
        (and (logic.constantp lhs)
             (logic.constantp rhs)
             (not (equal lhs rhs))))
      (and (clause.negative-termp rhs)
           (equal (clause.negative-term-guts rhs) lhs))))

(defthm booleanp-of-rw.fast-eqtrace-contradictionp
  (equal (booleanp (rw.fast-eqtrace-contradictionp iffp lhs rhs))
         t)
  :hints(("Goal" :in-theory (enable rw.fast-eqtrace-contradictionp))))

(defthm rw.fast-eqtrace-contradictionp-when-rw.eqtrace-contradictionp
  (equal (rw.fast-eqtrace-contradictionp (rw.eqtrace->iffp x) (rw.eqtrace->lhs x) (rw.eqtrace->rhs x))
         (rw.eqtrace-contradictionp x))
  :hints(("Goal" :in-theory (enable rw.fast-eqtrace-contradictionp
                                    rw.eqtrace-contradictionp))))



(definlined rw.fast-find-eqtrace-contradiction (iffp lhs rhses)
  (declare (xargs :guard (and (booleanp iffp)
                              (logic.termp lhs)
                              (logic.term-listp rhses))))
  (if (consp rhses)
      (or (rw.fast-eqtrace-contradictionp iffp lhs (car rhses))
          (rw.fast-find-eqtrace-contradiction iffp lhs (cdr rhses)))
    nil))

(defthm booleanp-of-rw.fast-find-eqtrace-contradiction
  (equal (booleanp (rw.fast-find-eqtrace-contradiction iffp lhs rhses))
         t)
  :hints(("Goal" :in-theory (enable rw.fast-find-eqtrace-contradiction))))

(defthm rw.fast-find-eqtrace-contradiction-when-rw.find-eqtrace-contradiction
  (implies (and (force (all-equalp lhs (rw.eqtrace-list-lhses x)))
                (force (all-equalp iffp (rw.eqtrace-list-iffps x))))
           (equal (rw.fast-find-eqtrace-contradiction iffp lhs (rw.eqtrace-list-rhses x))
                  (if (rw.find-eqtrace-contradiction x)
                      t
                    nil)))
  :hints(("Goal"
          :in-theory (enable rw.find-eqtrace-contradiction
                             rw.fast-find-eqtrace-contradiction)
          :induct (cdr-induction x))))



(definlined rw.find-contradiction-in-fast-eqset-list (x)
  (declare (xargs :guard (rw.fast-eqset-listp x)))
  (if (consp x)
      (or (rw.fast-find-eqtrace-contradiction (rw.fast-eqset->iffp (car x))
                                              (rw.fast-eqset->head (car x))
                                              (rw.fast-eqset->tail (car x)))
          (rw.find-contradiction-in-fast-eqset-list (cdr x)))
    nil))

(defthm booleanp-of-rw.find-contradiction-in-fast-eqset-list
  (equal (booleanp (rw.find-contradiction-in-fast-eqset-list x))
         t)
  :hints(("Goal" :in-theory (enable rw.find-contradiction-in-fast-eqset-list))))

(defthm rw.find-contradiction-in-fast-eqset-list-of-rw.eqset-list-fast-image
  (implies (force (rw.eqset-listp eqsets))
           (equal (rw.find-contradiction-in-fast-eqset-list (rw.eqset-list-fast-image eqsets))
                  (if (rw.find-contradiction-in-eqset-list eqsets)
                      t
                    nil)))
  :hints(("Goal"
          :in-theory (enable rw.find-contradiction-in-fast-eqset-list
                             rw.find-contradiction-in-eqset-list)
          :induct (cdr-induction eqsets))))





(defaggregate rw.fast-eqdatabase
  (equalsets iffsets contradiction)
  :require ((rw.fast-eqset-listp-of-rw.fast-eqdatabase->equalsets                 (rw.fast-eqset-listp equalsets))
            (rw.fast-eqset-listp-of-rw.fast-eqdatabase->iffsets                   (rw.fast-eqset-listp iffsets))
            (booleanp-of-rw.fast-eqdatabase->contradiction                        (booleanp contradiction))
            ;(uniquep-of-rw.fast-eqset-list-heads-of-rw.fast-eqdatabase->equalsets (uniquep (rw.fast-eqset-list-heads equalsets)))
            ;(uniquep-of-rw.fast-eqset-list-heads-of-rw.fast-eqdatabase->iffsets   (uniquep (rw.fast-eqset-list-heads iffsets)))
            )
  :legiblep nil)

(defthm equal-of-rw.fast-eqdatabase-rewrite
    (implies (force (and (rw.fast-eqset-listp equalsets)
                         (rw.fast-eqset-listp iffsets)
                         (booleanp contradiction)))
             (equal (equal (rw.fast-eqdatabase equalsets iffsets contradiction) db)
                    (and (rw.fast-eqdatabasep db)
                         (equal (rw.fast-eqdatabase->equalsets db) equalsets)
                         (equal (rw.fast-eqdatabase->iffsets db) iffsets)
                         (equal (rw.fast-eqdatabase->contradiction db) contradiction))))
    :hints(("Goal" :in-theory (enable rw.fast-eqdatabase
                                      rw.fast-eqdatabasep
                                      rw.fast-eqdatabase->equalsets
                                      rw.fast-eqdatabase->iffsets
                                      rw.fast-eqdatabase->contradiction))))


;; (defthmd lemma-for-uniquep-of-rw.fast-eqset-list-heads-of-rw.eqset-list-fast-image
;;   (equal (memberp a (rw.fast-eqset-list-heads (rw.eqset-list-fast-image x)))
;;          (memberp a (rw.eqset-list-heads x)))
;;   :hints(("Goal" :induct (cdr-induction x))))

;; (defthm uniquep-of-rw.fast-eqset-list-heads-of-rw.eqset-list-fast-image
;;   (equal (uniquep (rw.fast-eqset-list-heads (rw.eqset-list-fast-image eqsets)))
;;          (uniquep (rw.eqset-list-heads eqsets)))
;;   :hints(("Goal"
;;           :induct (cdr-induction eqsets))
;;           :in-theory (enable rw.eqset-fast-image
;;                              lemma-for-uniquep-of-rw.fast-eqset-list-heads-of-rw.eqset-list-fast-image)))

(defund rw.eqdatabase-fast-image (x)
  (declare (xargs :guard (rw.eqdatabasep x)))
  (rw.fast-eqdatabase (rw.eqset-list-fast-image (rw.eqdatabase->equalsets x))
                      (rw.eqset-list-fast-image (rw.eqdatabase->iffsets x))
                      (if (rw.eqdatabase->contradiction x)
                          t
                        nil)))

(defthm rw.fast-eqdatabasep-of-rw.eqdatabase-fast-image
  (implies (force (and (rw.eqdatabasep db)))
           (equal (rw.fast-eqdatabasep (rw.eqdatabase-fast-image db))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabase-fast-image))))






(definlined rw.fast-eqset-lookup (term eqset)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.fast-eqsetp eqset))
                  :guard-hints (("Goal" :in-theory (enable rw.fast-eqsetp)))))
  (if (logic.term-< term (rw.fast-eqset->head eqset))
      nil
    (if (memberp term (rw.fast-eqset->tail eqset))
        (rw.fast-eqset->head eqset)
      nil)))

(defthm rw.fast-eqset-lookup-of-rw.eqset-fast-image
  (implies (force (rw.eqsetp x))
           (equal (rw.fast-eqset-lookup term (rw.eqset-fast-image x))
                  (if (rw.eqset-lookup term x)
                      (rw.eqtrace->lhs (rw.eqset-lookup term x))
                    nil)))
  :hints(("Goal" :in-theory (enable rw.fast-eqset-lookup
                                    rw.eqset-lookup
                                    rw.eqset-fast-image))))

(defund rw.fast-eqset-list-lookup (term eqsets)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.fast-eqset-listp eqsets))))
  (if (consp eqsets)
      (or (rw.fast-eqset-lookup term (car eqsets))
          (rw.fast-eqset-list-lookup term (cdr eqsets)))
    nil))

(defthm rw.eqset->head-under-iff
  (implies (force (rw.eqsetp x))
           (iff (rw.eqset->head x)
                t))
  :hints(("Goal" :in-theory (enable rw.eqsetp
                                    rw.eqset->head))))

(defthm rw.fast-eqset-list-lookup-of-rw.eqset-list-fast-image
  (implies (force (rw.eqset-listp x))
           (equal (rw.fast-eqset-list-lookup term (rw.eqset-list-fast-image x))
                  (if (rw.eqset-list-lookup term x)
                      (rw.eqtrace->lhs (rw.eqset-list-lookup term x))
                    nil)))
  :hints(("Goal"
          :in-theory (enable rw.eqset-list-lookup
                             rw.fast-eqset-list-lookup)
          :induct (cdr-induction x))))

(definlined rw.fast-try-equiv-database (term database iffp)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.fast-eqdatabasep database)
                              (booleanp iffp))))
  (if iffp
      (rw.fast-eqset-list-lookup term (rw.fast-eqdatabase->iffsets database))
    (rw.fast-eqset-list-lookup term (rw.fast-eqdatabase->equalsets database))))

(defthm rw.fast-try-equiv-database-of-rw.eqdatabase-image
  (implies (rw.eqdatabasep database)
           (equal (rw.fast-try-equiv-database term (rw.eqdatabase-fast-image database) iffp)
                  (if (rw.try-equiv-database term database iffp)
                      (rw.eqtrace->lhs (rw.try-equiv-database term database iffp))
                    nil)))
  :hints(("Goal" :in-theory (enable rw.eqdatabase-fast-image
                                    rw.try-equiv-database
                                    rw.fast-try-equiv-database))))

(defthm logic.termp-of-rw.fast-eqset-lookup
  (implies (force (rw.fast-eqsetp eqset))
           (equal (logic.termp (rw.fast-eqset-lookup term eqset))
                  (if (rw.fast-eqset-lookup term eqset)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.fast-eqset-lookup))))

(defthm logic.termp-of-rw.fast-eqset-list-lookup
  (implies (force (rw.fast-eqset-listp eqsets))
           (equal (logic.termp (rw.fast-eqset-list-lookup term eqsets))
                  (if (rw.fast-eqset-list-lookup term eqsets)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.fast-eqset-list-lookup))))

(defthm logic.termp-of-rw.fast-try-equiv-database
  (implies (force (rw.fast-eqdatabasep database))
           (equal (logic.termp (rw.fast-try-equiv-database term database iffp))
                  (if (rw.fast-try-equiv-database term database iffp)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.fast-try-equiv-database))))




(definlined rw.fast-eqset-relevant (term eqset)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.fast-eqsetp eqset))))
  (or (equal (rw.fast-eqset->head eqset) term)
      (rw.fast-eqset-lookup term eqset)))

(defthm rw.fast-eqset-relevant-of-rw.eqset-fast-image
  (implies (force (rw.eqsetp x))
           (iff (rw.fast-eqset-relevant term (rw.eqset-fast-image x))
                (rw.eqset-relevant term x)))
  :hints(("Goal" :in-theory (enable rw.fast-eqset-relevant
                                    rw.eqset-relevant
                                    ))))

(definlined rw.find-relevant-fast-eqset (term eqsets)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.fast-eqset-listp eqsets))))
  (if (consp eqsets)
      (if (rw.fast-eqset-relevant term (car eqsets))
          (car eqsets)
        (rw.find-relevant-fast-eqset term (cdr eqsets)))
    nil))

(defthm rw.fast-eqsetp-of-rw.find-relevant-fast-eqset
  (implies (force (rw.fast-eqset-listp eqsets))
           (equal (rw.fast-eqsetp (rw.find-relevant-fast-eqset term eqsets))
                  (if (rw.find-relevant-fast-eqset term eqsets)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.find-relevant-fast-eqset))))

(defthm rw.find-relevant-fast-eqset-of-rw.eqset-list-fast-image
  (implies (force (rw.eqset-listp eqsets))
           (equal (rw.find-relevant-fast-eqset term (rw.eqset-list-fast-image eqsets))
                  (if (rw.find-relevant-eqset term eqsets)
                      (rw.eqset-fast-image (rw.find-relevant-eqset term eqsets))
                    nil)))
  :hints(("Goal"
          :in-theory (enable rw.fast-eqset-relevant
                             rw.eqset-relevant
                             rw.find-relevant-fast-eqset
                             rw.find-relevant-eqset))))

(defthm memberp-of-rw.find-relevant-fast-eqset
  (implies (force (rw.fast-eqset-listp x))
           (equal (memberp (rw.find-relevant-fast-eqset a x) x)
                  (if (rw.find-relevant-fast-eqset a x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.find-relevant-fast-eqset))))




(definlined rw.join-fast-eqsets (lhs-set rhs-set)
  ;; We are given a trace, say lhs equiv rhs, and two distinct eqsets which are
  ;; relevant to lhs and rhs, respectively.  We are to union these eqsets.
  (declare (xargs :guard (and (rw.fast-eqsetp lhs-set)
                              (rw.fast-eqsetp rhs-set))))
  (let* ((lhs* (rw.fast-eqset->head lhs-set))
         (rhs* (rw.fast-eqset->head rhs-set))
         (iffp (rw.fast-eqset->iffp lhs-set)))
    (if (logic.term-< lhs* rhs*)
        (rw.fast-eqset lhs* iffp
                       (revappend (rw.fast-eqset->tail lhs-set)
                                  (rw.fast-eqset->tail rhs-set)))
      (rw.fast-eqset rhs* iffp
                     (revappend (rw.fast-eqset->tail lhs-set)
                                (rw.fast-eqset->tail rhs-set))))))

(defthm rw.fast-eqsetp-of-rw.join-fast-eqsets
  (implies (force (and (rw.fast-eqsetp lhs-set)
                       (rw.fast-eqsetp rhs-set)))
           (equal (rw.fast-eqsetp (rw.join-fast-eqsets lhs-set rhs-set))
                  t))
  :hints(("Goal" :in-theory (enable rw.join-fast-eqsets))))

(defthm rw.eqset-fast-image-of-rw.join-eqsets
  (implies (force (and (rw.eqtracep trace)
                       (rw.eqsetp lhs-set)
                       (rw.eqsetp rhs-set)
                       (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp lhs-set))
                       (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp rhs-set))
                       (rw.eqset-relevant (rw.eqtrace->lhs trace) lhs-set)
                       (rw.eqset-relevant (rw.eqtrace->rhs trace) rhs-set)))
           (equal (rw.eqset-fast-image (rw.join-eqsets trace lhs-set rhs-set))
                  (rw.join-fast-eqsets (rw.eqset-fast-image lhs-set)
                                       (rw.eqset-fast-image rhs-set))))
  :hints(("Goal"
          :in-theory (enable rw.join-eqsets rw.join-fast-eqsets))))




(definlined rw.fast-eqset-extend (lhs rhs eqset)
  ;; Try to extend an eqset with lhs = rhs.  The eqset is only actually
  ;; extended if this equality is relevant, i.e., lhs or rhs occur in the set
  ;; somewhere.
  (declare (xargs :guard (and (logic.termp lhs)
                              (logic.termp rhs)
                              (rw.fast-eqsetp eqset))))
  (let* ((set-head  (rw.fast-eqset->head eqset))
         (set-tail  (rw.fast-eqset->tail eqset))
         (iffp      (rw.fast-eqset->iffp eqset)))
    (cond ((equal lhs set-head)
           ;; Special case.
           ;;  * The set's head need not change.
           ;;  * The set's tail needs to be extended with rhs exactly
           ;;    when trace-rhs is not already present.
           (if (memberp rhs set-tail)
               eqset
             (rw.fast-eqset set-head iffp (cons rhs set-tail))))
          ((equal rhs set-head)
           ;; Special case.
           ;;  * The set's head needs to change from rhs to lhs.
           ;;  * The set's tail does not currently include rhs, since rhs is
           ;;    the set-head.  Hence, we need to add rhs to the tail.
           (rw.fast-eqset lhs iffp (cons rhs set-tail)))
          (t
           (let ((lhs-lookup (memberp lhs set-tail))
                 (rhs-lookup (memberp rhs set-tail)))
             (cond ((and lhs-lookup rhs-lookup)
                    ;; lhs and rhs are already in the set.  We already know they
                    ;; are equal, and this trace adds nothing.
                    eqset)
                   (lhs-lookup
                    ;; lhs is in the set, but rhs is not.
                    ;;  * The set's head will not change, since head < lhs < rhs
                    ;;    and we are only adding rhs.
                    (rw.fast-eqset set-head iffp (cons rhs set-tail)))
                   (rhs-lookup
                    ;; rhs is in the set, but lhs is not.
                    (if (logic.term-< set-head lhs)
                        ;; Case 1.
                        ;;  * The set's head will not change
                        ;;  * We need to add lhs to the set's tail.
                        (rw.fast-eqset set-head iffp (cons lhs set-tail))
                      ;; Case 2.
                      ;; We know lhs < set-head, since we already ruled out the possibility
                      ;; that they are equal, and we know that set-head is not less than lhs.
                      ;;  * The set's head needs to become lhs.
                      ;;  * All the existing traces in the tail are currently of
                      ;;    the from set-head ~ x, and need to be updated to
                      ;;    become trace-lhs ~ x.
                      ;;  * We don't add trace-lhs ~ trace-rhs, because trace-rhs
                      ;;    is already a member of the tail.
                      ;;  * But trace-lhs ~ set-head needs to be added to the tail,
                      ;;    since it is not yet present.
                      (rw.fast-eqset lhs
                                     iffp
                                     (cons set-head set-tail))))
                   (t
                    ;; Neither trace-lhs nor trace-rhs are in the set.  The
                    ;; trace is not related to this set, so we won't need to
                    ;; change the set.
                    eqset)))))))

(defthm rw.fast-eqsetp-of-rw.fast-eqset-extend
  (implies (force (and (logic.termp lhs)
                       (logic.termp rhs)
                       (rw.fast-eqsetp eqset)))
           (equal (rw.fast-eqsetp (rw.fast-eqset-extend lhs rhs eqset))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-eqset-extend))))

(defthm rw.eqset-fast-image-of-rw.eqset-extend
  (implies (force (and (rw.eqtracep trace)
                       (rw.eqsetp eqset)
                       (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp eqset))))
           (equal (rw.eqset-fast-image (rw.eqset-extend trace eqset))
                  (rw.fast-eqset-extend (rw.eqtrace->lhs trace)
                                        (rw.eqtrace->rhs trace)
                                        (rw.eqset-fast-image eqset))))
  :hints(("Goal" :in-theory (enable rw.eqset-extend
                                    rw.fast-eqset-extend))))




(defund rw.remove-fast-eqset-by-head (head eqsets)
  (declare (xargs :guard (and (logic.termp head)
                              (rw.fast-eqset-listp eqsets))))
  (if (consp eqsets)
      (if (equal head (rw.fast-eqset->head (car eqsets)))
          (rw.remove-fast-eqset-by-head head (cdr eqsets))
        (cons (car eqsets)
              (rw.remove-fast-eqset-by-head head (cdr eqsets))))
    nil))

(defthm rw.fast-eqset-listp-of-rw.remove-fast-eqset-by-head
  (implies (force (rw.fast-eqset-listp eqsets))
           (equal (rw.fast-eqset-listp (rw.remove-fast-eqset-by-head head eqsets))
                  t))
  :hints(("Goal" :in-theory (enable rw.remove-fast-eqset-by-head))))



(definlined rw.fast-eqsets-extend (lhs rhs iffp eqsets)
  (declare (xargs :guard (and (logic.termp lhs)
                              (logic.termp rhs)
                              (booleanp iffp)
                              (rw.fast-eqset-listp eqsets)
                              ;(uniquep (rw.fast-eqset-list-heads eqsets))
                              )
                  :verify-guards nil))
  (let* ((lhs-set (rw.find-relevant-fast-eqset lhs eqsets))
         (rhs-set (rw.find-relevant-fast-eqset rhs eqsets)))
    (cond ((and (not lhs-set) (not rhs-set))
           ;; Neither term occurs in any existing set, so we want to create
           ;; a new set for these terms.
           (cons (rw.fast-eqset lhs iffp (list rhs)) eqsets))
          ((not lhs-set)
           ;; Only the rhs occurs in any set.  Update that set to include the
           ;; lhs.  There is no chance that this merges sets, since only one
           ;; set is relevant to the trace.
           (cons (rw.fast-eqset-extend lhs rhs rhs-set)
                 (rw.remove-fast-eqset-by-head (rw.fast-eqset->head rhs-set) eqsets)))
          ((not rhs-set)
           ;; Only the lhs occurs in any set. Update the set to include the
           ;; lhs.  As before, there is no chance that we need to merge sets,
           ;; since only one set is relevant.
           (cons (rw.fast-eqset-extend lhs rhs lhs-set)
                 (rw.remove-fast-eqset-by-head (rw.fast-eqset->head lhs-set) eqsets)))
          ((equal lhs-set rhs-set)
           ;; Both terms already occur in the same set, so we already know
           ;; they are equal.  No updates are necessary.
           eqsets)
          (t
           ;; Otherwise each term occurs in its own set.  This trace must now
           ;; be used to merge the sets.
           (let ((lhs-head (rw.fast-eqset->head lhs-set))
                 (rhs-head (rw.fast-eqset->head rhs-set)))
             (cons (rw.join-fast-eqsets lhs-set rhs-set)
                   (rw.remove-fast-eqset-by-head lhs-head
                    (rw.remove-fast-eqset-by-head rhs-head eqsets))))))))

(encapsulate
 ()
 (local (defthm crock
          (implies (and (not (memberp a cr0))
                        (memberp b cr0))
                   (equal (equal a b)
                          nil))))

 (local (defthm lemma
          (implies (and (uniquep (rw.fast-eqset-list-heads eqsets))
                        (memberp a eqsets)
                        (memberp b eqsets)
                        (rw.fast-eqset-listp eqsets))
                   (equal (equal (rw.fast-eqset->head a)
                                 (rw.fast-eqset->head b))
                          (equal a b)))
          :hints(("goal"
                  :induct (cdr-induction eqsets)))))

 (verify-guards rw.fast-eqsets-extend))



(defthm rw.fast-eqset-listp-of-rw.fast-eqsets-extend
  (implies (force (and (logic.termp lhs)
                       (logic.termp rhs)
                       (booleanp iffp)
                       (rw.fast-eqset-listp eqsets)))
           (equal (rw.fast-eqset-listp (rw.fast-eqsets-extend lhs rhs iffp eqsets))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-eqsets-extend))))



(defsection rw.eqset-fast-image-of-rw.eqsets-extend

  (defthmd lemma-0-for-rw.eqset-fast-image-of-rw.eqsets-extend
    (implies (not (memberp (rw.eqset->head a)
                           (rw.eqset-list-heads x)))
             (equal (remove-all a x)
                    (list-fix x)))
    :hints(("Goal" :induct (cdr-induction x))))

  (defthmd lemma-0b-for-rw.eqset-fast-image-of-rw.eqsets-extend
    (implies (not (memberp head (rw.fast-eqset-list-heads x)))
             (equal (rw.remove-fast-eqset-by-head head x)
                    (list-fix x)))
    :hints(("Goal" :in-theory (enable rw.remove-fast-eqset-by-head))))

  (defthmd lemma-1-for-rw.eqset-fast-image-of-rw.eqsets-extend
    (implies (and (uniquep (rw.eqset-list-heads x))
                  (memberp a x))
             (equal (rw.remove-fast-eqset-by-head (rw.eqset->head a) (rw.eqset-list-fast-image x))
                    (rw.eqset-list-fast-image (remove-all a x))))
    :hints(("Goal"
            :induct (cdr-induction x)
            :in-theory (enable rw.remove-fast-eqset-by-head
                               lemma-0-for-rw.eqset-fast-image-of-rw.eqsets-extend
                               lemma-0b-for-rw.eqset-fast-image-of-rw.eqsets-extend))))

  (defthmd lemma-2-for-rw.eqset-fast-image-of-rw.eqsets-extend
    (implies (and (uniquep (rw.eqset-list-heads x))
                  (memberp a x)
                  (memberp b x)
                  (not (equal a b)))
             (equal (equal (rw.eqset-fast-image a)
                           (rw.eqset-fast-image b))
                    nil))
    :hints(("Goal" :in-theory (enable rw.eqset-fast-image))))

  (defthm rw.eqset-fast-image-of-rw.eqsets-extend
    (implies (force (and (rw.eqtracep trace)
                         (rw.eqset-listp eqsets)
                         (all-equalp (rw.eqtrace->iffp trace) (rw.eqset-list-iffps eqsets))
                         (uniquep (rw.eqset-list-heads eqsets))
                         (mutually-disjointp (rw.eqset-list-rhses eqsets))
                         (disjoint-from-allp (rw.eqset-list-heads eqsets)
                                             (rw.eqset-list-rhses eqsets))))
             (equal (rw.eqset-list-fast-image (rw.eqsets-extend trace eqsets))
                    (rw.fast-eqsets-extend (rw.eqtrace->lhs trace)
                                           (rw.eqtrace->rhs trace)
                                           (rw.eqtrace->iffp trace)
                                           (rw.eqset-list-fast-image eqsets))))
    :hints(("Goal" :in-theory (enable rw.fast-eqsets-extend
                                      rw.eqsets-extend
                                      lemma-1-for-rw.eqset-fast-image-of-rw.eqsets-extend
                                      lemma-2-for-rw.eqset-fast-image-of-rw.eqsets-extend)))))



(defsection rw.fast-eqdatabase-extend

  (definlined rw.fast-eqdatabase-extend (nhyp database primaryp secondaryp directp negativep)
    (declare (xargs :guard (and (logic.termp nhyp)
                                (rw.fast-eqdatabasep database)
                                (booleanp primaryp)
                                (booleanp secondaryp)
                                (booleanp directp)
                                (booleanp negativep))))
    ;; BOZO building eqtraces here isn't really necessary, and we could avoid it by
    ;; writing some cut-down versions.  But this really isn't too much consing, and
    ;; it's hard to imagine that it would matter.
    (let ((trace1 (rw.primary-eqtrace primaryp nhyp))
          (trace2 (rw.secondary-eqtrace secondaryp nhyp))
          (trace3 (rw.direct-iff-eqtrace directp nhyp))
          (trace4 (rw.negative-iff-eqtrace negativep nhyp))
          (iffp   (or directp negativep)))
      (if (or trace1 trace2 trace3 trace4)
          (let* ((equalsets        (rw.fast-eqdatabase->equalsets database))
                 (iffsets          (rw.fast-eqdatabase->iffsets database))
                 (contradiction    (rw.fast-eqdatabase->contradiction database))
                 (equalsets-prime  (if trace1
                                       (rw.fast-eqsets-extend (rw.eqtrace->lhs trace1)
                                                              (rw.eqtrace->rhs trace1)
                                                              nil
                                                              equalsets)
                                     equalsets))
                 (equalsets-prime  (if trace2
                                       (rw.fast-eqsets-extend (rw.eqtrace->lhs trace2)
                                                              (rw.eqtrace->rhs trace2)
                                                              nil
                                                              equalsets-prime)
                                     equalsets-prime))
                 (iffsets-prime    (if (and iffp trace1)
                                       (rw.fast-eqsets-extend (rw.eqtrace->lhs trace1)
                                                              (rw.eqtrace->rhs trace1)
                                                              t
                                                              iffsets)
                                     iffsets))
                 (iffsets-prime    (if (and iffp trace2)
                                       (rw.fast-eqsets-extend (rw.eqtrace->lhs trace2)
                                                              (rw.eqtrace->rhs trace2)
                                                              t
                                                              iffsets-prime)
                                     iffsets-prime))
                 (iffsets-prime    (if trace3
                                       (rw.fast-eqsets-extend (rw.eqtrace->lhs trace3)
                                                              (rw.eqtrace->rhs trace3)
                                                              t
                                                              iffsets-prime)
                                     iffsets-prime))
                 (iffsets-prime    (if trace4
                                       (rw.fast-eqsets-extend (rw.eqtrace->lhs trace4)
                                                              (rw.eqtrace->rhs trace4)
                                                              t
                                                              iffsets-prime)
                                     iffsets-prime)))
            (rw.fast-eqdatabase equalsets-prime
                                iffsets-prime
                                (or contradiction
                                    (rw.find-contradiction-in-fast-eqset-list equalsets-prime)
                                    (rw.find-contradiction-in-fast-eqset-list iffsets-prime))))
        database)))


  ;; This proof was kind of hard.  I introduced some auxilliary functions to
  ;; help me break it down into pieces.

  (defund rw.fast-eqdatabase-extend-equalsets (nhyp database primaryp secondaryp)
    (declare (xargs :verify-guards nil))
    (let* ((trace1           (rw.primary-eqtrace primaryp nhyp))
           (trace2           (rw.secondary-eqtrace secondaryp nhyp))
           (equalsets        (rw.fast-eqdatabase->equalsets database))
           (equalsets-prime  (if trace1
                                 (rw.fast-eqsets-extend (rw.eqtrace->lhs trace1)
                                                        (rw.eqtrace->rhs trace1)
                                                        nil
                                                        equalsets)
                               equalsets))
           (equalsets-prime  (if trace2
                                 (rw.fast-eqsets-extend (rw.eqtrace->lhs trace2)
                                                        (rw.eqtrace->rhs trace2)
                                                        nil
                                                        equalsets-prime)
                               equalsets-prime)))
      (if (or trace1 trace2)
          equalsets-prime
        equalsets)))

  (defund rw.fast-eqdatabase-extend-iffsets (nhyp database primaryp secondaryp directp negativep)
    (declare (xargs :verify-guards nil))
    (let* ((trace1           (rw.primary-eqtrace primaryp nhyp))
           (trace2           (rw.secondary-eqtrace secondaryp nhyp))
           (trace3           (rw.direct-iff-eqtrace directp nhyp))
           (trace4           (rw.negative-iff-eqtrace negativep nhyp))
           (iffp             (or directp negativep))
           (iffsets          (rw.fast-eqdatabase->iffsets database))
           (iffsets-prime    (if (and trace1 iffp)
                                 (rw.fast-eqsets-extend (rw.eqtrace->lhs trace1)
                                                        (rw.eqtrace->rhs trace1)
                                                        t
                                                        iffsets)
                               iffsets))
           (iffsets-prime    (if (and trace2 iffp)
                                 (rw.fast-eqsets-extend (rw.eqtrace->lhs trace2)
                                                        (rw.eqtrace->rhs trace2)
                                                        t
                                                        iffsets-prime)
                               iffsets-prime))
           (iffsets-prime    (if trace3
                                 (rw.fast-eqsets-extend (rw.eqtrace->lhs trace3)
                                                        (rw.eqtrace->rhs trace3)
                                                        t
                                                        iffsets-prime)
                               iffsets-prime))
           (iffsets-prime    (if trace4
                                 (rw.fast-eqsets-extend (rw.eqtrace->lhs trace4)
                                                        (rw.eqtrace->rhs trace4)
                                                        t
                                                        iffsets-prime)
                               iffsets-prime)))
      (if (or trace1 trace2 trace3 trace4)
          iffsets-prime
        iffsets)))

  (defund rw.fast-eqdatabase-extend-contradiction (nhyp database primaryp secondaryp directp negativep)
    (declare (xargs :verify-guards nil))
    (let ((trace1 (rw.primary-eqtrace primaryp nhyp))
          (trace2 (rw.secondary-eqtrace secondaryp nhyp))
          (trace3 (rw.direct-iff-eqtrace directp nhyp))
          (trace4 (rw.negative-iff-eqtrace negativep nhyp)))
      (if (or trace1 trace2 trace3 trace4)
          (or (rw.fast-eqdatabase->contradiction database)
              (rw.find-contradiction-in-fast-eqset-list
               (rw.fast-eqdatabase-extend-equalsets nhyp database primaryp secondaryp))
              (rw.find-contradiction-in-fast-eqset-list
               (rw.fast-eqdatabase-extend-iffsets nhyp database primaryp secondaryp directp negativep)))
        (rw.fast-eqdatabase->contradiction database))))

  (defthm booleanp-of-rw.fast-eqdatabase-extend-contradiction
    (implies (force (and (logic.termp nhyp)
                         (rw.fast-eqdatabasep database)))
             (equal (booleanp (rw.fast-eqdatabase-extend-contradiction nhyp database primaryp secondaryp directp negativep))
                    t))
    :hints(("Goal" :in-theory (enable rw.fast-eqdatabase-extend-contradiction))))

  (defthmd rw.fast-eqdatabase-extend-redefinition
    (implies (force (and (logic.termp nhyp)
                         (rw.fast-eqdatabasep database)))
             (equal (rw.fast-eqdatabase-extend nhyp database primaryp secondaryp directp negativep)
                    (rw.fast-eqdatabase (rw.fast-eqdatabase-extend-equalsets nhyp database primaryp secondaryp)
                                        (rw.fast-eqdatabase-extend-iffsets nhyp database primaryp secondaryp directp negativep)
                                        (rw.fast-eqdatabase-extend-contradiction nhyp database primaryp secondaryp directp negativep))))
    :hints(("Goal" :in-theory (enable rw.fast-eqdatabase-extend
                                      rw.fast-eqdatabase-extend-equalsets
                                      rw.fast-eqdatabase-extend-iffsets
                                      rw.fast-eqdatabase-extend-contradiction))))

  (local (in-theory (enable rw.fast-eqdatabase-extend-redefinition)))


  ;; And here come analogues for the non-fast version.

  (defund rw.eqdatabase-extend-equalsets (nhyp database primaryp secondaryp)
    (declare (xargs :verify-guards nil))
    (let* ((trace1           (rw.primary-eqtrace primaryp nhyp))
           (trace2           (rw.secondary-eqtrace secondaryp nhyp))
           (equalsets        (rw.eqdatabase->equalsets database))
           (equalsets-prime  (if trace1 (rw.eqsets-extend trace1 equalsets) equalsets))
           (equalsets-prime  (if trace2 (rw.eqsets-extend trace2 equalsets-prime) equalsets-prime)))
      (if (or trace1 trace2)
          equalsets-prime
        equalsets)))

  (defund rw.eqdatabase-extend-iffsets (nhyp database primaryp secondaryp directp negativep)
    (declare (xargs :verify-guards nil))
    (let* ((trace1        (rw.primary-eqtrace primaryp nhyp))
           (trace2        (rw.secondary-eqtrace secondaryp nhyp))
           (trace3        (rw.direct-iff-eqtrace directp nhyp))
           (trace4        (rw.negative-iff-eqtrace negativep nhyp))
           (iffp          (or directp negativep))
           (iffsets       (rw.eqdatabase->iffsets database))
           (iffsets-prime (if (and iffp trace1) (rw.eqsets-extend (rw.weakening-eqtrace trace1) iffsets) iffsets))
           (iffsets-prime (if (and iffp trace2) (rw.eqsets-extend (rw.weakening-eqtrace trace2) iffsets-prime) iffsets-prime))
           (iffsets-prime (if trace3 (rw.eqsets-extend trace3 iffsets-prime) iffsets-prime))
           (iffsets-prime (if trace4 (rw.eqsets-extend trace4 iffsets-prime) iffsets-prime)))
      (if (or trace1 trace2 trace3 trace4)
          iffsets-prime
        iffsets)))

  (defund rw.eqdatabase-extend-contradiction (nhyp database primaryp secondaryp directp negativep)
    (declare (xargs :verify-guards nil))
    (let* ((trace1 (rw.primary-eqtrace primaryp nhyp))
           (trace2 (rw.secondary-eqtrace secondaryp nhyp))
           (trace3 (rw.direct-iff-eqtrace directp nhyp))
           (trace4 (rw.negative-iff-eqtrace negativep nhyp)))
      (if (or trace1 trace2 trace3 trace4)
          (or (rw.eqdatabase->contradiction database)
              (rw.find-contradiction-in-eqset-list (rw.eqdatabase-extend-equalsets nhyp database primaryp secondaryp))
              (rw.find-contradiction-in-eqset-list (rw.eqdatabase-extend-iffsets nhyp database primaryp secondaryp directp negativep)))
        (rw.eqdatabase->contradiction database))))

  (defthmd equal-of-rw.eqdatabase-rewrite
    ;; BOZO consider moving this to the main eqdatabase stuff.
    (implies (force (rw.eqdatabasep db))
             (equal (equal (rw.eqdatabase equalsets iffsets contradiction) db)
                    (and (equal (rw.eqdatabase->equalsets db) equalsets)
                         (equal (rw.eqdatabase->iffsets db) iffsets)
                         (equal (rw.eqdatabase->contradiction db) contradiction))))
    :hints(("Goal" :in-theory (enable rw.eqdatabase
                                      rw.eqdatabasep
                                      rw.eqdatabase->equalsets
                                      rw.eqdatabase->iffsets
                                      rw.eqdatabase->contradiction))))

  (local (in-theory (enable equal-of-rw.eqdatabase-rewrite)))

  (defthmd rw.eqdatabase-extend-redefinition
    (implies (force (and (logic.termp nhyp)
                         (rw.eqdatabasep database)))
             (equal (rw.eqdatabase-extend nhyp database primaryp secondaryp directp negativep)
                    (rw.eqdatabase (rw.eqdatabase-extend-equalsets nhyp database primaryp secondaryp)
                                   (rw.eqdatabase-extend-iffsets nhyp database primaryp secondaryp directp negativep)
                                   (rw.eqdatabase-extend-contradiction nhyp database primaryp secondaryp directp negativep))))
    :hints(("Goal" :in-theory (enable rw.eqdatabase-extend
                                      rw.eqdatabase-extend-equalsets
                                      rw.eqdatabase-extend-iffsets
                                      rw.eqdatabase-extend-contradiction))))

  (local (in-theory (enable rw.eqdatabase-extend-redefinition)))

  (defthm rw.fast-eqdatabasep-of-rw.fast-eqdatabase-extend
    (implies (force (and (logic.termp nhyp)
                         (rw.fast-eqdatabasep database)))
             (equal (rw.fast-eqdatabasep (rw.fast-eqdatabase-extend nhyp database primaryp secondaryp directp negativep))
                    t))
    :hints(("Goal" :in-theory (e/d (rw.fast-eqdatabase-extend)
                                   (rw.fast-eqdatabase-extend-redefinition)))))

  (defthm rw.eqset-listp-of-rw.eqdatabase-extend-equalsets
    (implies (force (and (logic.termp nhyp)
                         (rw.eqdatabasep database)))
             (equal (rw.eqset-listp (rw.eqdatabase-extend-equalsets nhyp database primaryp secondaryp))
                    t))
    :hints(("Goal" :in-theory (enable rw.eqdatabase-extend-equalsets))))

  (defthm rw.eqset-listp-of-rw.eqdatabase-extend-iffsets
    (implies (force (and (logic.termp nhyp)
                         (rw.eqdatabasep database)))
             (equal (rw.eqset-listp (rw.eqdatabase-extend-iffsets nhyp database primaryp secondaryp directp negativep))
                    t))
    :hints(("Goal" :in-theory (enable rw.eqdatabase-extend-iffsets))))

  (defthmd lemma-1-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
    (implies (force (and (logic.termp nhyp)
                         (rw.eqdatabasep database)))
             (equal (rw.fast-eqdatabase-extend-equalsets nhyp (rw.eqdatabase-fast-image database) primaryp secondaryp)
                    (rw.eqset-list-fast-image (rw.eqdatabase-extend-equalsets nhyp database primaryp secondaryp))))
    :hints(("Goal" :in-theory (enable rw.fast-eqdatabase-extend-equalsets
                                      rw.eqdatabase-extend-equalsets
                                      rw.eqdatabase-fast-image))))

  (defthmd lemma-2-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
    (implies (force (and (logic.termp nhyp)
                         (rw.eqdatabasep database)))
             (equal (rw.fast-eqdatabase-extend-iffsets nhyp (rw.eqdatabase-fast-image database) primaryp secondaryp directp negativep)
                    (rw.eqset-list-fast-image (rw.eqdatabase-extend-iffsets nhyp database primaryp secondaryp directp negativep))))
    :hints(("Goal" :in-theory (enable rw.fast-eqdatabase-extend-iffsets
                                      rw.eqdatabase-extend-iffsets
                                      rw.eqdatabase-fast-image))))

  (defthmd lemma-3-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
    (implies (and (rw.eqdatabase-extend-contradiction nhyp database primaryp secondaryp directp negativep)
                  (force (logic.termp nhyp))
                  (force (rw.eqdatabasep database)))
             (equal (rw.fast-eqdatabase-extend-contradiction nhyp (rw.eqdatabase-fast-image database) primaryp secondaryp directp negativep)
                    t))
    :hints(("Goal"
            :in-theory (enable rw.fast-eqdatabase-extend-contradiction
                               rw.eqdatabase-extend-contradiction
                               lemma-1-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
                               lemma-2-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend))
           (if (not (memberp (acl2::string-for-tilde-@-clause-id-phrase acl2::id) '("Goal" "Goal'")))
               '(:expand (RW.EQDATABASE-FAST-IMAGE DATABASE))
             nil)))

  (defthmd lemma-4-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
    (implies (and (not (rw.eqdatabase-extend-contradiction nhyp database primaryp secondaryp directp negativep))
                  (force (logic.termp nhyp))
                  (force (rw.eqdatabasep database)))
             (equal (rw.fast-eqdatabase-extend-contradiction nhyp (rw.eqdatabase-fast-image database) primaryp secondaryp directp negativep)
                    nil))
    :hints(("Goal" :in-theory (enable rw.fast-eqdatabase-extend-contradiction
                                      rw.eqdatabase-extend-contradiction
                                      lemma-1-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
                                      lemma-2-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend))
           (if (not (memberp (acl2::string-for-tilde-@-clause-id-phrase acl2::id) '("Goal" "Goal'")))
               '(:expand (RW.EQDATABASE-FAST-IMAGE DATABASE))
             nil)))

  (defthm rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
    (implies (force (and (logic.termp nhyp)
                         (rw.eqdatabasep database)))
             (equal (rw.eqdatabase-fast-image (rw.eqdatabase-extend nhyp database primaryp secondaryp directp negativep))
                    (rw.fast-eqdatabase-extend nhyp (rw.eqdatabase-fast-image database) primaryp secondaryp directp negativep)))
    :hints(("Goal"
            :in-theory (enable lemma-1-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
                               lemma-2-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
                               lemma-3-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
                               lemma-4-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend)
            :expand (rw.eqdatabase-fast-image
                     (rw.eqdatabase (rw.eqdatabase-extend-equalsets nhyp database primaryp secondaryp)
                                    (rw.eqdatabase-extend-iffsets nhyp database primaryp secondaryp directp negativep)
                                    (rw.eqdatabase-extend-contradiction nhyp database primaryp secondaryp directp negativep)))))))

;; Note: encapsulate ends.

(defthm rw.fast-eqdatabase->contradiction-of-rw.fast-eqdatabase-extend-of-rw.eqdatabase-fast-image
  (implies (force (and (logic.termp nhyp)
                       (rw.eqdatabasep database)))
           (equal (rw.fast-eqdatabase->contradiction (rw.fast-eqdatabase-extend nhyp (rw.eqdatabase-fast-image database) primaryp secondaryp directp negativep))
                  (if (rw.eqdatabase->contradiction (rw.eqdatabase-extend nhyp database primaryp secondaryp directp negativep))
                      t
                    nil)))
  :hints(("Goal"
          :in-theory (e/d (rw.eqdatabase-fast-image)
                          (rw.eqdatabase-fast-image-of-rw.eqdatabase-extend))
          :use ((:instance rw.eqdatabase-fast-image-of-rw.eqdatabase-extend)))))

(defthm rw.fast-eqdatabase->equalsets-of-rw.fast-eqdatabase-extend-of-rw.eqdatabase-fast-image
  (implies (force (and (logic.termp nhyp)
                       (rw.eqdatabasep database)))
           (equal (rw.fast-eqdatabase->equalsets (rw.fast-eqdatabase-extend nhyp (rw.eqdatabase-fast-image database) primaryp secondaryp directp negativep))
                  (rw.eqset-list-fast-image (rw.eqdatabase->equalsets (rw.eqdatabase-extend nhyp database primaryp secondaryp directp negativep)))))
  :hints(("Goal"
          :in-theory (e/d (rw.eqdatabase-fast-image)
                          (rw.eqdatabase-fast-image-of-rw.eqdatabase-extend))
          :use ((:instance rw.eqdatabase-fast-image-of-rw.eqdatabase-extend)))))

(defthm rw.fast-eqdatabase->iffsets-of-rw.fast-eqdatabase-extend-of-rw.eqdatabase-fast-image
  (implies (force (and (logic.termp nhyp)
                       (rw.eqdatabasep database)))
           (equal (rw.fast-eqdatabase->iffsets (rw.fast-eqdatabase-extend nhyp (rw.eqdatabase-fast-image database) primaryp secondaryp directp negativep))
                  (rw.eqset-list-fast-image (rw.eqdatabase->iffsets (rw.eqdatabase-extend nhyp database primaryp secondaryp directp negativep)))))
  :hints(("Goal"
          :in-theory (e/d (rw.eqdatabase-fast-image)
                          (rw.eqdatabase-fast-image-of-rw.eqdatabase-extend))
          :use ((:instance rw.eqdatabase-fast-image-of-rw.eqdatabase-extend)))))





(defaggregate rw.fast-assms
  (hypbox contradiction eqdatabase trueterms ctrl)
  :require ((rw.hypboxp-of-rw.fast-assms->hypbox              (rw.hypboxp hypbox))
            (booleanp-of-rw.fast-assms->contradiction         (booleanp contradiction))
            (rw.fast-eqdatabasep-of-rw.fast-assms->eqdatabase (rw.fast-eqdatabasep eqdatabase))
            (logic.term-listp-of-rw.fast-assms->trueterms     (logic.term-listp trueterms))
            (rw.assmctrlp-of-rw.fast-assms->ctrl              (rw.assmctrlp ctrl)))
  :legiblep nil)


(defund rw.assms-fast-image (x)
  (declare (xargs :guard (rw.assmsp x)))
  (rw.fast-assms (rw.assms->hypbox x)
                 (if (rw.assms->contradiction x) t nil)
                 (rw.eqdatabase-fast-image (rw.assms->eqdatabase x))
                 (rw.assms->trueterms x)
                 (rw.assms->ctrl x)))

(defthm rw.fast-assms->contradiction-of-rw.assms-fast-image
  (equal (rw.fast-assms->contradiction (rw.assms-fast-image assms))
         (if (rw.assms->contradiction assms)
             t
           nil))
  :hints(("Goal" :in-theory (enable rw.assms-fast-image))))

(defthm rw.fast-assms->hypbox-of-rw.assms-fast-image
  (equal (rw.fast-assms->hypbox (rw.assms-fast-image assms))
         (rw.assms->hypbox assms))
  :hints(("Goal" :in-theory (enable rw.assms-fast-image))))

(defthm rw.fast-assms->trueterms-of-rw.assms-fast-image
  (equal (rw.fast-assms->trueterms (rw.assms-fast-image assms))
         (rw.assms->trueterms assms))
  :hints(("goal" :in-theory (enable rw.assms-fast-image))))

(defthm rw.fast-assms->ctrl-of-rw.assms-fast-image
  (equal (rw.fast-assms->ctrl (rw.assms-fast-image assms))
         (rw.assms->ctrl assms))
  :hints(("Goal" :in-theory (enable rw.assms-fast-image))))


(defthm equal-of-rw.fast-assms
  (implies (force (rw.fast-assmsp assms))
           (equal (equal (rw.fast-assms hypbox contradiction eqdatabase trueterms ctrl) assms)
                  (and (equal (rw.fast-assms->hypbox assms) hypbox)
                       (equal (rw.fast-assms->contradiction assms) contradiction)
                       (equal (rw.fast-assms->eqdatabase assms) eqdatabase)
                       (equal (rw.fast-assms->trueterms assms) trueterms)
                       (equal (rw.fast-assms->ctrl assms) ctrl))))
  :hints(("Goal" :in-theory (enable rw.fast-assms
                                    rw.fast-assmsp
                                    rw.fast-assms->hypbox
                                    rw.fast-assms->contradiction
                                    rw.fast-assms->eqdatabase
                                    rw.fast-assms->trueterms
                                    rw.fast-assms->ctrl))))

(defund rw.fast-assume-left (nhyp assms)
  (declare (xargs :guard (and (logic.termp nhyp)
                              (rw.fast-assmsp assms))))
  (let* ((hypbox     (rw.fast-assms->hypbox assms))
         (eqdb       (rw.fast-assms->eqdatabase assms))
         (ctrl       (rw.fast-assms->ctrl assms))
         (new-hypbox (rw.hypbox (cons nhyp (rw.hypbox->left hypbox))
                                (rw.hypbox->right hypbox)))
         (new-eqdb   (rw.fast-eqdatabase-extend nhyp eqdb
                                                (rw.assmctrl->primaryp ctrl)
                                                (rw.assmctrl->secondaryp ctrl)
                                                (rw.assmctrl->directp ctrl)
                                                (rw.assmctrl->negativep ctrl)))
         (cont       (rw.fast-eqdatabase->contradiction new-eqdb))
         ;; We considered using the iff-t set, but found negating the equal-nil set to
         ;; be a better bet since it gives us (not x) terms as well.  Is this a bug
         ;; with our iff sets, or do we handle this?
         (false-set  (rw.find-relevant-fast-eqset ''nil (rw.fast-eqdatabase->equalsets new-eqdb)))
         (trueterms  (if false-set
                         (clause.smart-negate-list (rw.fast-eqset->tail false-set))
                       nil)))
    (rw.fast-assms new-hypbox cont new-eqdb trueterms ctrl)))

(defthm rw.assms-fast-image-of-rw.assume-left
  (implies (force (and (logic.termp nhyp)
                       (rw.assmsp assms)))
           (equal (rw.assms-fast-image (rw.assume-left nhyp assms))
                  (rw.fast-assume-left nhyp (rw.assms-fast-image assms))))
  :hints(("Goal" :in-theory (enable rw.assms-fast-image
                                    rw.assume-left
                                    rw.fast-assume-left
                                    rw.eqset->rhses))))

(defthm rw.fast-assmsp-of-rw.fast-assume-left
  (implies (force (and (logic.termp nhyp)
                       (rw.fast-assmsp assms)))
           (equal (rw.fast-assmsp (rw.fast-assume-left nhyp assms))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-assume-left))))



(definlined rw.fast-assume-right (nhyp assms)
  (declare (xargs :guard (and (logic.termp nhyp)
                              (rw.fast-assmsp assms))))
  (let* ((hypbox     (rw.fast-assms->hypbox assms))
         (eqdb       (rw.fast-assms->eqdatabase assms))
         (ctrl       (rw.fast-assms->ctrl assms))
         (new-hypbox (rw.hypbox (rw.hypbox->left hypbox)
                                (cons nhyp (rw.hypbox->right hypbox))))
         (new-eqdb   (rw.fast-eqdatabase-extend nhyp eqdb
                                                (rw.assmctrl->primaryp ctrl)
                                                (rw.assmctrl->secondaryp ctrl)
                                                (rw.assmctrl->directp ctrl)
                                                (rw.assmctrl->negativep ctrl)))
         (cont       (rw.fast-eqdatabase->contradiction new-eqdb))
         (false-row  (rw.find-relevant-fast-eqset ''nil (rw.fast-eqdatabase->equalsets new-eqdb)))
         (trueterms  (if false-row
                         (clause.smart-negate-list (rw.fast-eqset->tail false-row))
                       nil)))
    (rw.fast-assms new-hypbox cont new-eqdb trueterms ctrl)))

(defthm rw.assms-fast-image-of-rw.assume-right
  (implies (force (and (logic.termp nhyp)
                       (rw.assmsp assms)))
           (equal (rw.assms-fast-image (rw.assume-right nhyp assms))
                  (rw.fast-assume-right nhyp (rw.assms-fast-image assms))))
  :hints(("Goal" :in-theory (enable rw.assms-fast-image
                                    rw.assume-right
                                    rw.fast-assume-right
                                    rw.eqset->rhses))))

(defthm rw.fast-assmsp-of-rw.fast-assume-right
  (implies (force (and (logic.termp nhyp)
                       (rw.fast-assmsp assms)))
           (equal (rw.fast-assmsp (rw.fast-assume-right nhyp assms))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-assume-right))))



(defund rw.fast-assume-left-list (nhyps assms)
  (declare (xargs :guard (and (logic.term-listp nhyps)
                              (rw.fast-assmsp assms))))
  (if (consp nhyps)
      (rw.fast-assume-left (car nhyps)
                           (rw.fast-assume-left-list (cdr nhyps) assms))
    assms))

(defthm rw.assms-fast-image-of-rw.assume-left-list
  (implies (force (and (logic.term-listp nhyps)
                       (rw.assmsp assms)))
           (equal (rw.assms-fast-image (rw.assume-left-list nhyps assms))
                  (rw.fast-assume-left-list nhyps (rw.assms-fast-image assms))))
  :hints(("Goal" :in-theory (enable rw.fast-assume-left-list))))

(defthm rw.fast-assmsp-of-rw.fast-assume-left-list
  (implies (force (and (logic.term-listp nhyps)
                       (rw.fast-assmsp assms)))
           (equal (rw.fast-assmsp (rw.fast-assume-left-list nhyps assms))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-assume-left-list))))



(defund rw.fast-assume-right-list (nhyps assms)
  (declare (xargs :guard (and (logic.term-listp nhyps)
                              (rw.fast-assmsp assms))))
  (if (consp nhyps)
      (rw.fast-assume-right (car nhyps)
                            (rw.fast-assume-right-list (cdr nhyps) assms))
    assms))

(defthm rw.assms-fast-image-of-rw.assume-right-list
  (implies (force (and (logic.term-listp nhyps)
                       (rw.assmsp assms)))
           (equal (rw.assms-fast-image (rw.assume-right-list nhyps assms))
                  (rw.fast-assume-right-list nhyps (rw.assms-fast-image assms))))
  :hints(("Goal" :in-theory (enable rw.fast-assume-right-list))))

(defthm rw.fast-assmsp-of-rw.fast-assume-right-list
  (implies (force (and (logic.term-listp nhyps)
                       (rw.fast-assmsp assms)))
           (equal (rw.fast-assmsp (rw.fast-assume-right-list nhyps assms))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-assume-right-list))))



(definlined rw.empty-fast-assms (ctrl)
  (declare (xargs :guard (rw.assmctrlp ctrl)))
  (rw.fast-assms (rw.hypbox nil nil)
                 nil
                 (rw.fast-eqdatabase nil nil nil)
                 nil
                 ctrl))

(in-theory (disable (:e rw.empty-fast-assms)))

(defthm rw.assms-fast-image-of-rw.empty-assms
  (equal (rw.assms-fast-image (rw.empty-assms ctrl))
         (rw.empty-fast-assms ctrl))
  :hints(("Goal" :in-theory (e/d (rw.assms-fast-image
                                  rw.empty-fast-assms
                                  rw.empty-assms
                                  rw.eqdatabase-fast-image
                                  rw.empty-eqdatabase
                                  )
                                 ((:e ACL2::force))))))

(defthm rw.fast-assmsp-of-rw.empty-assms
  (implies (force (rw.assmctrlp ctrl))
           (equal (rw.fast-assmsp (rw.empty-fast-assms ctrl))
                  t))
  :hints(("Goal" :in-theory (enable rw.empty-fast-assms))))




(definlined rw.fast-assms-emptyp (assms)
  (declare (xargs :guard (rw.fast-assmsp assms)))
  (let ((hypbox (rw.fast-assms->hypbox assms)))
    (and (not (rw.hypbox->left hypbox))
         (not (rw.hypbox->right hypbox)))))

(defthm rw.fast-assms-emptyp-of-rw.assms-fast-image
  (equal (rw.fast-assms-emptyp (rw.assms-fast-image assms))
         (rw.assms-emptyp assms))
  :hints(("Goal" :in-theory (enable rw.fast-assms-emptyp
                                    rw.assms-emptyp
                                    rw.assms-fast-image))))



(defund rw.fast-assms-formula (assms)
  (declare (xargs :guard (and (rw.fast-assmsp assms)
                              (not (rw.fast-assms-emptyp assms)))
                  :guard-hints (("Goal" :in-theory (enable rw.fast-assms-emptyp)))))
  (rw.hypbox-formula (rw.fast-assms->hypbox assms)))

(defthm rw.fast-assms-formula-of-rw.assms-fast-image
  (equal (rw.fast-assms-formula (rw.assms-fast-image assms))
         (rw.assms-formula assms))
  :hints(("Goal" :in-theory (enable rw.fast-assms-formula
                                    rw.assms-formula
                                    rw.assms-fast-image))))



(definlined rw.fast-try-assms (assms term iffp)
  (declare (xargs :guard (and (rw.fast-assmsp assms)
                              (logic.termp term)
                              (booleanp iffp))))
  (let* ((iffp (and iffp
                    (let ((ctrl (rw.fast-assms->ctrl assms)))
                      (or (rw.assmctrl->directp ctrl)
                          (rw.assmctrl->negativep ctrl))))))
    (rw.fast-try-equiv-database term (rw.fast-assms->eqdatabase assms) iffp)))

(defthm rw.fast-try-assms-of-rw.assms-fast-image
  (implies (force (rw.assmsp assms))
           (equal (rw.fast-try-assms (rw.assms-fast-image assms) term iffp)
                  (rw.try-assms assms term iffp)))
  :hints(("Goal" :in-theory (enable rw.fast-try-assms
                                    rw.try-assms
                                    rw.assms-fast-image))))



(defconst *rw.fast-assms-sigma*
  (list (cons '(rw.try-assms ?assms ?term ?iffp)
              '(rw.fast-try-assms ?assms ?term ?iffp))
        (cons '(rw.assume-left ?nhyp ?assms)
              '(rw.fast-assume-left ?nhyp ?assms))
        (cons '(rw.assume-left-list ?nhyps ?assms)
              '(rw.fast-assume-left-list ?nhyps ?assms))
        (cons '(rw.assume-right ?nhyp ?assms)
              '(rw.fast-assume-right ?nhyp ?assms))
        (cons '(rw.assume-right-list ?nhyps ?assms)
              '(rw.fast-assume-right-list ?nhyps ?assms))
        (cons '(rw.assms->trueterms ?assms)
              '(rw.fast-assms->trueterms ?assms))
        (cons '(rw.assms->hypbox ?assms)
              '(rw.fast-assms->hypbox ?assms))))

