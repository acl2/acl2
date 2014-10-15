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
(include-book "contradictionp")
(include-book "eqtrace-okp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthmd all-equalp-as-repeat
  ;; BOZO move me to all-equalp.lisp
  (equal (all-equalp a x)
         (equal (list-fix x)
                (repeat a (len x))))
  :hints(("Goal"
          :in-theory (enable repeat)
          :induct (cdr-induction x))))




;; The equivalence database.
;;
;; We now are ready to introduce our equivalence database.  This structure
;; tracks equalities and boolean equivalences using two disjoined-set data
;; structures (sometimes called a union-find structures).  One of these is used
;; for equalities, and the other is used for iff-equivalences.  But we can
;; share a lot of code between the two.


;; Each equivalence set is simple aggregate containing:
;;   - head, a term which acts as the canonical member for this set
;;   - iffp, a flag indicating if the equivalence relation is equal or iff
;;   - traces, a list of eqtraces of the form (equiv lhs rhs), whose rhses
;;     are all unique

(defund rw.eqsetp (x)
  ;; BOZO why aren't we using defaggregate?
  ;; We use the custom cons structure (head . (iffp . tail))
  (let ((head (car x))
        (iffp (car (cdr x)))
        (tail (cdr (cdr x))))
    (and (logic.termp head)
         (booleanp iffp)
         (consp tail)
         (true-listp tail)
         (rw.eqtrace-listp tail)
         (all-equalp iffp (rw.eqtrace-list-iffps tail))
         (all-equalp head (rw.eqtrace-list-lhses tail))
         (uniquep (rw.eqtrace-list-rhses tail)))))

(definlined rw.eqset->head (x)
  (declare (xargs :guard (rw.eqsetp x)
                  :guard-hints (("Goal" :in-theory (enable rw.eqsetp)))))
  (car x))

(definlined rw.eqset->iffp (x)
  (declare (xargs :guard (rw.eqsetp x)
                  :guard-hints (("Goal" :in-theory (enable rw.eqsetp)))))
  (car (cdr x)))

(definlined rw.eqset->tail (x)
  (declare (xargs :guard (rw.eqsetp x)
                  :guard-hints (("Goal" :in-theory (enable rw.eqsetp)))))
  (cdr (cdr x)))

(definlined rw.eqset (head iffp tail)
  (declare (xargs :guard (and (logic.termp head)
                              (booleanp iffp)
                              (rw.eqtrace-listp tail)
                              (consp tail)
                              (all-equalp iffp (rw.eqtrace-list-iffps tail))
                              (all-equalp head (rw.eqtrace-list-lhses tail))
                              (uniquep (rw.eqtrace-list-rhses tail)))))
  (cons head
        (cons iffp tail)))

(defthm booleanp-of-rw.eqsetp
  (equal (booleanp (rw.eqsetp x))
         t)
  :hints(("Goal" :in-theory (enable rw.eqsetp))))

(defthm rw.eqset->head-of-rw.eqset
  (equal (rw.eqset->head (rw.eqset head iffp tail))
         head)
  :hints(("Goal" :in-theory (enable rw.eqset rw.eqset->head))))

(defthm rw.eqset->iffp-of-rw.eqset
  (equal (rw.eqset->iffp (rw.eqset head iffp tail))
         iffp)
  :hints(("Goal" :in-theory (enable rw.eqset rw.eqset->iffp))))

(defthm rw.eqset->tail-of-rw.eqset
  (equal (rw.eqset->tail (rw.eqset head iffp tail))
         tail)
  :hints(("Goal" :in-theory (enable rw.eqset rw.eqset->tail))))

(defthm forcing-rw.eqsetp-of-rw.eqset
  (implies (force (and (logic.termp head)
                       (booleanp iffp)
                       (consp tail)
                       (true-listp tail)
                       (rw.eqtrace-listp tail)
                       (all-equalp iffp (rw.eqtrace-list-iffps tail))
                       (all-equalp head (rw.eqtrace-list-lhses tail))
                       (uniquep (rw.eqtrace-list-rhses tail))))
           (equal (rw.eqsetp (rw.eqset head iffp tail))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqsetp rw.eqset))))

(defthm forcing-logic.termp-of-rw.eqset->head
  (implies (force (rw.eqsetp x))
           (equal (logic.termp (rw.eqset->head x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqsetp rw.eqset->head))))

(defthm forcing-booleanp-of-rw.eqset->iffp
  (implies (force (rw.eqsetp x))
           (equal (booleanp (rw.eqset->iffp x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqsetp rw.eqset->iffp))))

(defthm forcing-consp-of-rw.eqset->tail
  (implies (force (rw.eqsetp x))
           (equal (consp (rw.eqset->tail x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqsetp rw.eqset->tail))))

(defthm forcing-true-listp-of-rw.eqset->tail
  (implies (force (rw.eqsetp x))
           (equal (true-listp (rw.eqset->tail x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqsetp rw.eqset->tail))))

(defthm forcing-rw.eqtrace-listp-of-rw.eqset->tail
  (implies (force (rw.eqsetp x))
           (equal (rw.eqtrace-listp (rw.eqset->tail x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqsetp rw.eqset->tail))))

(defthm forcing-rw.eqtrace-list-iffps-of-rw.eqset->tail
  (implies (force (rw.eqsetp x))
           (equal (rw.eqtrace-list-iffps (rw.eqset->tail x))
                  (repeat (rw.eqset->iffp x) (len (rw.eqset->tail x)))))
  :hints(("Goal" :in-theory (enable rw.eqsetp rw.eqset->iffp rw.eqset->tail all-equalp-as-repeat))))

(defthm forcing-rw.eqtrace-list-lhses-of-rw.eqset->tail
  (implies (force (rw.eqsetp x))
           (equal (rw.eqtrace-list-lhses (rw.eqset->tail x))
                  (repeat (rw.eqset->head x) (len (rw.eqset->tail x)))))
  :hints(("Goal" :in-theory (enable rw.eqsetp rw.eqset->head rw.eqset->tail all-equalp-as-repeat))))

(defthm forcing-uniquep-of-rw.eqtrace-list-rhses-of-rw.eqset->tail
  (implies (force (rw.eqsetp x))
           (equal (uniquep (rw.eqtrace-list-rhses (rw.eqset->tail x)))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqsetp rw.eqset->tail))))

(deflist rw.eqset-listp (x)
  (rw.eqsetp x)
  :elementp-of-nil nil
  :guard t)




(definlined rw.eqset-atblp (x atbl)
  (declare (xargs :guard (and (rw.eqsetp x)
                              (logic.arity-tablep atbl))))
  (rw.eqtrace-list-atblp (rw.eqset->tail x) atbl))

(defthm booleanp-of-rw.eqset-atblp
  (equal (booleanp (rw.eqset-atblp x atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.eqset-atblp))))

(defthm forcing-rw.eqset-atblp-of-rw.eqset
  (implies (force (rw.eqtrace-list-atblp tail atbl))
           (equal (rw.eqset-atblp (rw.eqset head iffp tail) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqset-atblp))))

(defthm forcing-rw.eqtrace-list-atblp-of-rw.eqset->tail
  (implies (force (rw.eqset-atblp x atbl))
           (equal (rw.eqtrace-list-atblp (rw.eqset->tail x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqset-atblp))))

(defthmd lemma-for-forcing-logic.term-atblp-of-rw.eqset->head
  (implies (and (logic.term-list-atblp x atbl)
                (equal x (repeat term len))
                (not (zp len)))
           (equal (logic.term-atblp term atbl)
                  t)))

(defthm forcing-logic.term-atblp-of-rw.eqset->head
  (implies (force (and (rw.eqsetp x)
                       (rw.eqset-atblp x atbl)))
           (equal (logic.term-atblp (rw.eqset->head x) atbl)
                  t))
  :hints(("Goal"
          :in-theory (disable forcing-rw.eqtrace-list-atblp-of-rw.eqset->tail
                              forcing-rw.eqtrace-list-lhses-of-rw.eqset->tail)
          :use ((:instance lemma-for-forcing-logic.term-atblp-of-rw.eqset->head
                           (x    (rw.eqtrace-list-lhses (rw.eqset->tail x)))
                           (term (rw.eqset->head x))
                           (len  (len (rw.eqset->tail x))))
                (:instance forcing-rw.eqtrace-list-lhses-of-rw.eqset->tail)))))

(defthm rw.eqset-atblp-of-nil
  (equal (rw.eqset-atblp nil atbl)
         t)
  :hints(("Goal" :in-theory (enable rw.eqset-atblp))))

(deflist rw.eqset-list-atblp (x atbl)
  (rw.eqset-atblp x atbl)
  :elementp-of-nil t
  :guard (and (rw.eqset-listp x)
              (logic.arity-tablep atbl)))



(definlined rw.eqset-okp (x box)
  (declare (xargs :guard (and (rw.eqsetp x)
                              (rw.hypboxp box))))
  (rw.eqtrace-list-okp (rw.eqset->tail x) box))

(defthm booleanp-of-rw.eqset-okp
  (equal (booleanp (rw.eqset-okp x box))
         t)
  :hints(("Goal" :in-theory (enable rw.eqset-okp))))

(defthm forcing-rw.eqtrace-list-okp-of-rw.eqset->tail
  (implies (force (rw.eqset-okp x box))
           (equal (rw.eqtrace-list-okp (rw.eqset->tail x) box)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqset-okp))))

(defthm rw.eqset-okp-of-rw.eqset
  (implies (force (rw.eqtrace-list-okp tail box))
           (equal (rw.eqset-okp (rw.eqset head iffp tail) box)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqset-okp))))

(defthm rw.eqset-okp-of-nil
  (equal (rw.eqset-okp nil box)
         t)
  :hints(("Goal" :in-theory (enable rw.eqset-okp))))


(deflist rw.eqset-list-okp (x box)
  (rw.eqset-okp x box)
  :elementp-of-nil t
  :guard (and (rw.eqset-listp x)
              (rw.hypboxp box)))





(defprojection :list (rw.eqset-list-heads x)
               :element (rw.eqset->head x)
               :guard (rw.eqset-listp x)
               :nil-preservingp t)

(defthm forcing-logic.term-listp-of-rw.eqset-list-heads
  (implies (force (rw.eqset-listp x))
           (equal (logic.term-listp (rw.eqset-list-heads x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-rw.eqset-list-heads
  (implies (force (and (rw.eqset-listp x)
                       (rw.eqset-list-atblp x atbl)))
           (equal (logic.term-list-atblp (rw.eqset-list-heads x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(defprojection :list (rw.eqset-list-iffps x)
               :element (rw.eqset->iffp x)
               :guard (rw.eqset-listp x)
               :nil-preservingp t)





(definlined rw.eqset->rhses (x)
  (declare (xargs :guard (rw.eqsetp x)))
  (rw.eqtrace-list-rhses (rw.eqset->tail x)))

(defthm forcing-logic.term-listp-of-rw.eqset->rhses
  (implies (force (rw.eqsetp x))
           (equal (logic.term-listp (rw.eqset->rhses x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqset->rhses))))

(defthm forcing-logic.term-list-atblp-of-rw.eqset->rhses
  (implies (force (rw.eqset-atblp x atbl))
           (equal (logic.term-list-atblp (rw.eqset->rhses x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqset->rhses))))



(defprojection :list (rw.eqset-list-rhses x)
               :element (rw.eqset->rhses x)
               :guard (rw.eqset-listp x)
               :nil-preservingp t)

(defthm forcing-logic.term-list-listp-of-rw.eqset-list-rhses
  (implies (force (rw.eqset-listp x))
           (equal (logic.term-list-listp (rw.eqset-list-rhses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-rw.eqrow-list-rhses
  (implies (force (rw.eqset-list-atblp x atbl))
           (equal (logic.term-list-list-atblp (rw.eqset-list-rhses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(definlined rw.find-contradiction-in-eqset-list (x)
  (declare (xargs :guard (rw.eqset-listp x)
                  :guard-hints (("Goal" :in-theory (enable rw.eqsetp)))))
  (if (consp x)
      (or (rw.find-eqtrace-contradiction (rw.eqset->tail (car x)))
          (rw.find-contradiction-in-eqset-list (cdr x)))
    nil))

(encapsulate
 ()
 (local (in-theory (enable rw.find-contradiction-in-eqset-list)))

 (defthm forcing-rw.eqtracep-of-rw.find-contradiction-in-eqrow-list
   (implies (and (rw.find-contradiction-in-eqset-list x)
                 (force (rw.eqset-listp x)))
            (equal (rw.eqtracep (rw.find-contradiction-in-eqset-list x))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.find-contradiction-in-eqset-list
   (implies (and (rw.find-contradiction-in-eqset-list x)
                 (force (rw.eqset-list-atblp x atbl)))
            (equal (rw.eqtrace-atblp (rw.find-contradiction-in-eqset-list x) atbl)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.find-contradiction-in-eqset-list
   (implies (and (rw.find-contradiction-in-eqset-list x)
                 (force (rw.eqset-list-okp x box)))
            (equal (rw.eqtrace-okp (rw.find-contradiction-in-eqset-list x) box)
                   t)))

 (defthm forcing-rw.eqtrace-contradictionp-of-rw.find-contradiction-in-eqset-list
   (implies (rw.find-contradiction-in-eqset-list x)
            (equal (rw.eqtrace-contradictionp (rw.find-contradiction-in-eqset-list x))
                   t))))



(defund rw.eqdatabasep (x)
  (declare (xargs :guard t))
  ;; We use the cons structure (equalsets . (iffsets . contradiction))
  (and (consp x)
       (consp (cdr x))
       (let ((equalsets     (car x))
             (iffsets       (car (cdr x)))
             (contradiction (cdr (cdr x))))
         (and (rw.eqset-listp equalsets)
              (rw.eqset-listp iffsets)
              (let ((heads (rw.eqset-list-heads equalsets))
                    (iffps (rw.eqset-list-iffps equalsets))
                    (rhses (rw.eqset-list-rhses equalsets)))
                (and (all-equalp nil iffps)
                     (uniquep heads)
                     (mutually-disjointp rhses)
                     (disjoint-from-allp heads rhses)))
              (let ((heads (rw.eqset-list-heads iffsets))
                    (rhses (rw.eqset-list-rhses iffsets))
                    (iffps (rw.eqset-list-iffps iffsets)))
                (and (all-equalp t iffps)
                     (uniquep heads)
                     (mutually-disjointp rhses)
                     (disjoint-from-allp heads rhses)))
              (or (not contradiction)
                  (and (rw.eqtracep contradiction)
                       (rw.eqtrace-contradictionp contradiction)))))))

(definlined rw.eqdatabase->equalsets (x)
  (declare (xargs :guard (rw.eqdatabasep x)))
  (car x))

(definlined rw.eqdatabase->iffsets (x)
  (declare (xargs :guard (rw.eqdatabasep x)))
  (car (cdr x)))

(definlined rw.eqdatabase->contradiction (x)
  (declare (xargs :guard (rw.eqdatabasep x)))
  (cdr (cdr x)))

(definlined rw.eqdatabase (equalsets iffsets contradiction)
  (declare (xargs :guard (and (rw.eqset-listp equalsets)
                              (rw.eqset-listp iffsets)
                              (let ((heads (rw.eqset-list-heads equalsets))
                                    (iffps (rw.eqset-list-iffps equalsets))
                                    (rhses (rw.eqset-list-rhses equalsets)))
                                (and (all-equalp nil iffps)
                                     (uniquep heads)
                                     (mutually-disjointp rhses)
                                     (disjoint-from-allp heads rhses)))
                              (let ((heads (rw.eqset-list-heads iffsets))
                                    (rhses (rw.eqset-list-rhses iffsets))
                                    (iffps (rw.eqset-list-iffps iffsets)))
                                (and (all-equalp t iffps)
                                     (uniquep heads)
                                     (mutually-disjointp rhses)
                                     (disjoint-from-allp heads rhses)))
                              (or (not contradiction)
                                  (and (rw.eqtracep contradiction)
                                       (rw.eqtrace-contradictionp contradiction))))))
  (cons equalsets
        (cons iffsets contradiction)))

(defthm booleanp-of-rw.eqdatabasep
  (equal (booleanp (rw.eqdatabasep x))
         t)
  :hints(("Goal" :in-theory (enable rw.eqdatabasep))))

(defthm rw.eqdatabase->equalsets-of-rw.eqdatabase
  (equal (rw.eqdatabase->equalsets (rw.eqdatabase equalsets iffsets contradiction))
         equalsets)
  :hints(("Goal" :in-theory (enable rw.eqdatabase rw.eqdatabase->equalsets))))

(defthm rw.eqdatabase->iffsets-of-rw.eqdatabase
  (equal (rw.eqdatabase->iffsets (rw.eqdatabase equalsets iffsets contradiction))
         iffsets)
  :hints(("Goal" :in-theory (enable rw.eqdatabase rw.eqdatabase->iffsets))))

(defthm rw.eqdatabase->contradiction-of-rw.eqdatabase
  (equal (rw.eqdatabase->contradiction (rw.eqdatabase equalsets iffsets contradiction))
         contradiction)
  :hints(("Goal" :in-theory (enable rw.eqdatabase rw.eqdatabase->contradiction))))

(defthm forcing-rw.eqdatabasep-of-rw.eqdatabase
  (implies (force (and (rw.eqset-listp equalsets)
                       (rw.eqset-listp iffsets)
                       (let ((heads (rw.eqset-list-heads equalsets))
                             (iffps (rw.eqset-list-iffps equalsets))
                             (rhses (rw.eqset-list-rhses equalsets)))
                         (and (all-equalp nil iffps)
                              (uniquep heads)
                              (mutually-disjointp rhses)
                              (disjoint-from-allp heads rhses)))
                       (let ((heads (rw.eqset-list-heads iffsets))
                             (rhses (rw.eqset-list-rhses iffsets))
                             (iffps (rw.eqset-list-iffps iffsets)))
                         (and (all-equalp t iffps)
                              (uniquep heads)
                              (mutually-disjointp rhses)
                              (disjoint-from-allp heads rhses)))
                       (or (not contradiction)
                           (and (rw.eqtracep contradiction)
                                (rw.eqtrace-contradictionp contradiction)))))
           (equal (rw.eqdatabasep (rw.eqdatabase equalsets iffsets contradiction))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase))))

(defthm forcing-rw.eqset-listp-of-rw.eqdatabase->equalsets
  (implies (force (rw.eqdatabasep x))
           (equal (rw.eqset-listp (rw.eqdatabase->equalsets x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase->equalsets))))

(defthm forcing-uniquep-of-rw.eqset-list-heads-of-rw.eqdatabase->equalsets
  (implies (force (rw.eqdatabasep x))
           (equal (uniquep (rw.eqset-list-heads (rw.eqdatabase->equalsets x)))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase->equalsets))))

(defthm forcing-disjoint-from-allp-of-rw.eqrow-list-heads-of-rw.eqdatabase->equalsets
  (implies (force (rw.eqdatabasep x))
           (equal (disjoint-from-allp (rw.eqset-list-heads (rw.eqdatabase->equalsets x))
                                      (rw.eqset-list-rhses (rw.eqdatabase->equalsets x)))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase->equalsets))))

(defthm forcing-mutually-disjointp-of-rw.eqrow-list-rhses-of-rw.eqdatabase->equalsets
  (implies (force (rw.eqdatabasep x))
           (equal (mutually-disjointp (rw.eqset-list-rhses (rw.eqdatabase->equalsets x)))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase->equalsets))))

(defthm forcing-rw.eqset-list-iffps-of-rw.eqdatabase->equalsets
  (implies (force (rw.eqdatabasep x))
           (equal (rw.eqset-list-iffps (rw.eqdatabase->equalsets x))
                  (repeat nil (len (rw.eqdatabase->equalsets x)))))
  :hints(("Goal"
          :in-theory (enable rw.eqdatabasep rw.eqdatabase->equalsets all-equalp-as-repeat))))



(defthm forcing-rw.eqset-listp-of-rw.eqdatabase->iffsets
  (implies (force (rw.eqdatabasep x))
           (equal (rw.eqset-listp (rw.eqdatabase->iffsets x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase->iffsets))))

(defthm forcing-uniquep-of-rw.eqset-list-heads-of-rw.eqdatabase->iffsets
  (implies (force (rw.eqdatabasep x))
           (equal (uniquep (rw.eqset-list-heads (rw.eqdatabase->iffsets x)))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase->iffsets))))

(defthm forcing-disjoint-from-allp-of-rw.eqset-list-heads-of-rw.eqdatabase->iffsets
  (implies (force (rw.eqdatabasep x))
           (equal (disjoint-from-allp (rw.eqset-list-heads (rw.eqdatabase->iffsets x))
                                      (rw.eqset-list-rhses (rw.eqdatabase->iffsets x)))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase->iffsets))))

(defthm forcing-mutually-disjointp-of-rw.eqset-list-rhses-of-rw.eqdatabase->iffsets
  (implies (force (rw.eqdatabasep x))
           (equal (mutually-disjointp (rw.eqset-list-rhses (rw.eqdatabase->iffsets x)))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase->iffsets))))

(defthm forcing-rw.eqset-list-iffps-of-rw.eqdatabase->iffsets
  (implies (force (rw.eqdatabasep x))
           (equal (rw.eqset-list-iffps (rw.eqdatabase->iffsets x))
                  (repeat t (len (rw.eqdatabase->iffsets x)))))
  :hints(("Goal"
          :in-theory (enable rw.eqdatabasep rw.eqdatabase->iffsets all-equalp-as-repeat))))



(defthm forcing-rw.eqtracep-of-rw.eqdatabase->contradiction
  (implies (and (rw.eqdatabase->contradiction x)
                (force (rw.eqdatabasep x)))
           (equal (rw.eqtracep (rw.eqdatabase->contradiction x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase->contradiction))))

(defthm forcing-rw.eqtrace-contradictionp-of-rw.eqdatabase->contradiction
  (implies (and (rw.eqdatabase->contradiction x)
                (force (rw.eqdatabasep x)))
           (equal (rw.eqtrace-contradictionp (rw.eqdatabase->contradiction x))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep rw.eqdatabase->contradiction))))




(definlined rw.eqdatabase-atblp (x atbl)
  (declare (xargs :guard (and (rw.eqdatabasep x)
                              (logic.arity-tablep atbl))))
  (let ((equalsets     (rw.eqdatabase->equalsets x))
        (iffsets       (rw.eqdatabase->iffsets x))
        (contradiction (rw.eqdatabase->contradiction x)))
    (and (rw.eqset-list-atblp equalsets atbl)
         (rw.eqset-list-atblp iffsets atbl)
         (or (not contradiction)
             (rw.eqtrace-atblp contradiction atbl)))))

(defthm rw.eqdatabase-atblp-of-nil
  (equal (rw.eqdatabase-atblp nil atbl)
         t)
  :hints(("Goal" :in-theory (enable rw.eqdatabase-atblp))))

(defthm booleanp-of-rw.eqdatabase-atblp
  (equal (booleanp (rw.eqdatabase-atblp x atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.eqdatabase-atblp))))

(defthm forcing-rw.eqdatabase-atblp-of-rw.eqdatabase
  (implies (force (and (rw.eqset-list-atblp equalsets atbl)
                       (rw.eqset-list-atblp iffsets atbl)
                       (or (not contradiction)
                           (rw.eqtrace-atblp contradiction atbl))))
           (equal (rw.eqdatabase-atblp (rw.eqdatabase equalsets iffsets contradiction) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabase-atblp))))

(defthm forcing-rw.eqset-list-atblp-of-rw.eqdatabase->equalsets
  (implies (force (rw.eqdatabase-atblp x atbl))
           (equal (rw.eqset-list-atblp (rw.eqdatabase->equalsets x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabase-atblp))))

(defthm forcing-rw.eqset-list-atblp-of-rw.eqdatabase->iffsets
  (implies (force (rw.eqdatabase-atblp x atbl))
           (equal (rw.eqset-list-atblp (rw.eqdatabase->iffsets x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.eqdatabase-atblp)
                                 (forcing-rw.eqset-list-atblp-of-rw.eqdatabase->equalsets)))))

(defthm forcing-rw.trace-atblp-of-rw.eqdatabase->contradiction
  (implies (force (and (rw.eqdatabase->contradiction x)
                       (rw.eqdatabase-atblp x atbl)))
           (equal (rw.eqtrace-atblp (rw.eqdatabase->contradiction x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.eqdatabase-atblp)
                                 (forcing-rw.eqset-list-atblp-of-rw.eqdatabase->equalsets
                                  forcing-rw.eqset-list-atblp-of-rw.eqdatabase->iffsets)))))



(definlined rw.eqdatabase-okp (x box)
  (declare (xargs :guard (and (rw.eqdatabasep x)
                              (rw.hypboxp box))))
  (let ((equalsets     (rw.eqdatabase->equalsets x))
        (iffsets       (rw.eqdatabase->iffsets x))
        (contradiction (rw.eqdatabase->contradiction x)))
    (and (rw.eqset-list-okp equalsets box)
         (rw.eqset-list-okp iffsets box)
         (or (not contradiction)
             (rw.eqtrace-okp contradiction box)))))

(defthm booleanp-of-rw.eqdatabase-okp
  (equal (booleanp (rw.eqdatabase-okp x box))
         t)
  :hints(("Goal" :in-theory (enable rw.eqdatabase-okp))))

(defthm forcing-rw.eqdatabase-okp-of-rw.eqdatabase
  (implies (force (and (rw.eqset-list-okp equalsets box)
                       (rw.eqset-list-okp iffsets box)
                       (or (not contradiction)
                           (rw.eqtrace-okp contradiction box))))
           (equal (rw.eqdatabase-okp (rw.eqdatabase equalsets iffsets contradiction) box)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabase-okp))))

(defthm forcing-rw.eqset-list-okp-of-rw.eqdatabase->equalsets
  (implies (force (rw.eqdatabase-okp x box))
           (equal (rw.eqset-list-okp (rw.eqdatabase->equalsets x) box)
                  t))
  :hints(("Goal" :in-theory (enable rw.eqdatabase-okp))))

(defthm forcing-rw.eqset-list-okp-of-rw.eqdatabase->iffsets
  (implies (force (rw.eqdatabase-okp x box))
           (equal (rw.eqset-list-okp (rw.eqdatabase->iffsets x) box)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.eqdatabase-okp)
                                 (forcing-rw.eqset-list-okp-of-rw.eqdatabase->equalsets)))))

(defthm forcing-rw.trace-okp-of-rw.eqdatabase->contradiction
  (implies (force (and (rw.eqdatabase->contradiction x)
                       (rw.eqdatabase-okp x box)))
           (equal (rw.eqtrace-okp (rw.eqdatabase->contradiction x) box)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.eqdatabase-okp)
                                 (forcing-rw.eqset-list-okp-of-rw.eqdatabase->equalsets
                                  forcing-rw.eqset-list-okp-of-rw.eqdatabase->iffsets)))))


