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
(include-book "assms-top")
(%interactive)


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

(%defaggregate rw.fast-eqset
  (head iffp tail)
  :require ((logic.termp-of-rw.fast-eqset->head      (logic.termp head))
            (booleanp-of-rw.fast-eqset->iffp         (booleanp iffp))
            (consp-of-rw.fast-eqset->tail            (consp tail))
            (true-listp-of-rw.fast-eqset->tail       (true-listp tail))
            (logic.term-listp-of-rw.fast-eqset->tail (logic.term-listp tail))))

(%autoprove equal-of-rw.fast-eqset-and-rw.fast-eqset
            (%enable default rw.fast-eqset))

(%deflist rw.fast-eqset-listp (x)
          (rw.fast-eqsetp x))

(%defprojection :list (rw.fast-eqset-list-heads x)
                :element (rw.fast-eqset->head x)
                :nil-preservingp t)

(%defprojection :list (rw.fast-eqset-list-iffps x)
                :element (rw.fast-eqset->iffp x)
                :nil-preservingp t)

(%defprojection :list (rw.fast-eqset-list-tails x)
                :element (rw.fast-eqset->tail x)
                :nil-preservingp t)



(defsection rw.eqset-fast-image
  (%autoadmit rw.eqset-fast-image)
  (local (%enable default rw.eqset-fast-image))
  (%autoprove rw.eqset-fast-image-under-iff)
  (%autoprove rw.eqset-fast-image-of-rw.eqset)
  (%autoprove rw.fast-eqsetp-of-rw.eqset-fast-image)
  (%autoprove rw.fast-eqset->head-of-rw.eqset-fast-image)
  (%autoprove rw.fast-eqset->iffp-of-rw.eqset-fast-image)
  (%autoprove rw.fast-eqset->tail-of-rw.eqset-fast-image))



(%defprojection :list (rw.eqset-list-fast-image x)
                :element (rw.eqset-fast-image x))

(%autoprove rw.fast-eqset-listp-of-rw.eqset-list-fast-image (%cdr-induction x))
(%autoprove rw.fast-eqset-list-heads-of-rw.eqset-list-fast-image (%cdr-induction x))





(%autoadmit rw.fast-eqtrace-contradictionp)

(%autoprove booleanp-of-rw.fast-eqtrace-contradictionp
            (%enable default rw.fast-eqtrace-contradictionp))

(defthm rw.fast-eqtrace-contradictionp-when-rw.eqtrace-contradictionp
  ;; BOZO should be redundant now.
  (equal (rw.fast-eqtrace-contradictionp (rw.eqtrace->iffp x) (rw.eqtrace->lhs x) (rw.eqtrace->rhs x))
         (rw.eqtrace-contradictionp x))
  :hints(("Goal" :in-theory (enable rw.fast-eqtrace-contradictionp
                                    rw.eqtrace-contradictionp))))

(%autoprove rw.fast-eqtrace-contradictionp-when-rw.eqtrace-contradictionp
            (%enable default
                     rw.fast-eqtrace-contradictionp
                     rw.eqtrace-contradictionp))



(%autoadmit rw.fast-find-eqtrace-contradiction)

(%autoprove booleanp-of-rw.fast-find-eqtrace-contradiction
            (%cdr-induction rhses)
            (%restrict default rw.fast-find-eqtrace-contradiction (equal rhses 'rhses)))

(%autoprove rw.fast-find-eqtrace-contradiction-when-rw.find-eqtrace-contradiction
            (%cdr-induction x)
            (%restrict default rw.find-eqtrace-contradiction (memberp x '(x 'nil)))
            (%restrict default rw.fast-find-eqtrace-contradiction
                       (memberp rhses '(x 'nil (cons (rw.eqtrace->rhs x1)
                                                     (rw.eqtrace-list-rhses x2))))))



(%autoadmit rw.find-contradiction-in-fast-eqset-list)

(%autoprove booleanp-of-rw.find-contradiction-in-fast-eqset-list
            (%cdr-induction x)
            (%restrict default rw.find-contradiction-in-fast-eqset-list (equal x 'x)))

(%autoprove rw.find-contradiction-in-fast-eqset-list-of-rw.eqset-list-fast-image
            (%cdr-induction eqsets)
            (%restrict default rw.find-contradiction-in-fast-eqset-list
                       (memberp x '(eqsets (cons (rw.eqset-fast-image eqsets1)
                                                 (rw.eqset-list-fast-image eqsets2)))))
            (%restrict default rw.find-contradiction-in-eqset-list (equal x 'eqsets)))




(%defaggregate rw.fast-eqdatabase
  (equalsets iffsets contradiction)
  :require ((rw.fast-eqset-listp-of-rw.fast-eqdatabase->equalsets (rw.fast-eqset-listp equalsets))
            (rw.fast-eqset-listp-of-rw.fast-eqdatabase->iffsets   (rw.fast-eqset-listp iffsets))
            (booleanp-of-rw.fast-eqdatabase->contradiction        (booleanp contradiction))))

(%autoprove equal-of-rw.fast-eqdatabase-rewrite
            (%enable default
                     rw.fast-eqdatabase
                     rw.fast-eqdatabasep
                     rw.fast-eqdatabase->equalsets
                     rw.fast-eqdatabase->iffsets
                     rw.fast-eqdatabase->contradiction))

(defthm equal-of-rw.fast-eqdatabase-rewrite-alt
  (implies (force (and (rw.fast-eqset-listp equalsets)
                       (rw.fast-eqset-listp iffsets)
                       (booleanp contradiction)))
           (equal (equal db (rw.fast-eqdatabase equalsets iffsets contradiction))
                  (and (rw.fast-eqdatabasep db)
                       (equal (rw.fast-eqdatabase->equalsets db) equalsets)
                       (equal (rw.fast-eqdatabase->iffsets db) iffsets)
                       (equal (rw.fast-eqdatabase->contradiction db) contradiction)))))

(%autoprove equal-of-rw.fast-eqdatabase-rewrite-alt
            (%use (%thm equal-of-rw.fast-eqdatabase-rewrite)))




(%autoadmit rw.eqdatabase-fast-image)

(%autoprove rw.fast-eqdatabasep-of-rw.eqdatabase-fast-image
            (%enable default rw.eqdatabase-fast-image))



(%autoadmit rw.fast-eqset-lookup)

(%autoprove rw.fast-eqset-lookup-of-rw.eqset-fast-image
            (%enable default
                     rw.fast-eqset-lookup
                     rw.eqset-lookup
                     rw.eqset-fast-image))

(%autoadmit rw.fast-eqset-list-lookup)

(%autoprove rw.eqset->head-under-iff
            (%enable default rw.eqsetp rw.eqset->head))

(%autoprove rw.fast-eqset-list-lookup-of-rw.eqset-list-fast-image
            (%cdr-induction x)
            (%restrict default rw.eqset-list-lookup (equal eqsets 'x))
            (%restrict default rw.fast-eqset-list-lookup
                       (memberp eqsets '(x 'nil (cons (rw.eqset-fast-image x1)
                                                      (rw.eqset-list-fast-image x2))))))




(%autoadmit rw.fast-try-equiv-database)

(%autoprove rw.fast-try-equiv-database-of-rw.eqdatabase-image
            (%enable default
                     rw.eqdatabase-fast-image
                     rw.try-equiv-database
                     rw.fast-try-equiv-database))

(%autoprove logic.termp-of-rw.fast-eqset-lookup
            (%enable default rw.fast-eqset-lookup))

(%autoprove logic.termp-of-rw.fast-eqset-list-lookup
            (%cdr-induction eqsets)
            (%restrict default rw.fast-eqset-list-lookup (equal eqsets 'eqsets)))

(%autoprove logic.termp-of-rw.fast-try-equiv-database
            (%enable default rw.fast-try-equiv-database))




(%autoadmit rw.fast-eqset-relevant)

(%autoprove rw.fast-eqset-relevant-of-rw.eqset-fast-image
  (%enable default rw.fast-eqset-relevant rw.eqset-relevant))



(%autoadmit rw.find-relevant-fast-eqset)

(%autoprove rw.fast-eqsetp-of-rw.find-relevant-fast-eqset
            (%cdr-induction eqsets)
            (%restrict default rw.find-relevant-fast-eqset (equal eqsets 'eqsets)))

(%autoprove rw.find-relevant-fast-eqset-of-rw.eqset-list-fast-image
            (%cdr-induction eqsets)
            (%restrict default rw.find-relevant-eqset (equal eqsets 'eqsets))
            (%restrict default rw.find-relevant-fast-eqset
                       (memberp eqsets '(eqsets 'nil (cons (rw.eqset-fast-image eqsets1)
                                                           (rw.eqset-list-fast-image eqsets2))))))

(%autoprove memberp-of-rw.find-relevant-fast-eqset
            (%cdr-induction x)
            (%restrict default rw.find-relevant-fast-eqset (equal eqsets 'x)))




(%autoadmit rw.join-fast-eqsets)

(%autoprove rw.fast-eqsetp-of-rw.join-fast-eqsets
            (%enable default rw.join-fast-eqsets))

(%autoprove rw.eqset-fast-image-of-rw.join-eqsets
            (%enable default rw.join-eqsets rw.join-fast-eqsets))




(%autoadmit rw.fast-eqset-extend)

(%autoprove rw.fast-eqsetp-of-rw.fast-eqset-extend
            (%enable default rw.fast-eqset-extend))

(%autoprove rw.eqset-fast-image-of-rw.eqset-extend
            (%enable default rw.eqset-extend
                     rw.fast-eqset-extend))



(%autoadmit rw.remove-fast-eqset-by-head)

(%autoprove rw.fast-eqset-listp-of-rw.remove-fast-eqset-by-head
            (%cdr-induction eqsets)
            (%restrict default rw.remove-fast-eqset-by-head (equal eqsets 'eqsets)))




(%autoadmit rw.fast-eqsets-extend)

(%autoprove rw.fast-eqset-listp-of-rw.fast-eqsets-extend
            (%enable default rw.fast-eqsets-extend))

(%autoprove lemma-0-for-rw.eqset-fast-image-of-rw.eqsets-extend
            (%cdr-induction x))

(%autoprove lemma-0b-for-rw.eqset-fast-image-of-rw.eqsets-extend
            (%cdr-induction x)
            (%restrict default rw.remove-fast-eqset-by-head (equal eqsets 'x)))

(%autoprove lemma-1-for-rw.eqset-fast-image-of-rw.eqsets-extend
            (%cdr-induction x)
            (%enable default
                     lemma-0-for-rw.eqset-fast-image-of-rw.eqsets-extend
                     lemma-0b-for-rw.eqset-fast-image-of-rw.eqsets-extend)
            (%restrict default rw.remove-fast-eqset-by-head
                       (memberp eqsets '(x (cons (rw.eqset-fast-image x1)
                                                 (rw.eqset-list-fast-image x2))))))

(%autoprove lemma-2-for-rw.eqset-fast-image-of-rw.eqsets-extend
            (%enable default rw.eqset-fast-image))

(%autoprove rw.eqset-fast-image-of-rw.eqsets-extend
            (%enable default
                     rw.fast-eqsets-extend
                     rw.eqsets-extend
                     lemma-1-for-rw.eqset-fast-image-of-rw.eqsets-extend
                     lemma-2-for-rw.eqset-fast-image-of-rw.eqsets-extend)
            (%auto)
            (%restrict default rw.find-relevant-fast-eqset (equal eqsets ''nil))
            (%restrict default rw.find-relevant-eqset (equal eqsets 'eqsets)))




(defsection rw.fast-eqdatabase-extend

  (%autoadmit rw.fast-eqdatabase-extend)
  (%autoadmit rw.fast-eqdatabase-extend-equalsets)
  (%autoadmit rw.fast-eqdatabase-extend-iffsets)
  (%autoadmit rw.fast-eqdatabase-extend-contradiction)

  (%autoprove booleanp-of-rw.fast-eqdatabase-extend-contradiction
              (%enable default rw.fast-eqdatabase-extend-contradiction))

  (%autoprove rw.fast-eqdatabase-extend-redefinition
              (%enable default
                       rw.fast-eqdatabase-extend
                       rw.fast-eqdatabase-extend-equalsets
                       rw.fast-eqdatabase-extend-iffsets
                       rw.fast-eqdatabase-extend-contradiction))

  (local (%enable default rw.fast-eqdatabase-extend-redefinition))

  (%autoadmit rw.eqdatabase-extend-equalsets)
  (%autoadmit rw.eqdatabase-extend-iffsets)
  (%autoadmit rw.eqdatabase-extend-contradiction)
  (%autoprove equal-of-rw.eqdatabase-rewrite
              (%enable default
                       rw.eqdatabase
                       rw.eqdatabasep
                       rw.eqdatabase->equalsets
                       rw.eqdatabase->iffsets
                       rw.eqdatabase->contradiction))

  (local (%enable default equal-of-rw.eqdatabase-rewrite))

  (defthmd equal-of-rw.eqdatabase-rewrite-alt
    (implies (force (rw.eqdatabasep db))
             (equal (equal db (rw.eqdatabase equalsets iffsets contradiction))
                    (and (equal (rw.eqdatabase->equalsets db) equalsets)
                         (equal (rw.eqdatabase->iffsets db) iffsets)
                         (equal (rw.eqdatabase->contradiction db) contradiction))))
    :hints(("Goal" :in-theory (enable equal-of-rw.eqdatabase-rewrite))))

  (%autoprove equal-of-rw.eqdatabase-rewrite-alt
              (%use (%thm equal-of-rw.eqdatabase-rewrite)))

  (local (%enable default equal-of-rw.eqdatabase-rewrite-alt))

  (%autoprove rw.eqdatabase-extend-redefinition
              (%enable default
                       rw.eqdatabase-extend
                       rw.eqdatabase-extend-equalsets
                       rw.eqdatabase-extend-iffsets
                       rw.eqdatabase-extend-contradiction))


  (local (%enable default rw.eqdatabase-extend-redefinition))

  (%autoprove rw.fast-eqdatabasep-of-rw.fast-eqdatabase-extend
              (%enable default rw.fast-eqdatabase-extend)
              (%disable default rw.fast-eqdatabase-extend-redefinition))

  (%autoprove rw.eqset-listp-of-rw.eqdatabase-extend-equalsets
              (%enable default rw.eqdatabase-extend-equalsets))

  (%autoprove rw.eqset-listp-of-rw.eqdatabase-extend-iffsets
              (%enable default rw.eqdatabase-extend-iffsets))

  (%autoprove lemma-1-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
              (%enable default
                       rw.fast-eqdatabase-extend-equalsets
                       rw.eqdatabase-extend-equalsets
                       rw.eqdatabase-fast-image))

  (%autoprove lemma-2-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
              (%enable default
                       rw.fast-eqdatabase-extend-iffsets
                       rw.eqdatabase-extend-iffsets
                       rw.eqdatabase-fast-image))

  (%autoprove lemma-3-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
              (%enable default
                       rw.fast-eqdatabase-extend-contradiction
                       rw.eqdatabase-extend-contradiction
                       lemma-1-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
                       lemma-2-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend)
              (%auto)
              (%enable default rw.eqdatabase-fast-image))

  (%autoprove lemma-4-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
              (%enable default
                       rw.fast-eqdatabase-extend-contradiction
                       rw.eqdatabase-extend-contradiction
                       lemma-1-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
                       lemma-2-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend)
              (%auto)
              (%enable default rw.eqdatabase-fast-image))

  (%autoprove rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
              (%enable default
                       lemma-1-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
                       lemma-2-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
                       lemma-3-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend
                       lemma-4-for-rw.eqdatabase-fast-image-of-rw.eqdatabase-extend)
              (%restrict default rw.eqdatabase-fast-image
                         (equal x '(rw.eqdatabase
                                    (rw.eqdatabase-extend-equalsets nhyp database primaryp secondaryp)
                                    (rw.eqdatabase-extend-iffsets nhyp database primaryp secondaryp directp negativep)
                                    (rw.eqdatabase-extend-contradiction nhyp database primaryp secondaryp directp negativep))))))

(%autoprove rw.fast-eqdatabase->contradiction-of-rw.fast-eqdatabase-extend-of-rw.eqdatabase-fast-image
            (%enable default rw.eqdatabase-fast-image)
            (%disable default rw.eqdatabase-fast-image-of-rw.eqdatabase-extend)
            (%use (%instance (%thm rw.eqdatabase-fast-image-of-rw.eqdatabase-extend))))

(%autoprove rw.fast-eqdatabase->equalsets-of-rw.fast-eqdatabase-extend-of-rw.eqdatabase-fast-image
            (%enable default rw.eqdatabase-fast-image)
            (%disable default rw.eqdatabase-fast-image-of-rw.eqdatabase-extend)
            (%use (%instance (%thm rw.eqdatabase-fast-image-of-rw.eqdatabase-extend))))

(%autoprove rw.fast-eqdatabase->iffsets-of-rw.fast-eqdatabase-extend-of-rw.eqdatabase-fast-image
            (%enable default rw.eqdatabase-fast-image)
            (%disable default rw.eqdatabase-fast-image-of-rw.eqdatabase-extend)
            (%use (%instance (%thm rw.eqdatabase-fast-image-of-rw.eqdatabase-extend))))




(%defaggregate rw.fast-assms
  (hypbox contradiction eqdatabase trueterms ctrl)
  :require ((rw.hypboxp-of-rw.fast-assms->hypbox              (rw.hypboxp hypbox))
            (booleanp-of-rw.fast-assms->contradiction         (booleanp contradiction))
            (rw.fast-eqdatabasep-of-rw.fast-assms->eqdatabase (rw.fast-eqdatabasep eqdatabase))
            (logic.term-listp-of-rw.fast-assms->trueterms     (logic.term-listp trueterms))
            (rw.assmctrlp-of-rw.fast-assms->ctrl              (rw.assmsctrlp ctrl))))


(%autoadmit rw.assms-fast-image)

(%autoprove rw.fast-assms->contradiction-of-rw.assms-fast-image
            (%enable default rw.assms-fast-image))

(%autoprove rw.fast-assms->hypbox-of-rw.assms-fast-image
            (%enable default rw.assms-fast-image))

(%autoprove rw.fast-assms->trueterms-of-rw.assms-fast-image
            (%enable default rw.assms-fast-image))

(%autoprove rw.fast-assms->ctrl-of-rw.assms-fast-image
            (%enable default rw.assms-fast-image))

(%autoprove equal-of-rw.fast-assms
            (%enable default rw.fast-assms
                     rw.fast-assmsp
                     rw.fast-assms->hypbox
                     rw.fast-assms->contradiction
                     rw.fast-assms->eqdatabase
                     rw.fast-assms->trueterms
                     rw.fast-assms->ctrl))



(%autoadmit rw.fast-assume-left)

(%autoprove rw.assms-fast-image-of-rw.assume-left
            (%enable default
                     rw.assms-fast-image
                     rw.assume-left
                     rw.fast-assume-left
                     rw.eqset->rhses))
(%autoprove rw.fast-assmsp-of-rw.fast-assume-left
            (%enable default rw.fast-assume-left))



(%autoadmit rw.fast-assume-right)

(%autoprove rw.assms-fast-image-of-rw.assume-right
            (%enable default
                     rw.assms-fast-image
                     rw.assume-right
                     rw.fast-assume-right
                     rw.eqset->rhses))

(%autoprove rw.fast-assmsp-of-rw.fast-assume-right
            (%enable default rw.fast-assume-right))



(%autoadmit rw.fast-assume-left-list)

(%autoprove rw.assms-fast-image-of-rw.assume-left-list
            (%cdr-induction nhyps)
            (%restrict default rw.fast-assume-left-list (equal nhyps 'nhyps)))

(%autoprove rw.fast-assmsp-of-rw.fast-assume-left-list
            (%cdr-induction nhyps)
            (%restrict default rw.fast-assume-left-list (equal nhyps 'nhyps)))




(%autoadmit rw.fast-assume-right-list)

(%autoprove rw.assms-fast-image-of-rw.assume-right-list
            (%cdr-induction nhyps)
            (%restrict default rw.fast-assume-right-list (equal nhyps 'nhyps)))

(%autoprove rw.fast-assmsp-of-rw.fast-assume-right-list
            (%cdr-induction nhyps)
            (%restrict default rw.fast-assume-right-list (equal nhyps 'nhyps)))



(%autoadmit rw.empty-fast-assms)
(%noexec rw.empty-fast-assms)

(%autoprove rw.assms-fast-image-of-rw.empty-assms
            (%forcingp nil)
            (%enable default
                     rw.empty-assms
                     rw.assms-fast-image
                     rw.empty-fast-assms
                     rw.empty-eqdatabase))

(%autoprove rw.fast-assmsp-of-rw.empty-assms
            (%forcingp nil)
            (%enable default
                     rw.empty-assms
                     rw.assms-fast-image
                     rw.empty-fast-assms
                     rw.empty-eqdatabase))



(%autoadmit rw.fast-assms-emptyp)

(%autoprove rw.fast-assms-emptyp-of-rw.assms-fast-image
            (%enable default
                     rw.fast-assms-emptyp
                     rw.assms-emptyp
                     rw.assms-fast-image))



(%autoadmit rw.fast-assms-formula)

(%autoprove rw.fast-assms-formula-of-rw.assms-fast-image
  (%enable default
           rw.fast-assms-formula
           rw.assms-formula
           rw.assms-fast-image))


(%autoadmit rw.fast-try-assms)

(%autoprove rw.fast-try-assms-of-rw.assms-fast-image
  (%enable default
           rw.fast-try-assms
           rw.try-assms
           rw.assms-fast-image))


(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/fast")
