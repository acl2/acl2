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
(%interactive)


;; BOZO this is duplicated in basic-builders.  Move it to all-equalp.lisp
(%autoprove all-equalp-removal
            (%cdr-induction x)
            (%restrict default repeat (equal n '(+ '1 (len (cdr x))))))

(defsection rw.eqsetp

  (%autoadmit rw.eqsetp)
  (%autoadmit rw.eqset->head)
  (%autoadmit rw.eqset->iffp)
  (%autoadmit rw.eqset->tail)
  (%autoadmit rw.eqset)

  (local (%enable default
                  rw.eqsetp
                  rw.eqset->head
                  rw.eqset->iffp
                  rw.eqset->tail
                  rw.eqset))

  (%autoprove booleanp-of-rw.eqsetp)
  (%autoprove rw.eqset->head-of-rw.eqset)
  (%autoprove rw.eqset->iffp-of-rw.eqset)
  (%autoprove rw.eqset->tail-of-rw.eqset)
  (%autoprove forcing-rw.eqsetp-of-rw.eqset)
  (%autoprove forcing-logic.termp-of-rw.eqset->head)
  (%autoprove forcing-booleanp-of-rw.eqset->iffp)
  (%autoprove forcing-consp-of-rw.eqset->tail)
  (%autoprove forcing-true-listp-of-rw.eqset->tail)
  (%autoprove forcing-rw.eqtrace-listp-of-rw.eqset->tail)
  (%autoprove forcing-rw.eqtrace-list-iffps-of-rw.eqset->tail
              (%enable default all-equalp-removal))
  (%autoprove forcing-rw.eqtrace-list-lhses-of-rw.eqset->tail
              (%enable default all-equalp-removal))
  (%autoprove forcing-uniquep-of-rw.eqtrace-list-rhses-of-rw.eqset->tail))


(%deflist rw.eqset-listp (x)
          (rw.eqsetp x))


(defsection rw.eqset-atblp

  (%autoadmit rw.eqset-atblp)

  (local (%enable default rw.eqset-atblp))

  (%autoprove booleanp-of-rw.eqset-atblp)
  (%autoprove forcing-rw.eqset-atblp-of-rw.eqset)
  (%autoprove forcing-rw.eqtrace-list-atblp-of-rw.eqset->tail)
  (%autoprove lemma-for-forcing-logic.term-atblp-of-rw.eqset->head)

  (%autoprove forcing-logic.term-atblp-of-rw.eqset->head
              (%disable default
                        forcing-rw.eqtrace-list-atblp-of-rw.eqset->tail
                        forcing-rw.eqtrace-list-lhses-of-rw.eqset->tail)
              (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-rw.eqset->head)
                               (x    (rw.eqtrace-list-lhses (rw.eqset->tail x)))
                               (term (rw.eqset->head x))
                               (len  (len (rw.eqset->tail x)))))
              (%use (%instance (%thm forcing-rw.eqtrace-list-lhses-of-rw.eqset->tail))))

  (%autoprove rw.eqset-atblp-of-nil))


(%deflist rw.eqset-list-atblp (x atbl)
          (rw.eqset-atblp x atbl))


(defsection rw.eqset-okp
  (%autoadmit rw.eqset-okp)
  (local (%enable default rw.eqset-okp))
  (%autoprove booleanp-of-rw.eqset-okp)
  (%autoprove forcing-rw.eqtrace-list-okp-of-rw.eqset->tail)
  (%autoprove rw.eqset-okp-of-rw.eqset)
  (%autoprove rw.eqset-okp-of-nil))


(%deflist rw.eqset-list-okp (x box)
          (rw.eqset-okp x box))



(%defprojection :list (rw.eqset-list-heads x)
                :element (rw.eqset->head x)
                :nil-preservingp t)

(%autoprove forcing-logic.term-listp-of-rw.eqset-list-heads
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-rw.eqset-list-heads
            (%cdr-induction x))


(defsection rw.eqset-list-iffps
  (local (%forcingp nil))
  (%defprojection :list (rw.eqset-list-iffps x)
                  :element (rw.eqset->iffp x)
                  :nil-preservingp t))



(%autoadmit rw.eqset->rhses)

(%autoprove forcing-logic.term-listp-of-rw.eqset->rhses
            (%enable default rw.eqset->rhses))

(%autoprove forcing-logic.term-list-atblp-of-rw.eqset->rhses
            (%enable default rw.eqset->rhses))




(%defprojection :list (rw.eqset-list-rhses x)
                :element (rw.eqset->rhses x)
                :nil-preservingp t)

(%autoprove forcing-logic.term-list-listp-of-rw.eqset-list-rhses
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-rw.eqrow-list-rhses
            (%cdr-induction x))



(defsection rw.find-contradiction-in-eqset-list
  (%autoadmit rw.find-contradiction-in-eqset-list)
  (local (%restrict default rw.find-contradiction-in-eqset-list (equal x 'x)))
  (%autoprove forcing-rw.eqtracep-of-rw.find-contradiction-in-eqrow-list
              (%cdr-induction x))
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.find-contradiction-in-eqset-list
              (%cdr-induction x))
  (%autoprove forcing-rw.eqtrace-okp-of-rw.find-contradiction-in-eqset-list
              (%cdr-induction x))
  (%autoprove forcing-rw.eqtrace-contradictionp-of-rw.find-contradiction-in-eqset-list
              (%cdr-induction x)))



(defsection rw.eqdatabasep

  (%autoadmit rw.eqdatabasep)
  (%autoadmit rw.eqdatabase->equalsets)
  (%autoadmit rw.eqdatabase->iffsets)
  (%autoadmit rw.eqdatabase->contradiction)
  (%autoadmit rw.eqdatabase)

  (local (%enable default
                  rw.eqdatabasep
                  rw.eqdatabase->equalsets
                  rw.eqdatabase->iffsets
                  rw.eqdatabase->contradiction
                  rw.eqdatabase))

  (%autoprove booleanp-of-rw.eqdatabasep)
  (%autoprove rw.eqdatabase->equalsets-of-rw.eqdatabase)
  (%autoprove rw.eqdatabase->iffsets-of-rw.eqdatabase)
  (%autoprove rw.eqdatabase->contradiction-of-rw.eqdatabase)
  (%autoprove forcing-rw.eqdatabasep-of-rw.eqdatabase)
  (%autoprove forcing-rw.eqset-listp-of-rw.eqdatabase->equalsets)
  (%autoprove forcing-uniquep-of-rw.eqset-list-heads-of-rw.eqdatabase->equalsets)
  (%autoprove forcing-disjoint-from-allp-of-rw.eqrow-list-heads-of-rw.eqdatabase->equalsets)
  (%autoprove forcing-mutually-disjointp-of-rw.eqrow-list-rhses-of-rw.eqdatabase->equalsets)

  (%autoprove forcing-rw.eqset-list-iffps-of-rw.eqdatabase->equalsets
              (%enable default all-equalp-removal))

  (%autoprove forcing-rw.eqset-listp-of-rw.eqdatabase->iffsets)
  (%autoprove forcing-uniquep-of-rw.eqset-list-heads-of-rw.eqdatabase->iffsets)
  (%autoprove forcing-disjoint-from-allp-of-rw.eqset-list-heads-of-rw.eqdatabase->iffsets)
  (%autoprove forcing-mutually-disjointp-of-rw.eqset-list-rhses-of-rw.eqdatabase->iffsets)

  (%autoprove forcing-rw.eqset-list-iffps-of-rw.eqdatabase->iffsets
              (%enable default all-equalp-removal))

  (%autoprove forcing-rw.eqtracep-of-rw.eqdatabase->contradiction)
  (%autoprove forcing-rw.eqtrace-contradictionp-of-rw.eqdatabase->contradiction))


(defsection rw.eqdatabase-atblp
  (%autoadmit rw.eqdatabase-atblp)
  (local (%enable default rw.eqdatabase-atblp))
  (%autoprove rw.eqdatabase-atblp-of-nil)
  (%autoprove booleanp-of-rw.eqdatabase-atblp)
  (%autoprove forcing-rw.eqdatabase-atblp-of-rw.eqdatabase)
  (%autoprove forcing-rw.eqset-list-atblp-of-rw.eqdatabase->equalsets)
  (%autoprove forcing-rw.eqset-list-atblp-of-rw.eqdatabase->iffsets)
  (%autoprove forcing-rw.trace-atblp-of-rw.eqdatabase->contradiction))


(defsection rw.eqdatabase-okp
  (%autoadmit rw.eqdatabase-okp)
  (local (%enable default rw.eqdatabase-okp))
  (%autoprove booleanp-of-rw.eqdatabase-okp)
  (%autoprove forcing-rw.eqdatabase-okp-of-rw.eqdatabase)
  (%autoprove forcing-rw.eqset-list-okp-of-rw.eqdatabase->equalsets)
  (%autoprove forcing-rw.eqset-list-okp-of-rw.eqdatabase->iffsets)
  (%autoprove forcing-rw.trace-okp-of-rw.eqdatabase->contradiction))



(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/eqdatabasep"
                                         ;; BOZO this is getting killed
                                         all-equalp-as-repeat
                                         )