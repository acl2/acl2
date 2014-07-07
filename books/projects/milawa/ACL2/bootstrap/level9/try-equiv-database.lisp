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
(include-book "eqdatabasep")
(%interactive)


(defsection rw.eqtrace-list-lookup
  (%autoadmit rw.eqtrace-list-lookup)
  (local (%restrict default rw.eqtrace-list-lookup (equal eqtraces 'eqtraces)))
  (%autoprove forcing-rw.eqtrace-list-lookup-under-iff
              ;; BOZO inappropriately uses x
              (%autoinduct rw.eqtrace-list-lookup x eqtraces))
  (%autoprove forcing-rw.eqtracep-of-rw.eqtrace-list-lookup
              (%autoinduct rw.eqtrace-list-lookup))
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.eqtrace-list-lookup
              (%autoinduct rw.eqtrace-list-lookup))
  (%autoprove forcing-rw.eqtrace-okp-of-rw.eqtrace-list-lookup
              (%autoinduct rw.eqtrace-list-lookup))
  (%autoprove forcing-memberp-of-rw.eqtrace-list-lookup
              (%autoinduct rw.eqtrace-list-lookup))
  (%autoprove forcing-eqtrace->rhs-of-rw.eqtrace-list-lookup
              (%autoinduct rw.eqtrace-list-lookup))
  (%autoprove rw.eqtrace->lhs-of-rw.eqtrace-list-lookup-when-all-equalp
              (%disable default forcing-rw.eqtrace-list-lookup-under-iff))
  (%autoprove forcing-rw.eqtrace->iffp-of-rw.eqtrace-list-lookup-in-rw.eqset->tail
              (%use (%instance (%thm rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps)
                               (a    (rw.eqtrace-list-lookup term (rw.eqset->tail eqset)))
                               (x    (rw.eqset->tail eqset))
                               (iffp (rw.eqset->iffp eqset)))))
  (%autoprove forcing-rw.eqtrace->lhs-of-rw.eqtrace-list-lookup-in-rw.eqset->tail
              (%use (%instance (%thm rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses)
                               (a    (rw.eqtrace-list-lookup term (rw.eqset->tail eqset)))
                               (x    (rw.eqset->tail eqset))
                               (lhs  (rw.eqset->head eqset))))))


(defsection rw.eqset-lookup
  (%autoadmit rw.eqset-lookup)
  (local (%enable default rw.eqset-lookup))
  (%autoprove rw.eqset-lookup-of-term-and-nil)
  (%autoprove forcing-rw.eqtracep-of-rw.eqset-lookup)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.eqset-lookup)
  (%autoprove forcing-rw.eqtrace-okp-of-rw.eqset-lookup)
  (%autoprove forcing-memberp-of-rw.eqset-lookup)
  (%autoprove forcing-eqtrace->iffp-of-rw.eqset-lookup)
  (%autoprove forcing-eqtrace->rhs-of-rw.eqset-lookup)
  (%autoprove forcing-eqtrace->lhs-of-rw.eqset-lookup))


(%autoprove lemma-for-rw.eqset-lookup-of-rw.eqset->head (%cdr-induction x))
(%autoprove lemma-2-for-rw.eqset-lookup-of-rw.eqset->head (%cdr-induction x))
(%autoprove forcing-rw.eqset-lookup-of-rw.eqset->head
            (%enable default
                     rw.eqset-lookup
                     lemma-for-rw.eqset-lookup-of-rw.eqset->head
                     lemma-2-for-rw.eqset-lookup-of-rw.eqset->head))


(%autoprove forcing-rw.eqset-lookup-of-rw.eqset->head-free)

(%autoprove forcing-memberp-of-rw.eqset->head-in-rw.eqtrace-list-rhses-of-rw.eqset->tail
            (%use (%instance (%thm lemma-for-rw.eqset-lookup-of-rw.eqset->head)
                             (lhs (rw.eqset->head eqset))
                             (x   (rw.eqset->tail eqset)))))

(%autoprove forcing-memberp-of-rw.eqset->head-in-rw.eqtrace-list-rhses-of-rw.eqset->tail-free)

(%autoprove forcing-memberp-of-rw.eqtrace-list-rhses-of-rw.eqset->tail-when-smaller-than-head
            (%use (%instance (%thm lemma-for-rw.eqset-lookup-of-rw.eqset->head)
                             (lhs (rw.eqset->head eqset))
                             (x   (rw.eqset->tail eqset)))))

(%autoprove forcing-logic.term-<-of-rw.eqset->head-when-rw.eqset-lookup
            (%enable default
                     rw.eqset-lookup
                     lemma-for-rw.eqset-lookup-of-rw.eqset->head
                     lemma-2-for-rw.eqset-lookup-of-rw.eqset->head))


(defsection rw.eqset-list-lookup
  (%autoadmit rw.eqset-list-lookup)
  (local (%restrict default rw.eqset-list-lookup (equal eqsets 'eqsets)))
  (%autoprove forcing-rw.eqtracep-of-rw.eqset-list-lookup
              (%cdr-induction eqsets))
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.eqset-list-lookup
              (%cdr-induction eqsets))
  (%autoprove forcing-rw.eqtrace-okp-of-rw.eqset-list-lookup
              (%cdr-induction eqsets))
  (%autoprove forcing-eqtrace->rhs-of-rw.eqset-list-lookup
              (%cdr-induction eqsets))
  (%autoprove forcing-rw.eqtrace->iffp-of-rw.eqset-list-lookup-when-all-equalp
              (%cdr-induction eqsets)))


(defsection rw.try-equiv-database
  (%autoadmit rw.try-equiv-database)
  (local (%enable default rw.try-equiv-database))
  (%autoprove forcing-rw.eqtracep-of-rw.try-equiv-database)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.try-equiv-database)
  (%autoprove forcing-rw.eqtrace-okp-of-rw.try-equiv-database)
  (%autoprove forcing-eqtrace->rhs-of-rw.try-equiv-database)
  (%autoprove forcing-eqtrace->iffp-of-rw.try-equiv-database
              (%use (%instance (%thm forcing-rw.eqtrace->iffp-of-rw.eqset-list-lookup-when-all-equalp)
                               (iffp nil)
                               (eqsets (rw.eqdatabase->equalsets database))
                               (term term)))
              (%use (%instance (%thm forcing-rw.eqtrace->iffp-of-rw.eqset-list-lookup-when-all-equalp)
                               (iffp t)
                               (eqsets (rw.eqdatabase->iffsets database))
                               (term term)))))


(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/try-equiv-database")

