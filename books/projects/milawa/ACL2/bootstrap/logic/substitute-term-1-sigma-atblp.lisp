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
(include-book "terms")
(%interactive)


(%defmap :map (logic.sigma-atblp x atbl)
         :key (logic.variablep x)
         :val (logic.term-atblp x atbl)
         :key-list (logic.variable-listp x)
         :val-list (logic.term-list-atblp x atbl)
         :val-of-nil nil)

;; (DEFSECTION LOGIC.SIGMA-ATBLP
;; (%AUTOADMIT LOGIC.SIGMA-ATBLP)
;; (%AUTOPROVE LOGIC.SIGMA-ATBLP-WHEN-NOT-CONSP
;;               (%RESTRICT DEFAULT LOGIC.SIGMA-ATBLP (EQUAL X 'X)))
;; (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-CONS
;;               (%RESTRICT DEFAULT LOGIC.SIGMA-ATBLP
;;                          (EQUAL X '(CONS A X))))
;; (%AUTOPROVE CONSP-WHEN-MEMBERP-OF-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X)
;;               (%AUTO)
;;               (%CAR-CDR-ELIM X))
;; (%AUTOPROVE CONSP-WHEN-MEMBERP-OF-LOGIC.SIGMA-ATBLP-ALT)
;; (%AUTOPROVE LOGIC.VARIABLEP-OF-CAR-WHEN-MEMBERP-OF-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X)
;;               (%AUTO)
;;               (%CAR-CDR-ELIM X))
;; (%AUTOPROVE LOGIC.VARIABLEP-WHEN-LOOKUP-IN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X)
;;               (%AUTO)
;;               (%CAR-CDR-ELIM X))
;; (%AUTOPROVE LOGIC.TERM-ATBLP-OF-CDR-WHEN-MEMBERP-OF-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X)
;;               (%AUTO)
;;               (%CAR-CDR-ELIM X))
;; (%AUTOPROVE BOOLEANP-OF-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;; (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-LIST-FIX
;;               (%CDR-INDUCTION X))



;; (ACL2::defttag disable-caching)

;; (ACL2::progn!
;;  (ACL2::set-raw-mode t)
;;  (ACL2::defun rw.cache-update (term trace cache)
;;               (declare (xargs :guard (and (logic.termp term)
;;                                           (rw.tracep trace)
;;                                           (rw.cachep cache)))
;;                        (ignore term trace))
;;               cache)
;;  (ACL2::defun rw.cache-lookup (term iffp cache)
;;               (declare (xargs :guard (and (logic.termp term)
;;                                           (booleanp iffp)
;;                                           (rw.cachep cache)))
;;                        (ignore term iffp cache))
;;               nil))



;; (%AUTORULE LOGIC.SIGMA-ATBLP-OF-APP)
;; (%CDR-INDUCTION X)
;; ;; (%auto):
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; Progress; 11 goals remain
;; (%cleanup)
;; ;; Progress; 4 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; Progress; 8 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; No progress
;; (%distribute)
;; ;; No progress
;; (%urewrite default)
;; ;; Progress; 8 goals remain
;; (%cleanup)
;; ;; Progress; 7 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; No progress
;; (%distribute)
;; ;; No progress
;; (%urewrite default)
;; ;; No progress
;; (%profile)
;; (%crewrite default)                           ;; THE FIRST REWRITE
;; (%profile.report)
;; (%profile.clear)
;; ; Rewrote 7 clauses; 4 remain (0 forced)
;; ;; Progress; 4 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; Progress; 16 goals remain
;; (%cleanup)
;; ;; Progress; 7 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; No progress
;; (%distribute)
;; ;; No progress
;; (%urewrite default)
;; ;; No progress
;; (%crewrite default)                            ;; THE SECOND REWRITE
;; (%profile.report)

;; ;; No progress
;; (%auto-elim)
;; ;; Progress; 15 goals remain
;; (%cleanup)
;; ;; Progress; 8 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; No progress
;; (%distribute)
;; ;; No progress
;; (%urewrite default)
;; ;; Progress; 8 goals remain
;; (%cleanup)
;; ;; Progress; 8 goals remain
;; (%cleanup)
;; ;; No progress
;; (%split)
;; ;; Progress; 114 goals remain
;; (%cleanup)
;; ;; Progress; 0 goals remain
;; ;All goals have been proven.



;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-REV
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-REMOVE-ALL-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-REMOVE-DUPLICATES
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-DIFFERENCE-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-SUBSET-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.SIGMA-ATBLP-OF-SUBSET-WHEN-LOGIC.SIGMA-ATBLP-ALT)
;;   (%AUTOPROVE LOGIC.VARIABLE-LISTP-OF-DOMAIN-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.TERM-LIST-ATBLP-OF-RANGE-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE MAPP-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE LOGIC.TERM-ATBLP-OF-CDR-OF-LOOKUP-WHEN-LOGIC.SIGMA-ATBLP
;;               (%CDR-INDUCTION X))
;;   (%AUTOPROVE
;;    CDR-OF-LOOKUP-UNDER-IFF-WHEN-LOGIC.SIGMA-ATBLP
;;    (%USE
;;        (%INSTANCE
;;             (%THM LOGIC.TERM-ATBLP-OF-CDR-OF-LOOKUP-WHEN-LOGIC.SIGMA-ATBLP)))
;;    (%DISABLE DEFAULT
;;              LOGIC.TERM-ATBLP-OF-CDR-OF-LOOKUP-WHEN-LOGIC.SIGMA-ATBLP)))



(%autoprove forcing-logic.sigma-atblp-of-pair-lists
            (%autoinduct pair-lists))



(%deflist logic.sigma-list-atblp (x atbl)
  (logic.sigma-atblp x atbl))

(%autoprove logic.sigma-atblp-of-second-when-logic.sigma-list-atblp)

(%autoprove forcing-logic.sigma-list-atblp-of-revappend-onto-each
            (%cdr-induction x))



(%deflist logic.sigma-list-list-atblp (x atbl)
  (logic.sigma-list-atblp x atbl))

