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
(include-book "eqtracep")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(definlined rw.direct-iff-eqtrace (okp nhyp)
  ;; Try to generate a direct eqtrace from an nhyp.
  ;; The nhyp should have one of these forms:
  ;;   -- (not* (iff lhs rhs))
  ;;   -- (not* (iff rhs lhs))
  ;; Where lhs and rhs are distinct.
  (declare (xargs :guard (logic.termp nhyp)))
  (and okp
       (clause.negative-termp nhyp)
       (let ((guts (clause.negative-term-guts nhyp)))
         (and (logic.functionp guts)
              (equal (logic.function-name guts) 'iff)
              (let ((args (logic.function-args guts)))
                (and (equal (len args) 2)
                     (let ((lhs (first args))
                           (rhs (second args)))
                       (cond ((logic.term-< lhs rhs)
                              (rw.eqtrace 'direct-iff t lhs rhs nil))
                             ((logic.term-< rhs lhs)
                              (rw.eqtrace 'direct-iff t rhs lhs nil))
                             (t
                              ;; Lhs and rhs are not distinct.  We would be
                              ;; assuming lhs iff lhs, which is useless.
                              nil)))))))))

(encapsulate
 ()
 (local (in-theory (enable rw.direct-iff-eqtrace)))

 (defthm forcing-rw.eqtrace->method-of-rw.direct-iff-eqtrace
   (implies (force (rw.direct-iff-eqtrace okp nhyp))
            (equal (rw.eqtrace->method (rw.direct-iff-eqtrace okp nhyp))
                   'direct-iff)))

 (defthm forcing-rw.eqtrace->iffp-of-rw.direct-iff-eqtrace
   (implies (force (rw.direct-iff-eqtrace okp nhyp))
            (equal (rw.eqtrace->iffp (rw.direct-iff-eqtrace okp nhyp))
                   t)))

 (defthm forcing-rw.eqtrace->subtraces-of-rw.direct-iff-eqtrace
   (implies (force (rw.direct-iff-eqtrace okp nhyp))
            (equal (rw.eqtrace->subtraces (rw.direct-iff-eqtrace okp nhyp))
                   nil)))

 (defthm forcing-rw.eqtracep-of-rw.direct-iff-eqtrace
   (implies (force (and (rw.direct-iff-eqtrace okp nhyp)
                        (logic.termp nhyp)))
            (equal (rw.eqtracep (rw.direct-iff-eqtrace okp nhyp))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.direct-iff-eqtrace
   (implies (force (and (rw.direct-iff-eqtrace okp nhyp)
                        (logic.termp nhyp)
                        (logic.term-atblp nhyp atbl)))
            (equal (rw.eqtrace-atblp (rw.direct-iff-eqtrace okp nhyp) atbl)
                   t)))


 (defthm rw.direct-iff-eqtrace-normalize-okp-1
   (implies (and (rw.direct-iff-eqtrace okp nhyp)
                 (syntaxp (not (equal okp ''t))))
            (equal (rw.direct-iff-eqtrace okp nhyp)
                   (rw.direct-iff-eqtrace t nhyp))))

 (defthm rw.direct-iff-eqtrace-normalize-okp-2
   (implies (not (rw.direct-iff-eqtrace t nhyp))
            (equal (rw.direct-iff-eqtrace okp nhyp)
                   nil)))

 (defthm rw.direct-iff-eqtrace-normalize-okp-3
   (equal (rw.direct-iff-eqtrace nil nhyp)
          nil)))





(defund rw.find-nhyp-for-direct-iff-eqtracep (nhyps x)
  ;; Find the first nhyp in a list that would generate this direct-iff eqtrace.
  (declare (xargs :guard (and (logic.term-listp nhyps)
                              (rw.eqtracep x))))
  (if (consp nhyps)
      (if (equal (rw.direct-iff-eqtrace t (car nhyps)) x)
          (car nhyps)
        (rw.find-nhyp-for-direct-iff-eqtracep (cdr nhyps) x))
    nil))

(encapsulate
 ()
 (local (in-theory (enable rw.find-nhyp-for-direct-iff-eqtracep)))

 (defthm rw.find-nhyp-for-direct-iff-eqtracep-of-nil
   (equal (rw.find-nhyp-for-direct-iff-eqtracep nil x)
          nil))

 (defthm forcing-logic.termp-of-rw.find-nhyp-for-direct-iff-eqtracep
   (implies (force (and (rw.find-nhyp-for-direct-iff-eqtracep nhyps x)
                        (logic.term-listp nhyps)))
            (equal (logic.termp (rw.find-nhyp-for-direct-iff-eqtracep nhyps x))
                   t)))

 (defthm forcing-logic.term-atblp-of-rw.find-nhyp-for-direct-iff-eqtracep
   (implies (force (and (rw.find-nhyp-for-direct-iff-eqtracep nhyps x)
                        (logic.term-list-atblp nhyps atbl)))
            (equal (logic.term-atblp (rw.find-nhyp-for-direct-iff-eqtracep nhyps x) atbl)
                   t)))

 (defthm forcing-memberp-of-rw.find-nhyp-for-direct-iff-eqtracep
   (implies (force (rw.find-nhyp-for-direct-iff-eqtracep nhyps x))
            (equal (memberp (rw.find-nhyp-for-direct-iff-eqtracep nhyps x) nhyps)
                   t)))

 (defthm forcing-rw.direct-iff-eqtrace-of-rw.find-nhyp-for-direct-iff-eqtracep
   (implies (force (rw.find-nhyp-for-direct-iff-eqtracep nhyps x))
            (equal (rw.direct-iff-eqtrace t (rw.find-nhyp-for-direct-iff-eqtracep nhyps x))
                   x))))




(defund rw.direct-iff-eqtrace-okp (x box)
  ;; Check if any nhyp in the hypbox would generate this direct-iff eqtrace.
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box))))
  (and (equal (rw.eqtrace->method x) 'direct-iff)
       (equal (rw.eqtrace->iffp x) t)
       (if (or (rw.find-nhyp-for-direct-iff-eqtracep (rw.hypbox->left box) x)
               (rw.find-nhyp-for-direct-iff-eqtracep (rw.hypbox->right box) x))
           t
         nil)))

(encapsulate
 ()
 (local (in-theory (enable rw.direct-iff-eqtrace-okp)))

 (defthm booleanp-of-rw.direct-iff-eqtrace-okp
   (equal (booleanp (rw.direct-iff-eqtrace-okp x box))
          t)
   :hints(("Goal" :in-theory (disable forcing-booleanp-of-rw.eqtrace->iffp))))

 (defthmd lemma-for-forcing-rw.direct-iff-eqtrace-okp-rw.direct-iff-eqtrace
   (implies (and (memberp nhyp nhyps)
                 (rw.direct-iff-eqtrace okp nhyp))
            (iff (rw.find-nhyp-for-direct-iff-eqtracep nhyps (rw.direct-iff-eqtrace okp nhyp))
                 nhyp))
   :hints(("Goal" :in-theory (enable rw.find-nhyp-for-direct-iff-eqtracep))))

 (defthm forcing-rw.direct-iff-eqtrace-okp-rw.direct-iff-eqtrace
   (implies (force (and (rw.direct-iff-eqtrace okp nhyp)
                        (or (memberp nhyp (rw.hypbox->left box))
                            (memberp nhyp (rw.hypbox->right box)))))
            (equal (rw.direct-iff-eqtrace-okp (rw.direct-iff-eqtrace okp nhyp) box)
                   t))
   :hints(("Goal" :in-theory (e/d (lemma-for-forcing-rw.direct-iff-eqtrace-okp-rw.direct-iff-eqtrace)
                                  (rw.direct-iff-eqtrace-normalize-okp-1))))))

