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


(definlined rw.primary-eqtrace (okp nhyp)
  ;; We try to assume lhs = rhs from an nhyp of one of the following forms:
  ;;   -- (not* (equal lhs rhs))
  ;;   -- (not* (equal rhs lhs))
  ;; This is only useful if lhs and rhs are distinct.  Otherwise, we would
  ;; just be assuming lhs = lhs, which is not very informative.
  ;;
  ;; We only try to build the trace when okp is true.  This allows us to
  ;; turn off trace construction easily, at a high level, without adding
  ;; case splits.
  (declare (xargs :guard (and (booleanp okp)
                              (logic.termp nhyp))))
  (and okp
       (clause.negative-termp nhyp)
       (let ((guts (clause.negative-term-guts nhyp)))
         (and (logic.functionp guts)
              (equal (logic.function-name guts) 'equal)
              (let ((args (logic.function-args guts)))
                (and (equal (len args) 2)
                     (let ((lhs (first args))
                           (rhs (second args)))
                       (cond ((logic.term-< lhs rhs)
                              (rw.eqtrace 'primary nil lhs rhs nil))
                             ((logic.term-< rhs lhs)
                              (rw.eqtrace 'primary nil rhs lhs nil))
                             (t
                              nil)))))))))

(encapsulate
 ()
 (local (in-theory (enable rw.primary-eqtrace)))

 (defthm forcing-rw.eqtrace->method-of-rw.primary-eqtrace
   (implies (force (rw.primary-eqtrace okp nhyp))
            (equal (rw.eqtrace->method (rw.primary-eqtrace okp nhyp))
                   'primary)))

 (defthm forcing-rw.eqtrace->iffp-of-rw.primary-eqtrace
   (implies (force (rw.primary-eqtrace okp nhyp))
            (equal (rw.eqtrace->iffp (rw.primary-eqtrace okp nhyp))
                   nil)))

 (defthm forcing-rw.eqtrace->subtraces-of-rw.primary-eqtrace
   (implies (force (rw.primary-eqtrace okp nhyp))
            (equal (rw.eqtrace->subtraces (rw.primary-eqtrace okp nhyp))
                   nil)))

 (defthm forcing-rw.eqtracep-of-rw.primary-eqtrace
   (implies (force (and (rw.primary-eqtrace okp nhyp)
                        (logic.termp nhyp)))
            (equal (rw.eqtracep (rw.primary-eqtrace okp nhyp))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.primary-eqtrace
   (implies (force (and (rw.primary-eqtrace okp nhyp)
                        (logic.termp nhyp)
                        (logic.term-atblp nhyp atbl)))
            (equal (rw.eqtrace-atblp (rw.primary-eqtrace okp nhyp) atbl)
                   t)))

 (defthm rw.primary-eqtrace-normalize-okp-1
   (implies (and (rw.primary-eqtrace okp nhyp)
                 (syntaxp (not (equal okp ''t))))
            (equal (rw.primary-eqtrace okp nhyp)
                   (rw.primary-eqtrace t nhyp))))

 (defthm rw.primary-eqtrace-normalize-okp-2
   (implies (not (rw.primary-eqtrace t nhyp))
            (equal (rw.primary-eqtrace okp nhyp)
                   nil)))

 (defthm rw.primary-eqtrace-normalize-okp-3
   (equal (rw.primary-eqtrace nil nhyp)
          nil)))




(defund rw.find-nhyp-for-primary-eqtracep (nhyps x)
  ;; Find the first nhyp in a list that would generate this primary eqtrace.
  (declare (xargs :guard (and (logic.term-listp nhyps)
                              (rw.eqtracep x))))
  (if (consp nhyps)
      (if (equal (rw.primary-eqtrace t (car nhyps)) x)
          (car nhyps)
        (rw.find-nhyp-for-primary-eqtracep (cdr nhyps) x))
    nil))

(encapsulate
 ()
 (local (in-theory (enable rw.find-nhyp-for-primary-eqtracep)))

 (defthm rw.find-nhyp-for-primary-eqtracep-of-nil
   (equal (rw.find-nhyp-for-primary-eqtracep nil x)
          nil))

 (defthm forcing-logic.termp-of-rw.find-nhyp-for-primary-eqtracep
   (implies (force (and (rw.find-nhyp-for-primary-eqtracep nhyps x)
                        (logic.term-listp nhyps)))
            (equal (logic.termp (rw.find-nhyp-for-primary-eqtracep nhyps x))
                   t)))

 (defthm forcing-logic.term-atblp-of-rw.find-nhyp-for-primary-eqtracep
   (implies (force (and (rw.find-nhyp-for-primary-eqtracep nhyps x)
                        (logic.term-list-atblp nhyps atbl)))
            (equal (logic.term-atblp (rw.find-nhyp-for-primary-eqtracep nhyps x) atbl)
                   t)))

 (defthm forcing-memberp-of-rw.find-nhyp-for-primary-eqtracep
   (implies (force (rw.find-nhyp-for-primary-eqtracep nhyps x))
            (equal (memberp (rw.find-nhyp-for-primary-eqtracep nhyps x) nhyps)
                   t)))

 (defthm forcing-rw.primary-eqtrace-of-rw.find-nhyp-for-primary-eqtracep
   (implies (force (rw.find-nhyp-for-primary-eqtracep nhyps x))
            (equal (rw.primary-eqtrace t (rw.find-nhyp-for-primary-eqtracep nhyps x))
                   x))))




(defund rw.primary-eqtrace-okp (x box)
  ;; Check if any nhyp in the hypbox would generate this primary eqtrace.
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box))))
  (and (equal (rw.eqtrace->method x) 'primary)
       (equal (rw.eqtrace->iffp x) nil)
       (if (or (rw.find-nhyp-for-primary-eqtracep (rw.hypbox->left box) x)
               (rw.find-nhyp-for-primary-eqtracep (rw.hypbox->right box) x))
           t
         nil)))

(encapsulate
 ()
 (local (in-theory (enable rw.primary-eqtrace-okp)))

 (defthm booleanp-of-rw.primary-eqtrace-okp
   (equal (booleanp (rw.primary-eqtrace-okp x box))
          t))

 (defthmd lemma-for-forcing-rw.primary-eqtrace-okp-rw.primary-eqtrace
   (implies (and (memberp nhyp nhyps)
                 (rw.primary-eqtrace okp nhyp))
            (iff (rw.find-nhyp-for-primary-eqtracep nhyps (rw.primary-eqtrace okp nhyp))
                 nhyp))
   :hints(("Goal" :in-theory (enable rw.find-nhyp-for-primary-eqtracep))))


 (defthm forcing-rw.primary-eqtrace-okp-rw.primary-eqtrace
   (implies (force (and (rw.primary-eqtrace okp nhyp)
                        (or (memberp nhyp (rw.hypbox->left box))
                            (memberp nhyp (rw.hypbox->right box)))))
            (equal (rw.primary-eqtrace-okp (rw.primary-eqtrace okp nhyp) box)
                   t))
   :hints(("Goal" :in-theory (e/d (lemma-for-forcing-rw.primary-eqtrace-okp-rw.primary-eqtrace)
                                  (rw.primary-eqtrace-normalize-okp-1)
                                  )))))

