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
(include-book "substitute-term")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund logic.flag-replace-subterm (flag x old new)
   ;; Replace all occurrences of old with new in x.  We don't descend into
   ;; lambda bodies.
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (and (equal flag 'list)
                                     (logic.term-listp x)))
                              (logic.termp old)
                              (logic.termp new))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((equal x old) new)
            ((logic.constantp x) x)
            ((logic.variablep x) x)
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (logic.function name (logic.flag-replace-subterm 'list args old new))))
            ((logic.lambdap x)
             (let ((formals (logic.lambda-formals x))
                   (body    (logic.lambda-body x))
                   (actuals (logic.lambda-actuals x)))
               (logic.lambda formals body (logic.flag-replace-subterm 'list actuals old new))))
            (t nil))
    (if (consp x)
        (cons (logic.flag-replace-subterm 'term (car x) old new)
              (logic.flag-replace-subterm 'list (cdr x) old new))
      nil)))

(definlined logic.replace-subterm (x old new)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp old)
                              (logic.termp new))
                  :verify-guards nil))
  (logic.flag-replace-subterm 'term x old new))

(definlined logic.replace-subterm-list (x old new)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.termp old)
                              (logic.termp new))
                  :verify-guards nil))
  (logic.flag-replace-subterm 'list x old new))

(defthmd definition-of-logic.replace-subterm
  (equal (logic.replace-subterm x old new)
         (cond ((equal x old) new)
               ((logic.constantp x) x)
               ((logic.variablep x) x)
               ((logic.functionp x)
                (let ((name (logic.function-name x))
                      (args (logic.function-args x)))
                  (logic.function name (logic.replace-subterm-list args old new))))
               ((logic.lambdap x)
                (let ((formals (logic.lambda-formals x))
                      (body    (logic.lambda-body x))
                      (actuals (logic.lambda-actuals x)))
                  (logic.lambda formals body (logic.replace-subterm-list actuals old new))))
               (t nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-replace-subterm
                                    logic.replace-subterm
                                    logic.replace-subterm-list))))

(defthmd definition-of-logic.replace-subterm-list
  (equal (logic.replace-subterm-list x old new)
         (if (consp x)
             (cons (logic.replace-subterm (car x) old new)
                   (logic.replace-subterm-list (cdr x) old new))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-replace-subterm
                                    logic.replace-subterm
                                    logic.replace-subterm-list))))

(defthm logic.flag-replace-subterm-of-term-removal
  (equal (logic.flag-replace-subterm 'term x old new)
         (logic.replace-subterm x old new))
  :hints(("Goal" :in-theory (enable logic.replace-subterm))))

(defthm logic.flag-replace-subterm-of-list-removal
  (equal (logic.flag-replace-subterm 'list x old new)
         (logic.replace-subterm-list x old new))
  :hints(("Goal" :in-theory (enable logic.replace-subterm-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.replace-subterm))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.replace-subterm-list))))

(defthm logic.replace-subterm-list-when-not-consp
  (implies (not (consp x))
           (equal (logic.replace-subterm-list x old new)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.replace-subterm-list))))

(defthm logic.replace-subterm-list-of-cons
  (equal (logic.replace-subterm-list (cons a x) old new)
         (cons (logic.replace-subterm a old new)
               (logic.replace-subterm-list x old new)))
  :hints(("Goal" :in-theory (enable definition-of-logic.replace-subterm-list))))

(defprojection :list (logic.replace-subterm-list x old new)
               :element (logic.replace-subterm x old new)
               :already-definedp t)



(defthms-flag
  :shared-hyp (force (logic.termp new))
  :thms ((term forcing-logic.termp-of-logic.replace-subterm
               (implies (force (logic.termp x))
                        (equal (logic.termp (logic.replace-subterm x old new))
                               t)))
         (t forcing-logic.term-listp-of-logic.replace-subterm-list
            (implies (force (logic.term-listp x))
                     (equal (logic.term-listp (logic.replace-subterm-list x old new))
                            t))))
  :hints (("Goal"
           :in-theory (enable definition-of-logic.replace-subterm)
           :restrict ((definition-of-logic.replace-subterm ((x x))))
           :induct (logic.term-induction flag x))))

(defthms-flag
   :shared-hyp (force (logic.term-atblp new atbl))
   :thms ((term forcing-logic.term-atblp-of-logic.replace-subterm
                (implies (force (logic.term-atblp x atbl))
                         (equal (logic.term-atblp (logic.replace-subterm x old new) atbl)
                                t)))
          (t forcing-logic.term-list-atblp-of-logic.replace-subterm-list
             (implies (force (logic.term-list-atblp x atbl))
                      (equal (logic.term-list-atblp (logic.replace-subterm-list x old new) atbl)
                             t))))
   :hints (("Goal"
            :in-theory (enable definition-of-logic.replace-subterm)
            :induct (logic.term-induction flag x)
            :restrict ((definition-of-logic.replace-subterm ((x x)))))))

(defthms-flag
  :shared-hyp (logic.variablep new)
  :thms ((term forcing-logic.substitute-of-logic.replace-subterm-with-fresh-variable
               (implies (and (not (memberp new (logic.term-vars x)))
                             (force (logic.termp x)))
                        (equal (logic.substitute (logic.replace-subterm x old new)
                                                 (list (cons new old)))
                               x)))
         (t forcing-logic.substitute-of-logic.replace-subterm-list-with-fresh-variable
            (implies (and (not (memberp new (logic.term-list-vars x)))
                          (force (logic.term-listp x)))
                     (equal (logic.substitute-list (logic.replace-subterm-list x old new)
                                                   (list (cons new old)))
                            (list-fix x)))))
  :hints (("Goal"
           :in-theory (enable definition-of-logic.replace-subterm)
           :induct (logic.term-induction flag x)
           :restrict ((definition-of-logic.replace-subterm-list ((x x)))))))



(verify-guards logic.flag-replace-subterm)
(verify-guards logic.replace-subterm)
(verify-guards logic.replace-subterm-list)




(defprojection :list (logic.replace-subterm-list-list x old new)
               :element (logic.replace-subterm-list x old new)
               :guard (and (logic.term-list-listp x)
                           (logic.termp old)
                           (logic.termp new)))

(defthm forcing-logic.term-list-listp-of-logic.replace-subterm-list-list
  (implies (force (and (logic.term-list-listp x)
                       (logic.termp new)))
           (equal (logic.term-list-listp (logic.replace-subterm-list-list x old new))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-list-atblp-of-logic.replace-subterm-list-list
  (implies (force (and (logic.term-list-list-atblp x atbl)
                       (logic.term-atblp new atbl)))
           (equal (logic.term-list-list-atblp (logic.replace-subterm-list-list x old new) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-listp-of-logic.replace-subterm-list-list
  (equal (cons-listp (logic.replace-subterm-list-list x old new))
         (cons-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.substitute-of-logic.replace-subterm-list-list-with-fresh-variable
   (implies (and (not (memberp new (logic.term-list-list-vars x)))
                 (logic.variablep new)
                 (force (logic.term-list-listp x)))
            (equal (logic.substitute-list-list (logic.replace-subterm-list-list x old new)
                                               (list (cons new old)))
                   (list-list-fix x)))
   :hints(("Goal" :induct (cdr-induction x))))

