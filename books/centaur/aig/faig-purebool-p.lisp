; Centaur AIG Library
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "aig-sat")
(include-book "faig-base")

(local (in-theory (disable faig-eval)))

(defsection faig-purebool-p
  :parents (faig)
  :short "Does a FAIG always evaluate to a purely Boolean value, i.e., is it
never X or Z?"

  :long "<p>When an FAIG is known to be purely Boolean, then there is not much
reason to represent it as an FAIG&mdash;we might as well throw its offset away
and just work with its onset as an AIG.</p>

<p>When you are dealing with nice, well-behaved, RTL-level circuits that don't
use any fancy low-level, four-valued sorts of things like tri-state buffers,
this can be a useful optimization.  For instance, it may reduce the complexity
of SAT queries, or carry out other kinds of analysis where you don't have to
think about four-valuedness.</p>

<p>@(call faig-purebool-p) is a logically nice, but non-executable way to
express pure Boolean-ness.  See also @(see faig-purebool-check), which can be
executed; it uses a SAT solver to answer the question.</p>

@(def faig-purebool-p)"

  (defun-sk faig-purebool-p (x)
    (forall (env)
            (or (equal (faig-eval x env) (faig-t))
                (equal (faig-eval x env) (faig-f)))))

  (verify-guards faig-purebool-p))


(define faig-purebool-aig ((x "A single FAIG."))
  :parents (faig-purebool-p)
  :short "An AIG that captures exactly when the FAIG X is Boolean valued."
  :long "<p>This is useful mainly to implement @(see faig-purebool-check).</p>"
  :returns aig
  (b* ((x      (faig-fix x))
       (onset  (car x))
       (offset (cdr x)))
    (aig-or (aig-and onset (aig-not offset))
            (aig-and offset (aig-not onset))))
  ///
  (local (defthm l0
           (implies (not (aig-eval (faig-purebool-aig x) env))
                    (not (faig-purebool-p x)))
           :hints(("Goal"
                   :in-theory (e/d (faig-eval)
                                   (faig-purebool-p
                                    faig-purebool-p-necc))
                   :use ((:instance faig-purebool-p-necc
                                    (env env)))))))

  (local (defthm l1
           (implies (not (faig-purebool-p x))
                    (not (aig-eval (faig-purebool-aig x)
                                   (faig-purebool-p-witness x))))
           :hints(("Goal"
                   :in-theory (e/d (faig-eval)
                                   (faig-purebool-p))
                   :use ((:instance faig-purebool-p))))))

  (local (in-theory (disable faig-purebool-aig)))

  (local (defthm l2
           (implies (faig-purebool-p x)
                    (aig-eval (faig-purebool-aig x) env))))

  (defthmd faig-purebool-p-as-aig-eval
    (equal (faig-purebool-p x)
           (aig-eval (faig-purebool-aig x)
                     (faig-purebool-p-witness x))))

  (defthm faig-purebool-p-monotonicity
    (implies (not (aig-eval (faig-purebool-aig x) env))
             (not (aig-eval (faig-purebool-aig x)
                            (faig-purebool-p-witness x))))))



(define faig-purebool-check
  :parents (faig-purebool-p)
  :short "An executable version of @(see faig-purebool-p) using SAT."
  ((x "The FAIG to check.")
   &key
   ((config satlink::config-p) 'satlink::*default-config*))
  :returns (mv (fail     booleanp :rule-classes :type-prescription
                         "If true, calling the SAT solver failed and the other
                          answers are meaningless.")

               (purebool booleanp :rule-classes :type-prescription
                         "Does this FAIG always evaluate to purely Boolean?")

               (alist    "When this FAIG is not purely Boolean: an example
                          environment for @(see faig-eval) that drives it to
                          X or Z."))

  (b* ((aig               (faig-purebool-aig x))
       ((mv status alist) (aig-sat (aig-not aig) :config config))
       ((when (eq status :sat))
        (mv nil nil alist))
       ((when (eq status :unsat))
        (mv nil t nil)))
    (mv t nil nil))

  ///
  (local (defthm l0
           (b* (((mv fail purebool ?alist)
                 (faig-purebool-check x :config config)))
             (implies (and (not fail)
                           (not purebool))
                      (not (faig-purebool-p x))))
           :hints(("Goal"
                   :in-theory (e/d (faig-purebool-p-as-aig-eval)
                                   (aig-sat-when-sat))
                   :use ((:instance aig-sat-when-sat
                          (aig (aig-not (faig-purebool-aig x)))
                          (gatesimp (aignet::default-gatesimp))
                          (transform-config nil)))))))

  (local (defthm l1
           (b* (((mv fail purebool ?alist)
                 (faig-purebool-check x :config config)))
             (implies (and (not fail)
                           purebool)
                      (faig-purebool-p x)))
           :hints(("Goal"
                   :in-theory (e/d (faig-purebool-p-as-aig-eval)
                                   (aig-sat-when-unsat))
                   :use ((:instance aig-sat-when-unsat
                          (aig (aig-not (faig-purebool-aig x)))
                          (gatesimp (aignet::default-gatesimp))
                          (env (faig-purebool-p-witness x))
                          (transform-config nil)))))))

  (defthm faig-purebool-check-correct
    (b* (((mv fail purebool ?alist)
          (faig-purebool-check x :config config)))
      (implies (not fail)
               (equal purebool
                      (faig-purebool-p x))))
    :hints(("Goal"
            :use ((:instance l0)
                  (:instance l1)))))

  (local (defthm l2
           (b* (((mv fail purebool alist)
                 (faig-purebool-check x :config config)))
             (implies (and (not fail)
                           (not purebool))
                      (and (not (equal (faig-eval x alist) (faig-f)))
                           (not (equal (faig-eval x alist) (faig-t))))))
           :hints(("Goal"
                   :in-theory (e/d (faig-purebool-p-as-aig-eval
                                    faig-purebool-aig
                                    faig-eval)
                                   (aig-sat-when-sat))
                   :use ((:instance aig-sat-when-sat
                          (aig (aig-not (faig-purebool-aig x)))
                          (gatesimp (aignet::default-gatesimp))
                          (transform-config nil)))))))

  (defthm faig-purebool-counterexample-correct
    (b* (((mv fail ?purebool alist)
          (faig-purebool-check x :config config)))
      (implies (and (not fail)
                    (not (faig-purebool-p x)))
               (and (not (equal (faig-eval x alist) (faig-f)))
                    (not (equal (faig-eval x alist) (faig-t))))))
    :hints(("Goal"
            :in-theory (disable faig-purebool-check-correct
                                faig-purebool-check)
            :use ((:instance l1))))))





(std::deflist faig-purebool-list-p (x)
  (faig-purebool-p x)
  :guard t
  :parents (faig-purebool-p)
  :short "Do a list of FAIGs always evaluate to purely Boolean values, i.e.,
are they never X or Z?"

  :long "<p>This is a logically nice, but non-executable way to express pure
Boolean-ness.  See also @(see faig-purebool-list-check), which can be executed;
it uses a SAT solver to answer the question.</p>")


(define faig-purebool-list-witness (x)
  (cond ((atom x)
         nil)
        ((faig-purebool-p (car x))
         (faig-purebool-list-witness (cdr x)))
        (t
         (faig-purebool-p-witness (car x))))
  ///
  (defthm faig-purebool-list-witness-when-atom
    (implies (atom x)
             (equal (faig-purebool-list-witness x)
                    nil)))

  (defthm faig-purebool-list-witness-of-cons
    (equal (faig-purebool-list-witness (cons a x))
           (if (faig-purebool-p a)
               (faig-purebool-list-witness x)
             (faig-purebool-p-witness a)))))


(define faig-purebool-list-aig ((x "An FAIG List"))
  :returns (aig)
  :parents (faig-purebool-list-p)
  :short "An AIG that captures exactly when a list of FAIGs always evaluate to
purely Boolean values."
  :long "<p>This is useful mainly to implement @(see
faig-purebool-list-check).</p>"
  (if (atom x)
      t
    (aig-and (faig-purebool-aig (car x))
             (faig-purebool-list-aig (cdr x))))
  ///

  (local (defthm l0
           (implies (not (aig-eval (faig-purebool-list-aig x) env))
                    (not (faig-purebool-list-p x)))
           :hints(("Goal"
                   :in-theory (enable faig-purebool-p-as-aig-eval)))))

  (local (defthm l1
           (implies (not (faig-purebool-list-p x))
                    (not (aig-eval (faig-purebool-list-aig x)
                                   (faig-purebool-list-witness x))))
           :hints(("Goal"
                   :induct (len x)
                   :in-theory (e/d (faig-purebool-list-witness
                                    faig-purebool-p-as-aig-eval))))))

  (local (in-theory (disable faig-purebool-list-aig)))

  (local (defthm l2
           (implies (faig-purebool-list-p x)
                    (aig-eval (faig-purebool-list-aig x) env))))

  (defthmd faig-purebool-list-p-as-aig-eval
    (equal (faig-purebool-list-p x)
           (aig-eval (faig-purebool-list-aig x)
                     (faig-purebool-list-witness x)))
    :hints(("Goal" :cases ((faig-purebool-list-p x)))))

  (defthm faig-purebool-list-p-monotonicity
    (implies (not (aig-eval (faig-purebool-list-aig x) env))
             (not (aig-eval (faig-purebool-list-aig x)
                            (faig-purebool-list-witness x))))))





(define faig-purebool-list-check
  :parents (faig-purebool-list-p)
  :short "An executable version of @(see faig-purebool-list-p) using SAT."
  ((x "The FAIG List to check.")
   &key
   ((config satlink::config-p) 'satlink::*default-config*))
  :returns (mv (fail     booleanp :rule-classes :type-prescription
                         "If true, calling the SAT solver failed and the other
                          answers are meaningless.")

               (purebool-list booleanp :rule-classes :type-prescription
                              "Do these FAIGs always evaluate to purely Boolean?")

               (alist    "When these FAIGs are not purely Boolean: an example
                          environment for @(see faig-eval-list) that drives
                          some FAIG to X or Z."))

  (b* ((aig               (faig-purebool-list-aig x))
       ((mv status alist) (aig-sat (aig-not aig) :config config))
       ((when (eq status :sat))
        (mv nil nil alist))
       ((when (eq status :unsat))
        (mv nil t nil)))
    (mv t nil nil))

  ///
  (local (defthm l0
           (b* (((mv fail purebool-list ?alist)
                 (faig-purebool-list-check x :config config)))
             (implies (and (not fail)
                           (not purebool-list))
                      (not (faig-purebool-list-p x))))
           :hints(("Goal"
                   :in-theory (e/d (faig-purebool-list-p-as-aig-eval)
                                   (aig-sat-when-sat))
                   :use ((:instance aig-sat-when-sat
                          (gatesimp (aignet::default-gatesimp))
                          (aig (aig-not (faig-purebool-list-aig x)))
                          (transform-config nil)))))))

  (local (defthm l1
           (b* (((mv fail purebool-list ?alist)
                 (faig-purebool-list-check x :config config)))
             (implies (and (not fail)
                           purebool-list)
                      (faig-purebool-list-p x)))
           :hints(("Goal"
                   :in-theory (e/d (faig-purebool-list-p-as-aig-eval)
                                   (aig-sat-when-unsat))
                   :use ((:instance aig-sat-when-unsat
                          (gatesimp (aignet::default-gatesimp))
                          (aig (aig-not (faig-purebool-list-aig x)))
                          (env (faig-purebool-list-witness x))
                          (transform-config nil)))))))

  (defthm faig-purebool-list-check-correct
    (b* (((mv fail purebool-list ?alist)
          (faig-purebool-list-check x :config config)))
      (implies (not fail)
               (equal purebool-list
                      (faig-purebool-list-p x))))
    :hints(("Goal"
            :use ((:instance l0)
                  (:instance l1)))))

  ;; BOZO could eventually prove that the alist returned does indeed drive at
  ;; least some FAIG to X or Z.

  )

