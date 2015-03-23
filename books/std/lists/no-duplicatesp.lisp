; no-duplicatesp.lisp
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "duplicity")

(defthm no-duplicatesp-equal-when-atom
  (implies (atom x)
           (equal (no-duplicatesp-equal x)
                  t)))

(defthm no-duplicatesp-equal-of-cons
  (equal (no-duplicatesp-equal (cons a x))
         (and (not (member-equal a (double-rewrite x)))
              (no-duplicatesp-equal x))))

;; Not needed, equiv.lisp gives us a congruence rule for list-equiv
;; (defthm no-duplicatesp-equal-of-list-fix
;;   (equal (no-duplicatesp-equal (list-fix x))
;;          (no-duplicatesp-equal x)))


(defsection duplicity-badguy1
  :parents (duplicity-badguy)
  :short "@(call duplicity-badguy1) finds the first element of @('dom') whose
duplicity in @('x') exceeds 1, if such a member exists."

  (defund duplicity-badguy1 (dom x)
    (declare (xargs :guard t))
    (if (consp dom)
        (if (> (duplicity (car dom) x) 1)
            (list (car dom))
          (duplicity-badguy1 (cdr dom) x))
      nil))

  (defthm duplicity-badguy1-exists-in-list
    (implies (duplicity-badguy1 dom x)
             (member-equal (car (duplicity-badguy1 dom x)) x))
    :hints(("Goal" :in-theory (enable duplicity-badguy1))))

  (defthm duplicity-badguy1-exists-in-dom
    (implies (duplicity-badguy1 dom x)
             (member-equal (car (duplicity-badguy1 dom x)) dom))
    :hints(("Goal" :in-theory (enable duplicity-badguy1))))

  (defthm duplicity-badguy1-has-high-duplicity
    (implies (duplicity-badguy1 dom x)
             (< 1 (duplicity (car (duplicity-badguy1 dom x)) x)))
    :hints(("Goal" :in-theory (enable duplicity-badguy1))))

  (defthm duplicity-badguy1-is-complete-for-domain
    (implies (and (member-equal a dom)
                  (< 1 (duplicity a x)))
             (duplicity-badguy1 dom x))
    :hints(("Goal" :in-theory (enable duplicity-badguy1))))

  (defthm duplicity-badguy1-need-only-consider-the-list
    (implies (duplicity-badguy1 dom x)
             (duplicity-badguy1 x x))
    :hints(("Goal"
            :in-theory (disable duplicity-badguy1-exists-in-dom
                                duplicity-badguy1-exists-in-list)
            :use ((:instance duplicity-badguy1-exists-in-dom)
                  (:instance duplicity-badguy1-exists-in-list)))))

  (encapsulate
    ()
    (local (defthm lemma1
             (implies (duplicity-badguy1 dom x)
                      (duplicity-badguy1 dom (cons a x)))
             :hints(("Goal" :in-theory (enable duplicity-badguy1)))))

    (local (defthm lemma2
             (implies (and (member-equal a x)
                           (member-equal a dom))
                      (duplicity-badguy1 dom (cons a x)))
             :hints(("Goal" :in-theory (enable duplicity-badguy1)))))

    (defthm no-duplicatesp-equal-when-duplicity-badguy1
      (implies (and (not (duplicity-badguy1 dom x))
                    (subsetp-equal x dom))
               (no-duplicatesp-equal x))
      :hints(("Goal" :in-theory (enable duplicity-badguy1))))))



(defsection duplicity-badguy
  :parents (duplicity no-duplicatesp-equal-same-by-duplicity)
  :short "@(call duplicity-badguy) finds an element that occurs multiple times
in the list @('x'), if one exists."

  :long "<p>This function is central to our proof of @(see
no-duplicatesp-equal-same-by-duplicity), a pick-a-point style strategy for
proving that @(see no-duplicatesp) holds of a list by reasoning about duplicity
of an arbitrary element.</p>"

  (defund duplicity-badguy (x)
    (declare (xargs :guard t))
    (duplicity-badguy1 x x))

  (defthm duplicity-badguy-exists
    (implies (duplicity-badguy x)
             (member-equal (car (duplicity-badguy x)) x))
    :hints(("Goal" :in-theory (enable duplicity-badguy))))

  (defthm duplicity-badguy-has-high-duplicity
    (implies (duplicity-badguy x)
             (< 1 (duplicity (car (duplicity-badguy x)) x)))
    :hints(("Goal" :in-theory (e/d (duplicity-badguy)
                                   (duplicity-when-member-equal)))))

  (defthm duplicity-badguy-is-complete
    (implies (< 1 (duplicity a x))
             (duplicity-badguy x))
    :hints(("Goal"
            :in-theory (enable duplicity-badguy)
            :use ((:instance duplicity-badguy1-is-complete-for-domain
                             (dom x))))))

  (local (defthm lemma
           (implies (subsetp-equal a (cdr x))
                    (subsetp-equal a x))))

  (local (defthm lemma2
           (subsetp-equal x x)
           :hints(("Goal" :induct (len x)))))

  (local (defthm lemma3
           (implies (not (duplicity-badguy x))
                    (no-duplicatesp-equal x))
           :hints(("Goal" :in-theory (enable duplicity-badguy)))))

  (local (defthm lemma5
           (implies (duplicity-badguy x)
                    (not (no-duplicatesp-equal x)))
           :hints(("Goal"
                   :in-theory (disable no-duplicatesp-equal)
                   :use ((:instance no-duplicatesp-equal-when-high-duplicity
                                    (a (car (duplicity-badguy x)))))))))

  (defthm duplicity-badguy-under-iff
    (iff (duplicity-badguy x)
         (not (no-duplicatesp-equal x)))))



(defsection no-duplicatesp-equal-same-by-duplicity
  :parents (no-duplicatesp-equal duplicity)
  :short "Proof strategy: show that a list satisfies @(see no-duplicatesp-equal)
because it has no element whose @(see duplicity) is over 1."

  :long "<p>This is often a good way to prove @(see no-duplicatesp).  This is a
basic pick-a-point style theorem that you can (manually) <see topic='@(url
functional-instantiation-example)'>functionally instantiate</see>.</p>"

  (encapsulate
    (((duplicity-hyp) => *)
     ((duplicity-lhs) => *)
     ((duplicity-rhs) => *))

    (local (defun duplicity-hyp () nil))
    (local (defun duplicity-lhs () nil))
    (local (defun duplicity-rhs () nil))

    (defthm duplicity-constraint
      (implies (duplicity-hyp)
               (equal (duplicity a (duplicity-lhs))
                      (duplicity a (duplicity-rhs))))))

  (local (defthm lemma1
           (implies (and (duplicity-hyp)
                         (no-duplicatesp-equal (duplicity-lhs)))
                    (no-duplicatesp-equal (duplicity-rhs)))
           :hints(("goal"
                   :in-theory (disable duplicity-constraint
                                       duplicity-badguy-has-high-duplicity)
                   :use ((:instance duplicity-badguy-has-high-duplicity
                                    (x (duplicity-rhs)))
                         (:instance duplicity-constraint
                                    (a (car (duplicity-badguy (duplicity-rhs))))))))))

  (local (defthm lemma2
           (implies (and (duplicity-hyp)
                         (no-duplicatesp-equal (duplicity-rhs)))
                    (no-duplicatesp-equal (duplicity-lhs)))
           :hints(("goal"
                   :in-theory (disable duplicity-constraint
                                       duplicity-badguy-has-high-duplicity)
                   :use ((:instance duplicity-badguy-has-high-duplicity
                                    (x (duplicity-lhs)))
                         (:instance duplicity-constraint
                                    (a (car (duplicity-badguy (duplicity-lhs))))))))))

  (defthm no-duplicatesp-equal-same-by-duplicity
    (implies (duplicity-hyp)
             (equal (no-duplicatesp-equal (duplicity-lhs))
                    (no-duplicatesp-equal (duplicity-rhs))))
    :hints(("goal"
            :use ((:instance lemma1)
                  (:instance lemma2))))))



(defthm no-duplicatesp-equal-of-rev
  (equal (no-duplicatesp-equal (rev x))
         (no-duplicatesp-equal x))
  :hints(("Goal"
          :use ((:functional-instance
                 no-duplicatesp-equal-same-by-duplicity
                 (duplicity-hyp (lambda () t))
                 (duplicity-lhs (lambda () (rev x)))
                 (duplicity-rhs (lambda () x)))))))

(defthm no-duplicatesp-equal-of-append-of-rev-1
  (equal (no-duplicatesp-equal (append (rev x) y))
         (no-duplicatesp-equal (append x y)))
  :hints(("Goal"
          :use ((:functional-instance
                 no-duplicatesp-equal-same-by-duplicity
                 (duplicity-hyp (lambda () t))
                 (duplicity-lhs (lambda () (append (rev x) y)))
                 (duplicity-rhs (lambda () (append x y))))))))

(defthm no-duplicatesp-equal-of-append-of-rev-2
  (equal (no-duplicatesp-equal (append x (rev y)))
         (no-duplicatesp-equal (append x y)))
  :hints(("Goal"
          :use ((:functional-instance
                 no-duplicatesp-equal-same-by-duplicity
                 (duplicity-hyp (lambda () t))
                 (duplicity-lhs (lambda () (append x (rev y))))
                 (duplicity-rhs (lambda () (append x y))))))))

(defthm no-duplicatesp-equal-of-append-of-append
  (equal (no-duplicatesp-equal (append x y))
         (no-duplicatesp-equal (append y x)))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :use ((:functional-instance
                         no-duplicatesp-equal-same-by-duplicity
                         (duplicity-hyp (lambda () t))
                         (duplicity-lhs (lambda () (append x y)))
                         (duplicity-rhs (lambda () (append y x))))))))

(defthm no-duplicatesp-equal-of-flatten-of-rev
  (equal (no-duplicatesp-equal (flatten (rev x)))
         (no-duplicatesp-equal (flatten x)))
  :hints(("Goal"
          :use ((:functional-instance
                 no-duplicatesp-equal-same-by-duplicity
                 (duplicity-hyp (lambda () t))
                 (duplicity-lhs (lambda () (flatten (rev x))))
                 (duplicity-rhs (lambda () (flatten x))))))))
