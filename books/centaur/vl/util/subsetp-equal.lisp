; VL Verilog Toolkit
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

(in-package "VL")

; This book should be only locally included!  Define functions in util/defs
; redundantly if you need to.  Eventually this stuff should be put into a
; library.

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/misc/equal-sets" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "std/lists/list-fix" :dir :system)
(include-book "std/lists/take" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(include-book "std/lists/no-duplicatesp" :dir :system)

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))

(in-theory (disable member subsetp))

;; These are disabled in equal-sets.lisp because they can sometimes be
;; expensive.  But I prefer to leave them enabled by default, and just disable
;; them when they become expensive.
(in-theory (enable acl2::subsetp-member acl2::subsetp-trans2))

;; BOZO maybe this should be forward-chaining?
(defrule member-equal-when-member-equal-of-cdr-under-iff
  (implies (member-equal a (cdr x))
           (member-equal a x))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))


;; BOZO some of this, especially the congruences, should be moved to equal-sets

(defrule member-equal-of-list-fix
  ;; This is slightly different than LIST-EQUIV-IMPLIES-LIST-EQUIV-MEMBER-2,
  ;; since it can fire in an equal context.
  (equal (member-equal a (list-fix x))
         (list-fix (member-equal a x)))
  :induct (len x))


(defsection set-equiv-by-duplicity

  (local (defruled l0
           (iff (member-equal a x)
                (< 0 (duplicity a x)))
           :enable duplicity))

  (local (defrule member-equal-same-by-duplicity
           (implies (acl2::duplicity-hyp)
                    (iff (member-equal a (acl2::duplicity-lhs))
                         (member-equal a (acl2::duplicity-rhs))))
           :enable l0
           :use ((:instance acl2::duplicity-constraint
                            (acl2::a a)))))

  (defruled set-equiv-by-duplicity
    (implies (acl2::duplicity-hyp)
             (set-equiv (acl2::duplicity-lhs)
                        (acl2::duplicity-rhs)))
    :hints((set-reasoning))))

(defcong set-equiv set-equiv (<<-sort x) 1
  :event-name <<-sort-preserves-set-equiv
  :hints(("Goal"
          :use ((:functional-instance
                 set-equiv-by-duplicity
                 (acl2::duplicity-hyp (lambda () t))
                 (acl2::duplicity-rhs (lambda () (<<-sort x)))
                 (acl2::duplicity-lhs (lambda () x)))
                (:functional-instance
                 set-equiv-by-duplicity
                 (acl2::duplicity-hyp (lambda () t))
                 (acl2::duplicity-rhs (lambda () (<<-sort x-equiv)))
                 (acl2::duplicity-lhs (lambda () x-equiv)))))))

(defrule <<-sort-under-set-equiv
  (set-equiv (<<-sort x) x)
  :hints(("Goal"
          :use ((:functional-instance set-equiv-by-duplicity
                 (acl2::duplicity-hyp (lambda () t))
                 (acl2::duplicity-rhs (lambda () (<<-sort x)))
                 (acl2::duplicity-lhs (lambda () x)))))))



(encapsulate
  ()
  (local (defrule l0
           (implies (and (string-listp y)
                         (member-equal a y))
                    (stringp a))))

  (defrule string-listp-when-subsetp-equal-of-string-listp
    (implies (and (string-listp y)
                  (subsetp-equal x y))
             (equal (string-listp x)
                    (true-listp x)))
    :induct (len x)
    :rule-classes ((:rewrite)
                   (:rewrite :corollary
                             (implies (and (subsetp-equal x y)
                                           (string-listp y))
                                      (equal (string-listp x)
                                             (true-listp x)))))))

(encapsulate
  ()
  (local (defrule l0
           (implies (and (symbol-listp y)
                         (member-equal a y))
                    (symbolp a))))

  (defrule symbol-listp-when-subsetp-equal-of-symbol-listp
    (implies (and (symbol-listp y)
                  (subsetp-equal x y))
             (equal (symbol-listp x)
                    (true-listp x)))
    :induct (len x)
    :rule-classes ((:rewrite)
                   (:rewrite :corollary
                             (implies (and (subsetp-equal x y)
                                           (symbol-listp y))
                                      (equal (symbol-listp x)
                                             (true-listp x)))))))


(defrule subsetp-equal-of-duplicated-members
  (subsetp-equal (duplicated-members x) x)
  :hints((set-reasoning)))

(defrule subsetp-equal-of-hons-duplicated-members
  (subsetp-equal (hons-duplicated-members x) x)
  :hints((set-reasoning)))

(defrule string-listp-of-duplicated-members
  (implies (string-listp x)
           (string-listp (duplicated-members x))))

(defrule symbol-listp-of-duplicated-members
  (implies (symbol-listp x)
           (symbol-listp (duplicated-members x))))

(defrule string-listp-of-hons-duplicated-members
  (implies (string-listp x)
           (string-listp (hons-duplicated-members x))))

(defrule symbol-listp-of-hons-duplicated-members
  (implies (symbol-listp x)
           (symbol-listp (hons-duplicated-members x))))


