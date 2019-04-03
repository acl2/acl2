; Centaur Meta-reasoning Library
; Copyright (C) 2019 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "CMR")

(include-book "centaur/misc/rewrite-rule" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "std/util/define" :dir :system)


(define pseudo-rewrite-rule-p (x)
  (and (acl2::weak-rewrite-rule-p x)
       (b* (((acl2::rewrite-rule x)))
         (and (pseudo-term-listp x.hyps)
              (pseudo-termp x.lhs)
              (pseudo-termp x.rhs)
              (symbolp x.equiv)
              (not (eq x.equiv 'quote))
              (not (eq x.subclass 'acl2::meta))
              (natp x.nume))))
  ///
  (defthm pseudo-rewrite-rule-p-implies
    (implies (pseudo-rewrite-rule-p x)
             (and (acl2::weak-rewrite-rule-p x)
                  (b* (((acl2::rewrite-rule x)))
                    (and (pseudo-term-listp x.hyps)
                         (pseudo-termp x.lhs)
                         (pseudo-termp x.rhs)
                         (symbolp x.equiv)
                         (not (equal x.equiv 'quote))
                         (not (equal x.subclass 'acl2::meta))
                         (natp x.nume))))))

  (defthm pseudo-rewrite-rule-p-implies-natp-nume
    (implies (pseudo-rewrite-rule-p x)
             (natp (acl2::rewrite-rule->nume x)))
    :rule-classes :type-prescription))


(define mextract-good-rewrite-rulesp (rules)
  (if (atom rules)
      t
    (and (acl2::mextract-ev-theoremp (acl2::rewrite-rule-term (car rules)))
         (mextract-good-rewrite-rulesp (cdr rules))))
  ///
  (defthm mextract-good-rewrite-rulesp-of-cons
    (equal (mextract-good-rewrite-rulesp (cons a b))
           (and (acl2::mextract-ev-theoremp (acl2::rewrite-rule-term a))
                (mextract-good-rewrite-rulesp b))))

  (defthm mextract-good-rewrite-rulesp-of-cdr
    (implies (mextract-good-rewrite-rulesp x)
             (mextract-good-rewrite-rulesp (cdr x))))

  (defthm mextract-ev-of-car-when-good-rewrite-rulesp
    (implies (and (mextract-good-rewrite-rulesp x) (consp x))
             (acl2::mextract-ev (acl2::rewrite-rule-term (car x)) a))
    :hints(("Goal" :in-theory (disable acl2::rewrite-rule-term)
            :expand ((mextract-good-rewrite-rulesp x))
            :use ((:instance acl2::mextract-ev-falsify
                   (x (acl2::rewrite-rule-term (car x))) (a a))))))

  (local (defun mextract-good-rewrite-rulesp-badguy (rules)
           (if (atom rules)
               nil
             (if (acl2::mextract-ev-theoremp (acl2::rewrite-rule-term (car rules)))
                 (mextract-good-rewrite-rulesp-badguy (cdr rules))
               (car rules)))))

  (local (defthmd mextract-good-rewrite-rulesp-by-badguy
           (iff (mextract-good-rewrite-rulesp rules)
                (b* ((badguy (mextract-good-rewrite-rulesp-badguy rules)))
                  (or (not (member badguy rules))
                      (acl2::mextract-ev-theoremp (acl2::rewrite-rule-term badguy)))))))


  (defthm mextract-good-rewrite-rulesp-of-lemmas
    (implies (and (acl2::mextract-ev-global-facts)
                  (equal wrld (w state)))
             (mextract-good-rewrite-rulesp (fgetprop fn 'acl2::lemmas nil wrld)))
    :hints(("Goal" :in-theory (e/d (mextract-good-rewrite-rulesp-by-badguy)
                                   (mextract-good-rewrite-rulesp
                                    mextract-good-rewrite-rulesp-badguy
                                    acl2::rewrite-rule-term
                                    w))
            :do-not-induct t))))

(define pseudo-rewrite-rule-listp (x)
  (if (atom x)
      (eq x nil)
    (and (pseudo-rewrite-rule-p (car x))
         (pseudo-rewrite-rule-listp (cdr x))))
  ///
  (defthm pseudo-rewrite-rule-listp-of-cons
    (equal (pseudo-rewrite-rule-listp (cons a b))
           (and (pseudo-rewrite-rule-p a)
                (pseudo-rewrite-rule-listp b))))

  (defthm pseudo-rewrite-rule-listp-of-cdr
    (implies (pseudo-rewrite-rule-listp x)
             (pseudo-rewrite-rule-listp (cdr x))))

  (defthm pseudo-rewrite-rule-p-of-car
    (implies (and (pseudo-rewrite-rule-listp x)
                  (consp x))
             (pseudo-rewrite-rule-p (car x)))))


(local (in-theory (disable acl2::rewrite-rule-term)))                  

(defthmd rewrite-rule-term-alt-def
  (equal (acl2::rewrite-rule-term x)
         (if (eq (acl2::rewrite-rule->subclass x) 'acl2::meta)
             ''t
           `(implies ,(conjoin (acl2::rewrite-rule->hyps x))
                     (,(acl2::rewrite-rule->equiv x)
                      ,(acl2::rewrite-rule->lhs x)
                      ,(acl2::rewrite-rule->rhs x)))))
  :hints(("Goal" :in-theory (enable acl2::rewrite-rule-term
                                    acl2::rewrite-rule->subclass
                                    acl2::rewrite-rule->hyps
                                    acl2::rewrite-rule->equiv
                                    acl2::rewrite-rule->lhs
                                    acl2::rewrite-rule->rhs))))
