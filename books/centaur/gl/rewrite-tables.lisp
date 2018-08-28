; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "GL")

(include-book "std/util/define" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "centaur/misc/rewrite-rule" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)

;; This book defines two main functions, each supporting one type of rewrite
;; rule usage in GL.  Each returns a list of rules applicable to a given
;; function symbol. One lists branch merge rules where the function is the
;; leading symbol of the then branch of an IF on the LHS, given a list of all
;; runes to be allowed as branch merge rules; the other lists rules where the
;; function is the leading symbol, given a table mapping function names to
;; allowed rewrite rule runes.  Both are memoized (though in different ways)
;; and should give good performance: the branch-merge function computes a full
;; table of branch merge rules initially and memoizes that table, then does
;; constant-time lookups in it; the standard rewriting function computes a list
;; for each function symbol one at a time, memoizing the results per-function.

; note: similar named function exists in system/pseudo-good-worldp, but since
; this is in the GL package there's no name clash.
(define pseudo-rewrite-rule-p (x)
  (and (acl2::weak-rewrite-rule-p x)
       (b* (((acl2::rewrite-rule x)))
         (and (pseudo-term-listp x.hyps)
              (pseudo-termp x.lhs)
              (pseudo-termp x.rhs)
              (symbolp x.equiv)
              (not (eq x.equiv 'quote))
              (not (eq x.subclass 'acl2::meta)))))
  ///
  (defthm pseudo-rewrite-rule-p-implies
    (implies (pseudo-rewrite-rule-p x)
             (and (acl2::weak-rewrite-rule-p x)
                  (b* (((acl2::rewrite-rule x)))
                    (and (pseudo-term-listp x.hyps)
                         (pseudo-termp x.lhs)
                         (pseudo-termp x.rhs)
                         (symbolp x.equiv)
                         (not (eq x.equiv 'quote))
                         (not (eq x.subclass 'acl2::meta))))))))

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

(define pseudo-rewrite-table-p (x)
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (symbolp (caar x))
         (pseudo-rewrite-rule-listp (cdar x))
         (pseudo-rewrite-table-p (cdr x))))
  ///
  (defthm pseudo-rewrite-table-p-of-cons
    (equal (pseudo-rewrite-table-p (cons a b))
           (and (consp a)
                (symbolp (car a))
                (pseudo-rewrite-rule-listp (cdr a))
                (pseudo-rewrite-table-p b))))

  (defthm lookup-when-pseudo-rewrite-table-p
    (implies (pseudo-rewrite-table-p x)
             (pseudo-rewrite-rule-listp (cdr (hons-assoc-equal k x))))))


(define mextract-good-rewrite-rule-tablep (x)
  (if (atom x)
      t
    (and (or (atom (car x))
             (mextract-good-rewrite-rulesp (cdar x)))
         (mextract-good-rewrite-rule-tablep (cdr x))))
  ///
  (defthm mextract-good-rewrite-rule-tablep-of-cons
    (equal (mextract-good-rewrite-rule-tablep (cons a b))
           (and (or (atom a)
                    (mextract-good-rewrite-rulesp (cdr a)))
                (mextract-good-rewrite-rule-tablep b))))

  (defthm lookup-when-mextract-good-rewrite-table-p
    (implies (mextract-good-rewrite-rule-tablep x)
             (mextract-good-rewrite-rulesp (cdr (hons-assoc-equal k x))))))




(define filter-rewrite-rules (lemmas (runes true-listp))
  :returns (rules pseudo-rewrite-rule-listp)
  (b* (((when (atom lemmas)) nil)
       ((unless (pseudo-rewrite-rule-p (car lemmas)))
        (filter-rewrite-rules (cdr lemmas) runes))
       ((acl2::rewrite-rule x) (car lemmas))
       ((unless (member-equal x.rune runes))
        (filter-rewrite-rules (cdr lemmas) runes)))
    (cons x (filter-rewrite-rules (cdr lemmas) runes)))
  ///
  (std::defret mextract-good-rewrite-rulesp-of-filter-rewrite-rules
    (implies (mextract-good-rewrite-rulesp lemmas)
             (mextract-good-rewrite-rulesp rules))))



;; Main function for regular rewriting
(define rune-table-to-rewrite-table (x (wrld plist-worldp))
  :returns (table pseudo-rewrite-table-p)
  (b* (((when (atom x)) nil)
       ((when (or (atom (car x))
                  (not (symbolp (caar x)))))
        (rune-table-to-rewrite-table (cdr x) wrld))
       (fn (caar x))
       (runes (list-fix (cdar x)))
       (lemmas (fgetprop fn 'acl2::lemmas nil wrld))
       (rules (filter-rewrite-rules lemmas runes)))
    (if rules
        (hons-acons fn rules (rune-table-to-rewrite-table (cdr x) wrld))
      (rune-table-to-rewrite-table (cdr x) wrld)))
  ///
  (std::defret mextract-good-rewrite-rule-tablep-of-rune-table-to-rewrite-table
    (implies (and (acl2::mextract-ev-global-facts)
                  (equal wrld (w state)))
             (mextract-good-rewrite-rule-tablep table))
    :hints(("Goal" :in-theory (disable w)))))

(local (defthm pseudo-rewrite-table-p-of-fast-alist-fork
         (implies (and (pseudo-rewrite-table-p x)
                       (pseudo-rewrite-table-p y))
                  (pseudo-rewrite-table-p (fast-alist-fork x y)))))

(local (defthm mextract-good-rewrite-rule-tablep-of-fast-alist-fork
         (implies (and (mextract-good-rewrite-rule-tablep x)
                       (mextract-good-rewrite-rule-tablep y))
                  (mextract-good-rewrite-rule-tablep (fast-alist-fork x y)))))

(define sort-branch-merge-rules-by-function ((rules pseudo-rewrite-rule-listp)
                                             (acc pseudo-rewrite-table-p))
  :returns (table pseudo-rewrite-table-p :hyp :guard)
  (b* (((when (atom rules)) (fast-alist-clean acc))
       ((acl2::rewrite-rule x) (car rules)))
    (case-match x.lhs
      (('if test (fn . &) else)
       (if (and (symbolp test)
                (symbolp else)
                (symbolp fn)
                (not (eq fn 'quote)))
           (sort-branch-merge-rules-by-function
            (cdr rules)
            (hons-acons fn (cons x (cdr (hons-get fn acc))) acc))
         (sort-branch-merge-rules-by-function (cdr rules) acc)))
      (& (sort-branch-merge-rules-by-function (cdr rules) acc))))

  :prepwork ((local (defthm cdr-last-when-pseudo-rewrite-table-p
                      (implies (pseudo-rewrite-table-p x)
                               (equal (cdr (last x)) nil))
                      :hints(("Goal" :in-theory (enable pseudo-rewrite-table-p)))))

             (local (defthm atom-of-cdr-last
                      (atom (cdr (last x)))
                      :rule-classes :type-prescription))

             (local (defthm mextract-good-rewrite-rule-tablep-when-atom
                      (implies (atom x)
                               (mextract-good-rewrite-rule-tablep x))
                      :hints(("Goal" :in-theory (enable mextract-good-rewrite-rule-tablep))))))

  ///
  (std::defret mextract-good-rewrite-rule-tablep-of-sort-branch-merge-rules-by-function
    (implies (and (mextract-good-rewrite-rulesp rules)
                  (mextract-good-rewrite-rule-tablep acc))
             (mextract-good-rewrite-rule-tablep table))))
       
    
(define branch-merge-rewrite-table (runes (wrld plist-worldp))
  :returns (table pseudo-rewrite-table-p)
  (b* ((lemmas (fgetprop 'if 'acl2::lemmas nil wrld))
       (rules (filter-rewrite-rules lemmas (list-fix runes))))
    (sort-branch-merge-rules-by-function rules nil))
  ///
  (std::defret mextract-good-rewrite-rule-tablep-of-branch-merge-rewrite-table
    (implies (and (acl2::mextract-ev-global-facts)
                  (equal wrld (w state)))
             (mextract-good-rewrite-rule-tablep table)))

  (memoize 'branch-merge-rewrite-table))


(define fn-branch-merge-rules (fn runes (wrld plist-worldp))
  :returns (rules pseudo-rewrite-rule-listp)
  (cdr (hons-get fn (branch-merge-rewrite-table runes wrld)))
  ///
  (std::defret mextract-good-rewrite-rulesp-of-fn-branch-merge-rules
    (implies (and (acl2::mextract-ev-global-facts)
                  (equal wrld (w state)))
             (mextract-good-rewrite-rulesp rules))))

(define fn-rewrite-rules ((fn symbolp) runetable (wrld plist-worldp))
  :returns (rules pseudo-rewrite-rule-listp)
  (b* ((runes (cdr (hons-assoc-equal fn runetable)))
       (lemmas (fgetprop fn 'acl2::lemmas nil wrld)))
    (filter-rewrite-rules lemmas (list-fix runes)))
  ///
  (std::defret mextract-good-rewrite-rulesp-of-fn-rewrite-rules
    (implies (and (acl2::mextract-ev-global-facts)
                  (equal wrld (w state)))
             (mextract-good-rewrite-rulesp rules)))

  (memoize 'fn-rewrite-rules))
