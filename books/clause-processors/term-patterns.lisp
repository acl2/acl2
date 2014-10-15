; Automation for recognizing categories of terms
; Copyright (C) 2010 Centaur Technology
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


(in-package "ACL2")

(include-book "meta/pseudo-termp-lemmas" :dir :system)

;; This book establishes a table for the purpose of storing patterns that allow
;; us to recognize terms of some sort, and it provides a pattern-matching
;; algorithm for recognizing those terms.  For example, if we want to recognize
;; terms that produce BDDs, the table entry for bdd-functions would contain
;; things like (q-ite . &), (q-not . &), etc.

;; The language of these term patterns is very simple.  Function symbols must
;; be matched literally.  Quotations must be matched identically, and Booleans
;; and non-symbol atoms must be matched with a quotation of that identical
;; atom.  Symbols may match anything, but are checked for consistency, with the
;; exception of the wildcard symbol &.  The matched assignments of the symbols
;; is returned in case of a match.

;; Therefore:
;; (foo 'a) only matches (foo 'a)
;; (foo a)  matches (foo (...)) and returns '((a . (...)))
;; (foo &) matches (foo X) where x may be anything
;; (foo . &) matches any list beginning with foo.

;; Accessors for term pattern lists.

(defmacro get-term-patterns (name)
  `(cdr (assoc ',name (table-alist 'term-patterns world))))

(defmacro set-term-patterns (name val)
  `(table term-patterns ',name ,val))

(defmacro add-term-pattern (name val)
  `(set-term-patterns ,name (cons ',val (get-term-patterns ,name))))

(defmacro add-term-patterns (name &rest vals)
  `(set-term-patterns ,name (append ',vals (get-term-patterns ,name))))

(defun fn-pat (fn)
  (declare (xargs :guard t))
  `(,fn . &))

(defun fn-pats (fns)
  (declare (xargs :guard t))
  (if (atom fns)
      nil
    (cons (fn-pat (car fns)) (fn-pats (cdr fns)))))

(defmacro add-fn-term-pattern (name fn)
  `(set-term-patterns ,name (cons ',(fn-pat fn) (get-term-patterns ,name))))

(defmacro add-fn-term-patterns (name &rest fns)
  `(set-term-patterns
    ,name (append ',(fn-pats fns) (get-term-patterns ,name))))

(mutual-recursion
 (defun term-patternp (x)
   (declare (xargs :guard t))
   (cond ((atom x) t)
         ((eq (car x) 'quote) t)
         (t (and (symbolp (car x))
                 (term-pattern-listp (cdr x))))))
 (defun term-pattern-listp (x)
   (if (atom x)
       (or (eq x nil) (eq x '&))
     (and (term-patternp (car x))
          (term-pattern-listp (cdr x))))))

;; Should be started with an accumulator of ((& . &)).  No special significance
;; to this, just that it's a non-empty alist that won't disrupt anything here.
(mutual-recursion
 (defun term-pattern-match (x pat acc)
   (declare (xargs :guard (and (term-patternp pat)
                               (alistp acc))
                   :verify-guards nil))
   (cond ((eq pat '&) acc)
         ((and (symbolp pat) (not (booleanp pat)))
          (let ((look (assoc pat acc)))
            (if look
                (and (equal x (cdr look))
                     acc)
              (cons (cons pat x) acc))))
         ((atom pat) (case-match x
                       (('quote !pat) acc)))
         ((eq (car pat) 'quote) (and (equal x pat) acc))
         (t (and (consp x)
                 (eq (car x) (car pat))
                 (term-pattern-match-list (cdr x) (cdr pat) acc)))))
 (defun term-pattern-match-list (x pat acc)
   (declare (xargs :guard (and (term-pattern-listp pat)
                               (alistp acc))))
   (if (atom pat)
       (cond ((eq pat '&) acc)
             (t (and (eq x nil) acc)))
     (and (consp x)
          (let ((acc (term-pattern-match (car x) (car pat) acc)))
            (and acc
                 (term-pattern-match-list (cdr x) (cdr pat) acc)))))))

(include-book "tools/flag" :dir :system)

(make-flag term-pattern-match-flag term-pattern-match)

(defthm-term-pattern-match-flag
  term-pattern-match-flag-alistp
  (term-pattern-match
   (implies (alistp acc)
            (alistp (term-pattern-match x pat acc)))
   :name term-pattern-match-alistp)
  (term-pattern-match-list
   (implies (alistp acc)
            (alistp (term-pattern-match-list x pat acc)))
   :name term-pattern-match-list-alistp)
  :hints (("goal" :induct (term-pattern-match-flag flag x pat acc))))

(verify-guards term-pattern-match)

(defthm-term-pattern-match-flag
  term-pattern-match-flag-pseudo-term-substp
  (term-pattern-match
   (implies (and (pseudo-termp x)
                 (pseudo-term-substp acc))
            (pseudo-term-substp (term-pattern-match x pat acc)))
   :name term-pattern-match-pseudo-term-substp)
  (term-pattern-match-list
   (implies (and (pseudo-term-listp x)
                 (pseudo-term-substp acc))
            (pseudo-term-substp (term-pattern-match-list x pat acc)))
   :name term-pattern-match-list-pseudo-term-substp)
  :hints (("goal" :induct (term-pattern-match-flag flag x pat acc))))



(defun match-term-pattern (x pats)
  (declare (xargs :guard (term-pattern-listp pats)))
  (if (atom pats)
      nil
    (or (term-pattern-match x (car pats) '((& . &)))
        (match-term-pattern x (cdr pats)))))

(defthm pseudo-term-substp-match-term-pattern
  (implies (pseudo-termp x)
           (pseudo-term-substp (match-term-pattern x pats))))

(defun term-matches (term name world)
  (match-term-pattern
   term
   (cdr (assoc name (table-alist 'term-patterns world)))))

(defthm pseudo-term-substp-term-matches
  (implies (pseudo-termp x)
           (pseudo-term-substp (term-matches x name world))))

(in-theory (disable match-term-pattern term-pattern-match term-matches))
