; Base definitions of generic list predicates/projections/etc.
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "std/lists/abstract" :dir :system)

(defxdoc std/alists/abstract
  :parents (std/alists)
  :short "Abstract theories for alist predicates"
  :long "<p>This book works similarly to @(see std/lists/abstract), defining a set of
theorems about a generic alist using functions:</p>
<ul>
<li>keytype-p</li>
<li>valtype-p</li>
<li>keyval-alist-p</li>
</ul>

<p>See @(see std/lists/abstract) for documentation of the general idea.</p>

<h3>List of requirement variables recognized by @(see std::deflist)</h3>
<p>Note: All of these are symbols in the ACL2 package.</p>
<ul>
<li>@('keytype-p-of-nil'), @('valtype-p-of-nil'), respectively, are true if NIL
is known to be a key/value</li>
<li>@('not-keytype-p-of-nil'), @('not-valtype-p-of-nil') are true if NIL is
known not to be a key/value.  @('***-of-nil') and @('not-***-of-nil') may not
both be true, but may both be false in cases where the status of NIL is unknown
or depends on extra input parameters.</li>
<li>@('key-negatedp'), @('val-negatedp') are true if we are creating an alist
that recognizes elements defined by @('NOT') of the predicate, which may affect
the correct formulation of rewrite rules</li>
<li>@('true-listp') is true if the alist recognizer is strict, i.e., implies true-listp</li>
<li>@('single-var') is true if the alist recognizer has no extra parameters</li>
<li>@('cheap') is true if the user gave an extra option requesting cheaper versions of some rules.</li>
</ul>

")

(local (set-default-parents std/alists/abstract))



(defsection keytype-p
  :short "Generic typed list keytype recognizer."
  ;; Keytypep functions for defining various types of list recognizers, with fixing functions.
  (encapsulate (((keytype-p *) => *)
                ((keytype-example) => *))

    (local (defun keytype-p (x) (natp x)))
    (local (defun keytype-example () 0)))

  (encapsulate
    (((non-keytype-p *) => *))
    (local (defun non-keytype-p (x)
             ;; Rewriting target for when keytype-p is (not (foo-p x))
             (not (keytype-p x))))
    (defthm non-keytype-p-def
      (iff (non-keytype-p x)
           (not (keytype-p x))))))

(defsection valtype-p
  :short "Generic typed list valtype recognizer."
  ;; Valtypep functions for defining various types of list recognizers, with fixing functions.
  (encapsulate (((valtype-p *) => *)
                ((valtype-example) => *))

    (local (defun valtype-p (x) (natp x)))
    (local (defun valtype-example () 0)))

  (encapsulate
    (((non-valtype-p *) => *))
    (local (defun non-valtype-p (x)
             ;; Rewriting target for when valtype-p is (not (foo-p x))
             (not (valtype-p x))))
    (defthm non-valtype-p-def
      (iff (non-valtype-p x)
           (not (valtype-p x))))))

(encapsulate
  (((keyval-alist-final-cdr-p *) => *))

  (local (defun keyval-alist-final-cdr-p (x)
           (not x)))

  (defthm keyval-alist-final-cdr-p-of-nil
    (keyval-alist-final-cdr-p nil))

  (defthm keyval-alist-final-cdr-p-type
    (or (equal (keyval-alist-final-cdr-p x) t)
        (equal (keyval-alist-final-cdr-p x) nil))
    :rule-classes :type-prescription)

  (defthm keyval-alist-final-cdr-p-rewrite
    (implies (syntaxp (and (not (equal x ''t))
                           (not (equal x ''nil))))
             (equal (keyval-alist-final-cdr-p x)
                    (or (equal x nil)
                        (keyval-alist-final-cdr-p t))))))






;; Listp-rules table (and projection-rule table, etc) format:
;; each entry is:
;; generic-rule-name . t
;;   to denote straightforward instantiation with the same rule classes, no restrictions
;; generic-rule-name alist
;;   where alist may bind keys:
;;     :requirement :name :body :rule-classes
;;     to denote that you instantiate generic-rule-name to prove the theorem, as
;;     long as requirement-list is satisfied.
;; The following macros only support the straightforward form.

(defsection def-alistp-rule
  :short "Define a theorem and save it in a table, denoting that it is a rule
about keyval-alistp."
  (defmacro def-alistp-rule (&rest args)
    `(def-generic-rule alistp-rules . ,args)))


(defsection keyval-alist-p
  :short "Generic typed list recognizer function."

  (defun keyval-alist-p (x)
    (if (atom x)
        (keyval-alist-final-cdr-p x)
      (and (consp (car x))
           (keytype-p (caar x))
           (valtype-p (cdar x))
           (keyval-alist-p (cdr x)))))

  (in-theory (disable (keyval-alist-p)))

  (def-alistp-rule keytype-p-of-caar-when-keyval-alist-p-when-keytype-p-nil
    (implies (and (keytype-p nil)
                  (keyval-alist-p x))
             (keytype-p (caar x)))
    :requirement (and keytype-simple keytype-p-of-nil)
    :name keytype-p-of-caar-when-keyval-alist-p
    :body (implies (keyval-alist-p x)
                   (keytype-p (caar x)))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule valtype-p-of-cdar-when-keyval-alist-p-when-valtype-p-nil
    (implies (and (valtype-p nil)
                  (keyval-alist-p x))
             (valtype-p (cdar x)))
    :requirement (and valtype-simple valtype-p-of-nil)
    :name valtype-p-of-cdar-when-keyval-alist-p
    :body (implies (keyval-alist-p x)
                   (valtype-p (cdar x)))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule keytype-p-of-caar-when-keyval-alist-p-when-not-keytype-p-nil-and-not-negated
    (implies (and (not (keytype-p nil))
                  (keyval-alist-p x))
             (iff (keytype-p (caar x))
                  (consp x)))
    :requirement (and not-keytype-p-of-nil
                      (not key-negatedp))
    :name keytype-p-of-caar-when-keyval-alist-p
    :body (implies (keyval-alist-p x)
                   (iff (keytype-p (caar x))
                        (consp x)))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule keytype-p-of-caar-when-keyval-alist-p-when-not-keytype-p-nil-and-negated
    (implies (and (not (keytype-p nil))
                  (keyval-alist-p x))
             (iff (non-keytype-p (caar x))
                  (not (consp x))))
    :requirement (and not-keytype-p-of-nil
                      key-negatedp)
    :name keytype-p-of-caar-when-keyval-alist-p
    :body (implies (keyval-alist-p x)
                   (iff (non-keytype-p (caar x))
                        (not (consp x))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule valtype-p-of-cdar-when-keyval-alist-p-when-not-valtype-p-nil-and-not-negated
    (implies (and (not (valtype-p nil))
                  (keyval-alist-p x))
             (iff (valtype-p (cdar x))
                  (consp x)))
    :requirement (and not-valtype-p-of-nil
                      (not val-negatedp))
    :name valtype-p-of-cdar-when-keyval-alist-p
    :body (implies (keyval-alist-p x)
                   (iff (valtype-p (cdar x))
                        (consp x)))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule valtype-p-of-cdar-when-keyval-alist-p-when-not-valtype-p-nil-and-negated
    (implies (and (not (valtype-p nil))
                  (keyval-alist-p x))
             (iff (non-valtype-p (cdar x))
                  (not (consp x))))
    :requirement (and not-valtype-p-of-nil
                      key-negatedp)
    :name valtype-p-of-cdar-when-keyval-alist-p
    :body (implies (keyval-alist-p x)
                   (iff (non-valtype-p (cdar x))
                        (not (consp x))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule keytype-p-of-caar-when-keyval-alist-p-when-unknown-nil
    (implies (keyval-alist-p x)
             (iff (keytype-p (caar x))
                  (or (consp x)
                      (keytype-p nil))))
    :requirement (and keytype-simple
                      (not keytype-p-of-nil)
                      (not not-keytype-p-of-nil)
                      (not key-negatedp))
    :name keytype-p-of-caar-when-keyval-alist-p
    :body (implies (keyval-alist-p x)
                   (iff (keytype-p (caar x))
                        (or (consp x)
                            (keytype-p nil))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule keytype-p-of-caar-when-keyval-alist-p-when-unknown-nil-negated
    (implies (keyval-alist-p x)
             (iff (non-keytype-p (caar x))
                  (and (not (consp x))
                       (non-keytype-p nil))))
    ;; :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))

    :requirement (and (not keytype-p-of-nil)
                      (not not-keytype-p-of-nil)
                      key-negatedp)
    :name keytype-p-of-caar-when-keyval-alist-p
    :body (implies (keyval-alist-p x)
                   (iff (non-keytype-p (caar x))
                        (and (not (consp x))
                             (non-keytype-p nil))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule valtype-p-of-cdar-when-keyval-alist-p-when-unknown-nil
    (implies (keyval-alist-p x)
             (iff (valtype-p (cdar x))
                  (or (consp x)
                      (valtype-p nil))))
    :requirement (and valtype-simple
                      (not valtype-p-of-nil)
                      (not not-valtype-p-of-nil)
                      (not val-negatedp))
    :name valtype-p-of-cdar-when-keyval-alist-p
    :body (implies (keyval-alist-p x)
                   (iff (valtype-p (cdar x))
                        (or (consp x)
                            (valtype-p nil))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule valtype-p-of-cdar-when-keyval-alist-p-when-unknown-nil-negated
    (implies (keyval-alist-p x)
             (iff (non-valtype-p (cdar x))
                  (and (not (consp x))
                       (non-valtype-p nil))))
    ;; :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))

    :requirement (and (not valtype-p-of-nil)
                      (not not-valtype-p-of-nil)
                      val-negatedp)
    :name valtype-p-of-cdar-when-keyval-alist-p
    :body (implies (keyval-alist-p x)
                   (iff (non-valtype-p (cdar x))
                        (and (not (consp x))
                             (non-valtype-p nil))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))


  (def-alistp-rule alistp-when-keyval-alist-p-tau
    (implies (and (keyval-alist-p x)
                  (not (keyval-alist-final-cdr-p t)))
             (alistp x))
    :rule-classes nil
    :inst-rule-classes :tau-system
    :name alistp-when-keyval-alist-p
    :requirement (and true-listp single-var)
    :body (implies (keyval-alist-p x)
                   (alistp x))
    :tags (:alistp))

  (def-alistp-rule alistp-when-keyval-alist-p-rewrite
    (implies (and (keyval-alist-p x)
                  (not (keyval-alist-final-cdr-p t)))
             (alistp x))
    :name alistp-when-keyval-alist-p-rewrite
    :disable t
    :requirement true-listp
    :body (implies (keyval-alist-p x)
                   (alistp x))
    :tags (:alistp :alistp-rewrite))

  (def-alistp-rule valtype-p-of-cdr-of-hons-assoc-equal-when-keyval-alist-p-unknown-valtype-p-nil
    (implies (keyval-alist-p x)
             (iff (valtype-p (cdr (hons-assoc-equal k x)))
                  (or (hons-assoc-equal k x)
                      (valtype-p nil))))
    :name valtype-p-of-cdr-of-hons-assoc-equal-when-keyval-alist-p
    :requirement (and valtype-simple
                      (not valtype-p-of-nil)
                      (not not-valtype-p-of-nil)
                      (not val-negatedp))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule valtype-p-of-cdr-of-hons-assoc-equal-when-keyval-alist-p-valtype-p-nil
    (implies (and (keyval-alist-p x)
                  (valtype-p nil))
             (valtype-p (cdr (hons-assoc-equal k x))))
    :name valtype-p-of-cdr-of-hons-assoc-equal-when-keyval-alist-p
    :requirement (and valtype-simple
                      valtype-p-of-nil)
    :body (implies (keyval-alist-p x)
                   (valtype-p (cdr (hons-assoc-equal k x))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule valtype-p-of-cdr-of-hons-assoc-equal-when-keyval-alist-p-not-valtype-p-nil
    (implies (and (keyval-alist-p x)
                  (not (valtype-p nil)))
             (iff (valtype-p (cdr (hons-assoc-equal k x)))
                  (hons-assoc-equal k x)))
    :name valtype-p-of-cdr-of-hons-assoc-equal-when-keyval-alist-p
    :requirement (and not-valtype-p-of-nil (not val-negatedp))
    :body (implies (keyval-alist-p x)
                   (iff (valtype-p (cdr (hons-assoc-equal k x)))
                        (hons-assoc-equal k x)))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule valtype-p-of-cdr-of-hons-assoc-equal-when-keyval-alist-p-unknown-valtype-p-nil-negated
    (implies (keyval-alist-p x)
             (iff (non-valtype-p (cdr (hons-assoc-equal k x)))
                  (not (or (hons-assoc-equal k x)
                           (valtype-p nil)))))
    :name valtype-p-of-cdr-of-hons-assoc-equal-when-keyval-alist-p
    :requirement (and (not valtype-p-of-nil)
                      (not not-valtype-p-of-nil)
                      val-negatedp)
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule valtype-p-of-cdr-of-hons-assoc-equal-when-keyval-alist-p-not-valtype-p-nil-negated
    (implies (and (keyval-alist-p x)
                  (not (valtype-p nil)))
             (iff (non-valtype-p (cdr (hons-assoc-equal k x)))
                  (not (hons-assoc-equal k x))))
    :name valtype-p-of-cdr-of-hons-assoc-equal-when-keyval-alist-p
    :requirement (and not-valtype-p-of-nil val-negatedp)
    :body (implies (keyval-alist-p x)
                   (iff (non-valtype-p (cdr (hons-assoc-equal k x)))
                        (not (hons-assoc-equal k x))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-alistp-rule keyval-alist-p-of-hons-acons
    (equal (keyval-alist-p (hons-acons a n x))
           (and (keytype-p a)
                (valtype-p n)
                (keyval-alist-p x))))

  (def-alistp-rule keyval-alist-p-of-hons-shrink-alist
    (implies (and (keyval-alist-p x)
                  (keyval-alist-p y))
             (keyval-alist-p (hons-shrink-alist x y)))
    :name keyval-alist-p-of-hons-shrink-alist)

  (def-alistp-rule alistp-of-put-assoc
    (implies (and (keyval-alist-p x)
                  (not (keyval-alist-final-cdr-p t)))
             (iff (keyval-alist-p (put-assoc-equal name val x))
                  (and (keytype-p name) (valtype-p val))))
    :name keyval-alist-p-of-put-assoc
    :requirement true-listp
    :body
    (implies (and (keyval-alist-p x))
             (iff (keyval-alist-p (put-assoc-equal name val x))
                  (and (keytype-p name) (valtype-p val))))
    :tags (:alistp))

  (def-alistp-rule valtype-p-of-cdr-of-assoc-when-keyval-alist-p-valtype-p-nil
    (implies (and (keyval-alist-p x)
                  (valtype-p nil))
             (valtype-p (cdr (assoc-equal k x))))
    :name valtype-p-of-cdr-of-assoc-when-keyval-alist-p
    :requirement valtype-p-of-nil
    :body (implies (keyval-alist-p x)
                   (valtype-p (cdr (assoc-equal k x)))))

  (def-alistp-rule alistp-of-remove-assoc
    (implies (keyval-alist-p x)
             (keyval-alist-p (remove-assoc-equal name x)))
    :name keyval-alist-p-of-remove-assoc
    :requirement true-listp
    :body
    (implies (keyval-alist-p x)
             (keyval-alist-p (remove-assoc-equal name x)))
    :tags (:alistp)))


;; expensive...
(in-theory (disable alistp-when-keyval-alist-p-rewrite))

;; missing:
;; keyval-alist-p-of-make-fal
