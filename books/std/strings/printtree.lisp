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

(in-package "STR")

(include-book "cat-base")

(defsection printable
  :parents (printtree)
  :short "A printable element: a string, a character, or NIL, which we take as
          equivalent to the empty string."
  :long "<p>The main operation on a printable element is @('printable->str'),
which turns it into a string.  Printable objects are the leaves of @(see
printtree) objects.</p>"
  (defund printable-p (x)
    (declare (xargs :guard t))
    (or (stringp x)
        (characterp x)
        (eq x nil)))

  (local (in-theory (enable printable-p)))

  (defthm printable-p-compound-recognizer
    (iff (printable-p x)
         (or (stringp x)
             (characterp x)
             (eq x nil)))
    :rule-classes :compound-recognizer)

  (defthm printable-p-when-stringp
    (implies (stringp x)
             (printable-p x)))

  (defthm printable-p-when-characterp
    (implies (characterp x)
             (printable-p x)))

  (defund printable-fix$ (x)
    (declare (xargs :guard t))
    (and (printable-p x) x))

  (local (in-theory (enable printable-fix$)))

  (defund printable-fix (x)
    (declare (xargs :guard (printable-p x)))
    (mbe :logic (and (printable-p x) x)
         :exec x))

  (local (in-theory (enable printable-fix)))

  (defthm printable-p-of-printable-fix
    (printable-p (printable-fix x)))

  (defthm printable-fix-when-printable-p
    (implies (printable-p x)
             (equal (printable-fix x) x)))

  (defthm printable-fix$-is-printable-fix
    (equal (printable-fix$ x)
           (printable-fix x)))

  ;; (local (in-theory (disable printable-fix)))

  (defund printable->str (x)
    (declare (xargs :guard (printable-p x)))
    (cond ((stringp x) x)
          ((characterp x) (coerce (list x) 'string))
          (t "")))

  (local (in-theory (enable printable->str)))

  (defun revappend-printable (x acc)
    (declare (Xargs :guard (printable-p x)
                    :guard-hints (("goal" :in-theory (enable revappend-chars)))))
    (mbe :logic (revappend-chars (printable->str x) acc)
         :exec (cond ((stringp x) (revappend-chars x acc))
                     ((characterp x) (cons x acc))
                     (t acc)))))

(defsection printtree
  :parents (std/strings)
  :short "A tree structure for building up a block of text from components."
  :long "<p>A printtree is simply either a @(see printable) object or else a
cons of @(see printtree) objects.  It represents a block of text formed by
concatenating together all its leaves in reverse order, i.e. from rightmost to
leftmost.</p>

<p>It might seem like an odd choice to standardize on right-to-left.  We do so
because usually we build up a block of text by adding text to the end, and
usually we expect trees of conses to be longer on the right than on the left,
like lists.  Some Lisps might be especially optimized for such constructs and
not so much for the other kind.</p>

<p>A printtree object can be turned into a string using the function
@('printtree->str').</p>

<p>In case there's any reason to accumulate a printtree left to right instead,
it can be turned into a string in reverse order using
@('printtree->str-left2right').</p>

<p>@('pcat') is a convenient macro for composing printtree objects together;
think of it as string concatenation for printtree objects.  @('(pcat a b c d)')
simply macroexpands to @('(list* d c b a)'), so that @('(printtree->str (pcat a
b c d))') equals @('(concatenate \'string (printtree->str a)
... (printtree->str d))').</p>"

  (defund printtree-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        (printable-p x)
      (and (printtree-p (car x))
           (printtree-p (cdr x)))))

  (local (in-theory (enable printtree-p)))

  (defthm printtree-p-when-printable-p
    (implies (printable-p x)
             (printtree-p x)))

  (defthm printtree-p-of-cons
    (equal (printtree-p (cons x y))
           (and (printtree-p x)
                (printtree-p y))))

  (defthm printtree-p-when-consp
    (implies (and (consp x)
                  (printtree-p (car x))
                  (printtree-p (cdr x)))
             (printtree-p x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil))))

  (defund printtree-fix$ (x)
    (declare (xargs :guard t))
    (if (atom x)
        (printable-fix$ x)
      (cons (printtree-fix$ (car x))
            (printtree-fix$ (cdr x)))))

  (defund printtree-fix (x)
    (declare (xargs :guard (printtree-p x)
                    :verify-guards nil))
    (mbe :logic (if (atom x)
                    (printable-fix x)
                  (cons (printtree-fix (car x))
                        (printtree-fix (cdr x))))
         :exec x))

  (local (in-theory (enable printtree-fix$ printtree-fix)))

  (local (defthm printtree-fix$-is-printtree-fix
           (equal (printtree-fix$ x)
                  (printtree-fix x))))

  (defthm printtree-p-of-printtree-fix
    (printtree-p (printtree-fix x)))

  (defthm printtree-fix-when-printtree-p
    (implies (printtree-p x)
             (equal (printtree-fix x) x)))

  (verify-guards printtree-fix)

  (defthm printtree-fix-of-cons
    (equal (printtree-fix (cons a b))
           (cons (printtree-fix a)
                 (printtree-fix b))))

  (defund printtree->strlist-aux (x acc)
    (declare (xargs :guard (printtree-p x)))
    (if (atom x)
        ;; optimization to save a cons on a null entry
        (if (printable-fix x)
            (cons (printable->str x) acc)
          acc)
      (printtree->strlist-aux (cdr x)
                              (printtree->strlist-aux (car x) acc))))

  (local (in-theory (enable printtree->strlist-aux)))

  (defund printtree->strlist (x)
    (declare (xargs :guard (printtree-p x)
                    :verify-guards nil))
    (mbe :logic (if (atom x)
                    (and (printable-fix x)
                         (list (printable->str x)))
                  (append (printtree->strlist (cdr x))
                          (printtree->strlist (car x))))
         :exec (printtree->strlist-aux x nil)))

  (local (in-theory (enable printtree->strlist)))

  (defthm printtree->strlist-aux-elim
    (equal (printtree->strlist-aux x acc)
           (append (printtree->strlist x) acc)))

  (verify-guards printtree->strlist)

  (defthm string-listp-of-printtree->strlist
    (string-listp (printtree->strlist x)))

  (defund revappend-printtree (x acc)
    (declare (xargs :guard (printtree-p x)))
    (if (atom x)
        (revappend-printable x acc)
      (revappend-printtree (car x) (revappend-printtree (cdr x) acc))))

  (local (in-theory (enable revappend-printtree)))

  (local (defthm printable->str-when-empty
           (implies (not (printable-fix x))
                    (equal (printable->str x) ""))
           :hints(("Goal" :in-theory (enable printable-fix
                                             printable->str)))))

  (local (defthm append-of-append
           (equal (append (append x y) z)
                  (append x y z))))

  (local (defthm string-append-lst-of-append
           (equal (string-append-lst (append x y))
                  (string-append (string-append-lst x)
                                 (string-append-lst y)))))

  (local (defthm revappend-of-append
           (equal (revappend (append a b) c)
                  (revappend b (revappend a c)))))

  (defthm revappend-printtree-elim
    (equal (revappend-printtree x acc)
           (revappend-chars (string-append-lst (printtree->strlist x)) acc))
    :hints(("Goal" :in-theory (enable revappend-chars)
            :induct (revappend-printtree x acc))))

  ;; note: this function is smashed with an even faster under-the-hood
  ;; definition when we load fast-cat.lisp.  This one at least is
  ;; linear, rather than quadratic, as it would be if using string-append-lst
  ;; or the logic definition of printtree->str below.
  (defun printtree->str1 (x)
    (declare (xargs :guard (printtree-p x)))
    (rchars-to-string (revappend-printtree x nil)))

  (defund printtree->str (x)
    (declare (xargs :guard (printtree-p x)
                    :verify-guards nil))
    (mbe :logic (if (atom x)
                    (printable->str x)
                  (concatenate 'string
                               (printtree->str (cdr x))
                               (printtree->str (car x))))
         ;; Maybe add an under-the-hood definition that doesn't even need to
         ;; make the list?
         :exec (if (atom x)
                   (printable->str x) ;; optimization
                 (printtree->str1 x))))

  (local (in-theory (enable printtree->str)))

  (defthm printtree->str-of-cons
    (equal (printtree->str (cons a b))
           (string-append (printtree->str b)
                          (printtree->str a))))

  (defthm string-append-lst-of-printtree->strlist
    (equal (string-append-lst (printtree->strlist x))
           (printtree->str x))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable printable-fix printable->str)))))

  (local (defthm revappend-of-revappend
           (equal (revappend (revappend a b) c)
                  (revappend b (append a c)))))

  (verify-guards printtree->str
    :hints(("Goal" :in-theory (enable revappend-chars))))

  (local (defthm string-listp-of-revappend
           (implies (and (string-listp x) (string-listp y))
                    (string-listp (revappend x y)))))

  (defund printtree->str-left2right (x)
    (declare (xargs :guard (printtree-p x)))
    (fast-string-append-lst (reverse (printtree->strlist x))))

  (local (in-theory (enable printtree->str-left2right))))



