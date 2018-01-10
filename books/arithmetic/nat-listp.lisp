;; Nat-listp.
;;

;; Note: Contributed initially by Sol Swords; modified by Matt Kaufmann.
;; Adapted from unicode/nat-listp.lisp, but INCOMPATIBLE with it.  This
;; version of nat-listp is similar to built-in ACL2 functions integer-listp,
;; symbol-listp, etc, in that it implies true-listp.

; Copyright (C) 2014 Centaur Technology
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

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(in-theory (disable nat-listp))

(defsection arithmetic/nat-listp
  :parents (nat-listp)
  :short "Lemmas about @(see nat-listp) available in the @('arithmetic/nat-listp')
book."

  :long "<p>Note: this book is extremely minimal.  You should generally instead
see @(see std/typed-lists/nat-listp).  Note however that this book is part
of a widely-used library of basic arithmetic facts: @('(include-book
\"arithmetic/top\" :dir :system)').</p>"

  (local (in-theory (enable nat-listp)))

  (defthm nat-listp-implies-true-listp
    (implies (nat-listp x)
             (true-listp x))
    :rule-classes (:rewrite :compound-recognizer))

  (in-theory (disable (:rewrite nat-listp-implies-true-listp)))

  (defthm nat-listp-when-not-consp
    (implies (not (consp x))
             (equal (nat-listp x)
                    (not x)))
    :hints(("Goal" :in-theory (enable nat-listp))))

  (defthm nat-listp-of-cons
    (equal (nat-listp (cons a x))
           (and (natp a)
                (nat-listp x)))
    :hints(("Goal" :in-theory (enable nat-listp))))

  (defthm nat-listp-of-append-weak
    ;; [Jared] added "weak" in support of std/typed-lists/nat-listp
    (implies (true-listp x)
             (equal (nat-listp (append x y))
                    (and (nat-listp x)
                         (nat-listp y)))))

  (defthm car-nat-listp
    (implies (and (nat-listp x)
                  x)
             (natp (car x)))
    :rule-classes :forward-chaining)

  (defthm nat-listp-of-cdr-when-nat-listp
    ;; [Jared] added double-rewrite in support of std/typed-lists/nat-listp
    (implies (nat-listp (double-rewrite x))
             (nat-listp (cdr x)))))
