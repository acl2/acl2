; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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
;
; Additional copyright notice for make-character-list.lisp:
;
; This file is adapted from the Unicode library, Copyright (C) 2005-2013 by
; Jared Davis, which was also released under the GPL.

(in-package "STR")
(include-book "char-fix")
(local (include-book "std/lists/append" :dir :system))

(in-theory (disable make-character-list))

(defsection std/strings/make-character-list
  :parents (coercion make-character-list)
  :short "Lemmas about @(see make-character-list) in the @(see std/strings)
library."

  :long "<p>This function is normally not anything you would ever want to use.
It is notable mainly for the role it plays in the completion axiom for @(see
coerce).</p>"

  (local (in-theory (enable make-character-list)))

  (defthm make-character-list-when-atom
    (implies (atom x)
             (equal (make-character-list x)
                    nil)))

  (defthm make-character-list-of-cons
    (equal (make-character-list (cons a x))
           (cons (char-fix a)
                 (make-character-list x))))

  (defthm consp-of-make-character-list
    (equal (consp (make-character-list x))
           (consp x)))

  (defthm make-character-list-under-iff
    (iff (make-character-list x)
         (consp x)))

  (defthm len-of-make-character-list
    (equal (len (make-character-list x))
           (len x)))

  (defthm make-character-list-when-character-listp
    (implies (character-listp x)
             (equal (make-character-list x)
                    x)))

  (defthm character-listp-of-make-character-list
    (character-listp (make-character-list x)))

  (defthm make-character-list-of-append
    (equal (make-character-list (append x y))
           (append (make-character-list x)
                   (make-character-list y))))

  (defthm make-character-list-of-revappend
    (equal (make-character-list (revappend x y))
           (revappend (make-character-list x)
                      (make-character-list y)))))

