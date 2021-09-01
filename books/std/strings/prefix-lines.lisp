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

(in-package "STR")
(include-book "cat")
(local (include-book "arithmetic"))

(defsection prefix-lines
  :parents (lines)
  :short "Add a prefix to every line in a string."
  :long "<p>@(call prefix-lines) builds a new string by adding @('prefix') to
the start of every line in the string @('x').  The start of @('x') is regarded
as the start of a line, and also gets the prefix.  For instance,</p>

@({
 (prefix-lines \"hello world
 goodbye world\" \"  ** \")
})

<p>Would create the following result:</p>

@({
 \"  ** hello world
   ** goodbye world\"
})

<p>This is sometimes useful for indenting blobs of text when you are trying to
pretty-print things.  The operation is fairly efficient: we cons everything
into a character list and then coerce it back into a string at the end.</p>"

  (defund prefix-lines-aux (n x xl acc prefix)
    (declare (xargs :guard (and (natp n)
                                (stringp x)
                                (natp xl)
                                (<= n xl)
                                (= xl (length x))
                                (stringp prefix))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (let ((n  (lnfix n))
          (xl (lnfix xl)))
      (if (mbe :logic (zp (- xl n))
               :exec (int= n xl))
          acc
        (let* ((char (char x n))
               (acc  (cons char acc))
               (acc  (if (eql char #\Newline)
                         (str::revappend-chars prefix acc)
                       acc)))
          (prefix-lines-aux (+ 1 n) x xl acc prefix)))))

  (defund prefix-lines (x prefix)
    (declare (xargs :guard (and (stringp x)
                                (stringp prefix))
                    :verify-guards nil))
    (let* ((acc    (str::revappend-chars prefix nil))
           (rchars (prefix-lines-aux 0 x (length x) acc prefix)))
      (rchars-to-string rchars)))

  (local (in-theory (enable prefix-lines-aux prefix-lines)))

  (defthm character-listp-of-prefix-lines-aux
    (implies (and (natp n)
                  (stringp x)
                  (<= n xl)
                  (= xl (length x))
                  (stringp rprefix)
                  (character-listp acc))
             (character-listp (prefix-lines-aux n x xl acc prefix)))
    :hints(("Goal" :induct (prefix-lines-aux n x xl acc prefix))))

  (verify-guards prefix-lines)

  (defthm stringp-of-prefix-lines
    (stringp (prefix-lines x prefix))
    :rule-classes :type-prescription))
