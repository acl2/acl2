; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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

(in-package "RSTOBJ")
(include-book "misc/records" :dir :system)
(local (include-book "misc/equal-by-g" :dir :system))

; g-delete-keys.lisp
;
; This just deletes a bunch of keys from a record.  It is used in the
; development of fancy-worseguy and to ensure that the MISC fields we add in
; our record stobjs do not overlap with the real stobj fields.

(defund g-delete-keys (keys x)
  (declare (xargs :guard t
                  :measure (len keys)))
  (if (atom keys)
      x
    (g-delete-keys (cdr keys)
                   (s (car keys) nil x))))

(defthm g-of-g-delete-keys
  (equal (g key (g-delete-keys keys x))
         (if (member-equal key keys)
             nil
           (g key x)))
  :hints(("Goal"
          :in-theory (enable g-delete-keys)
          :induct (g-delete-keys keys x))))

(defthm g-delete-keys-of-s-diff
  (implies (not (member-equal name keys))
           (equal (g-delete-keys keys (s name val x))
                  (s name val (g-delete-keys keys x))))
  :hints(("Goal"
          :in-theory (enable acl2::g-of-s-redux)
          :use ((:functional-instance
                 acl2::equal-by-g
                 (acl2::equal-by-g-hyp
                  (lambda () (not (member-equal name keys))))
                 (acl2::equal-by-g-lhs
                  (lambda () (s name val (g-delete-keys keys x))))
                 (acl2::equal-by-g-rhs
                  (lambda () (g-delete-keys keys (s name val x)))))))))