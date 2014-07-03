; Standard Association Lists Library
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "alist-equiv")
(local (include-book "../lists/append"))
(local (include-book "../lists/rev"))
(local (include-book "../lists/equiv"))


(defsection fal-extract-vals
  :parents (std/alists)
  :short "@(call fal-extract) extracts the values associated with the given
@('keys') in the alist @('al').  For unbound keys, we arbitrarily assign the
value @('nil')."

  :long "<p>This is similar to @(see fal-extract) except that we only return
the values instead of a sub-alist, and we don't skip unbound keys.</p>

<p>This is a \"modern\" alist function that respects the non-alist convention;
see @(see std/alists) for discussion of this convention.</p>

<p>This function is optimized for @(see fast-alists).  Ordinary alists will be
temporarily made fast.</p>"

  (defund fal-extract-vals1 (keys al)
    "Assumes AL is fast"
    (declare (xargs :guard t))
    (if (atom keys)
        nil
      (cons (cdr (hons-get (car keys) al))
            (fal-extract-vals1 (cdr keys) al))))

  (defund fal-extract-vals (keys al)
    "Makes AL fast if necessary"
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom keys)
             nil
           (cons (cdr (hons-get (car keys) al))
                 (fal-extract-vals (cdr keys) al)))
         :exec
         (with-fast-alist al
           (fal-extract-vals1 keys al))))

  (local (in-theory (enable fal-extract-vals)))

  (defthm fal-extract-vals1-removal
    (equal (fal-extract-vals1 keys al)
           (fal-extract-vals keys al))
    :hints(("Goal" :in-theory (enable fal-extract-vals1))))

  (verify-guards fal-extract-vals)

  (defthm fal-extract-vals-when-atom
    (implies (atom keys)
             (equal (fal-extract-vals keys al)
                    nil)))

  (defthm fal-extract-vals-of-cons
    (equal (fal-extract-vals (cons a keys) al)
           (cons (cdr (hons-get a al))
                 (fal-extract-vals keys al))))

  (defthm fal-extract-vals-of-list-fix
    (equal (fal-extract-vals (list-fix keys) al)
           (fal-extract-vals keys al)))

  (defcong list-equiv equal (fal-extract-vals keys al) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (fal-extract-vals-of-list-fix))
            :use ((:instance fal-extract-vals-of-list-fix (keys keys))
                  (:instance fal-extract-vals-of-list-fix (keys keys-equiv))))))

  (defcong alist-equiv equal (fal-extract-vals keys al) 2)

  (defthm fal-extract-vals-of-append
    (equal (fal-extract-vals (append x y) al)
           (append (fal-extract-vals x al)
                   (fal-extract-vals y al))))

  (defthm fal-extract-vals-of-rev
    (equal (fal-extract-vals (rev x) al)
           (rev (fal-extract-vals x al))))

  (defthm fal-extract-vals-of-revappend
    (equal (fal-extract-vals (revappend x y) al)
           (revappend (fal-extract-vals x al)
                      (fal-extract-vals y al))))

  ;; BOZO should probably add something like:
  ;; (defcong set-equiv set-equiv (fal-extract-vals keys al) 1)

  (defthm len-of-fal-extract-vals
    (equal (len (fal-extract-vals x al))
           (len x))))


