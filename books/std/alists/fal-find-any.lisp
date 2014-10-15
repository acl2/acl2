; Standard Association Lists Library
; Copyright (C) 2013-2014 Centaur Technology
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
(include-book "std/util/define" :dir :system)
(include-book "alist-equiv")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "hons-assoc-equal"))

(define fal-find-any
  :parents (std/alists)
  :short "Find the first of many keys bound in a fast alist."
  ((keys  "List of keys to look for.")
   (alist "Fast alist to search."))
  :returns
  (ans "A @('(key . value)') pair on success, or @('nil') on failure.")

  :long "<p>We walk over each @('key') in @('keys').  As soon as we find a
@('key') that is bound in @('alist'), we return its value.  If none of the keys
are bound in @('alist'), we return @('nil').</p>"

  (if (atom keys)
      nil
    (or (hons-get (car keys) alist)
        (fal-find-any (cdr keys) alist)))
  ///
  (defthm fal-find-any-when-atom
    (implies (atom keys)
             (equal (fal-find-any keys alist)
                    nil)))

  (defthm fal-find-any-when-empty-alist
    (implies (atom alist)
             (not (fal-find-any keys alist))))

  (defthm fal-find-any-of-cons
    (equal (fal-find-any (cons key keys) alist)
           (or (hons-get key alist)
               (fal-find-any keys alist))))

  (defthm type-of-fal-find-any
    (or (not (fal-find-any keys alist))
        (consp (fal-find-any keys alist)))
    :rule-classes :type-prescription)

  (defthm consp-of-fal-find-any
    (iff (consp (fal-find-any keys alist))
         (fal-find-any keys alist)))

  (defthm fal-find-any-of-list-fix-keys
    (equal (fal-find-any (list-fix keys) alist)
           (fal-find-any keys alist))
    :hints(("Goal" :in-theory (enable list-fix))))

  (defcong list-equiv equal (fal-find-any keys alist) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (fal-find-any-of-list-fix-keys))
            :use ((:instance fal-find-any-of-list-fix-keys (keys keys))
                  (:instance fal-find-any-of-list-fix-keys (keys keys-equiv))))))

  (defcong alist-equiv equal (fal-find-any keys alist) 2
    :hints(("Goal" :induct t)))

  (defthm fal-find-any-of-append
    (equal (fal-find-any (append x y) alist)
           (or (fal-find-any x alist)
               (fal-find-any y alist))))

  (local (defthm intersectp-equal-when-atom
           (implies (atom x)
                    (equal (intersectp-equal x y)
                           nil))
           :hints(("Goal" :in-theory (enable intersectp-equal)))))

  (defthm fal-find-any-under-iff
    (iff (fal-find-any keys alist)
         (intersectp-equal keys (alist-keys alist)))
    :hints(("Goal" :in-theory (enable intersectp-equal))))

  (defcong set-equiv iff (fal-find-any keys alist) 1
    :hints(("Goal" :in-theory (disable set-equiv))))

  (defthm hons-assoc-equal-when-found-by-fal-find-any
    (implies (and (equal (fal-find-any keys alist) ans)
                  ans)
             (equal (hons-assoc-equal (car ans) alist)
                    ans))
    :hints(("Goal" :in-theory (enable intersectp-equal)))))
