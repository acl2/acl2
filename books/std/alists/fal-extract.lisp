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
(include-book "std/util/bstar" :dir :system)

(local (in-theory (enable list-fix rev)))

(defsection fal-extract
  :parents (std/alists)
  :short "@(call fal-extract) extracts a \"subset\" of the alist @('al') by
binding every key in @('keys') to its value in @('al'), skipping any unbound
keys."

  :long "<p>This is a \"modern\" alist function that respects the non-alist
convention; see @(see std/alists) for discussion of this convention.</p>

<p>This function is optimized for @(see fast-alists).  Ordinary alists will be
temporarily made fast.</p>"

  (defund fal-extract1 (keys al)
    "Assumes AL is fast"
    (declare (xargs :guard t))
    (b* (((when (atom keys))
          nil)
         (look (hons-get (car keys) al))
         ((when look)
          (cons look (fal-extract1 (cdr keys) al))))
      (fal-extract1 (cdr keys) al)))

  (defund fal-extract (keys al)
    "Makes AL fast if necessary"
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (b* (((when (atom keys))
               nil)
              (look (hons-get (car keys) al))
              ((when look)
               (cons look (fal-extract (cdr keys) al))))
           (fal-extract (cdr keys) al))
         :exec
         (with-fast-alist al
           (fal-extract1 keys al))))

  (local (in-theory (enable fal-extract)))

  (defthm fal-extract1-removal
    (equal (fal-extract1 keys al)
           (fal-extract keys al))
    :hints(("Goal" :in-theory (enable fal-extract1))))

  (verify-guards fal-extract)

  (defthm fal-extract-when-atom
    (implies (atom keys)
             (equal (fal-extract keys al)
                    nil)))

  (defthm fal-extract-of-cons
    (equal (fal-extract (cons a keys) al)
           (if (hons-get a al)
               (cons (hons-get a al)
                     (fal-extract keys al))
             (fal-extract keys al))))

  (defthm alistp-of-fal-extract
    (alistp (fal-extract keys al)))

  (defthm fal-extract-of-list-fix-keys
    (equal (fal-extract (list-fix keys) al)
           (fal-extract keys al)))

  (defcong list-equiv equal (fal-extract keys al) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (fal-extract-of-list-fix-keys))
            :use ((:instance fal-extract-of-list-fix-keys (keys keys))
                  (:instance fal-extract-of-list-fix-keys (keys keys-equiv))))))

  (defcong alist-equiv equal (fal-extract keys al) 2
    :hints(("Goal" :induct t)))

  (defthm fal-extract-of-append
    (equal (fal-extract (append x y) al)
           (append (fal-extract x al)
                   (fal-extract y al))))

  (defthm fal-extract-of-rev
    (equal (fal-extract (rev x) al)
           (rev (fal-extract x al))))

  (defthm fal-extract-of-revappend
    (equal (fal-extract (revappend x y) al)
           (revappend (fal-extract x al)
                      (fal-extract y al))))

  (defthm len-of-fal-extract
    (<= (len (fal-extract x al))
        (len x))
    :rule-classes ((:rewrite) (:linear)))

  (local (defthm l0
           (implies (hons-assoc-equal key alist)
                    (equal (car (hons-assoc-equal key alist))
                           key))))

  (defthm hons-assoc-equal-fal-extract
    (equal (hons-assoc-equal x (fal-extract keys al))
           (and (member-equal x keys)
                (hons-assoc-equal x al)))
    :hints(("Goal" :induct (fal-extract keys al))))

  ;; BOZO eventually add this... proven in centaur/misc/fast-alists, but uses
  ;; set-reasoning:
  ;;
  ;;  (defcong set-equiv alist-equiv (fal-extract keys al) 1)


  )
