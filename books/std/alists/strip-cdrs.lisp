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
(include-book "xdoc/top" :dir :system)
(include-book "../lists/list-defuns")
(local (include-book "../lists/take"))
(local (in-theory (enable strip-cdrs)))

(local (defthm commutativity-2-of-+
         (equal (+ x (+ y z))
                (+ y (+ x z)))))

(local (defthm fold-consts-in-+
         (implies (and (syntaxp (quotep x))
                       (syntaxp (quotep y)))
                  (equal (+ x (+ y z)) (+ (+ x y) z)))))

(local (defthm distributivity-of-minus-over-+
         (equal (- (+ x y)) (+ (- x) (- y)))))

(local (defthm take-of-nil
         (equal (take n nil)
                (replicate n nil))
         :hints(("Goal" :in-theory (enable replicate)))))

(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil)
                nil)))

(defsection std/alists/strip-cdrs
  :parents (std/alists strip-cdrs)
  :short "Lemmas about @(see strip-cdrs) available in the @(see std/alists)
library."

  :long "<p>Note that @('strip-cdrs') is a \"traditional\" alist function: it
has an @(see alistp) guard and fails to respect the non-alist convention.  We
generally prefer to work with @(see alist-vals) instead.</p>

<p>Even so, we provide many lemmas for working with @('strip-cdrs'), in case
for some reason that's what you want to do.</p>"

  (defthm strip-cdrs-when-atom
    (implies (atom x)
             (equal (strip-cdrs x)
                    nil)))

  (defthm strip-cdrs-of-cons
    (equal (strip-cdrs (cons a x))
           (cons (cdr a)
                 (strip-cdrs x))))

  (defthm len-of-strip-cdrs
    (equal (len (strip-cdrs x))
           (len x)))

  (defthm consp-of-strip-cdrs
    (equal (consp (strip-cdrs x))
           (consp x)))

  (defthm car-of-strip-cdrs
    (equal (car (strip-cdrs x))
           (cdr (car x))))

  (defthm cdr-of-strip-cdrs
    (equal (cdr (strip-cdrs x))
           (strip-cdrs (cdr x))))

  (defthm strip-cdrs-under-iff
    (iff (strip-cdrs x)
         (consp x)))

  (defthm strip-cdrs-of-list-fix
    (equal (strip-cdrs (list-fix x))
           (strip-cdrs x))
    :hints(("Goal" :in-theory (enable list-fix))))

  (defcong list-equiv equal (strip-cdrs x) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (strip-cdrs-of-list-fix))
            :use ((:instance strip-cdrs-of-list-fix (x x))
                  (:instance strip-cdrs-of-list-fix (x x-equiv))))))

  (encapsulate
    ()
    (local (defthm l1
             (implies (and (member-equal a x)
                           (not (consp a)))
                      (member-equal nil (strip-cdrs x)))))

    (local (defthm l2
             (implies (member-equal (cons a b) x)
                      (member-equal b (strip-cdrs x)))))

    (local (defthm l3
             (implies (and (subsetp x y)
                           (member a x))
                      (member (cdr a) (strip-cdrs y)))
             :hints(("Goal" :induct (len x)))))

    (local (defthm l4
             (implies (subsetp x y)
                      (subsetp (strip-cdrs x) (strip-cdrs y)))
             :hints(("Goal" :induct (len x)))))

    (defcong set-equiv set-equiv (strip-cdrs x) 1
      :hints(("Goal" :in-theory (enable set-equiv)))))

  (defthm strip-cdrs-of-append
    (equal (strip-cdrs (append x y))
           (append (strip-cdrs x)
                   (strip-cdrs y))))

  (defthm strip-cdrs-of-rev
    (equal (strip-cdrs (rev x))
           (rev (strip-cdrs x)))
    :hints(("Goal" :in-theory (enable rev))))

  (defthm strip-cdrs-of-revappend
    (equal (strip-cdrs (revappend x y))
           (revappend (strip-cdrs x)
                      (strip-cdrs y))))

  (defthm strip-cdrs-of-replicate
    (equal (strip-cdrs (replicate n x))
           (replicate n (cdr x)))
    :hints(("Goal" :in-theory (enable replicate))))

  (defthm strip-cdrs-of-take
    (equal (strip-cdrs (take n x))
           (take n (strip-cdrs x)))
    :hints(("Goal" :in-theory (enable replicate))))

  (defthm strip-cdrs-of-nthcdr
    (equal (strip-cdrs (nthcdr n x))
           (nthcdr n (strip-cdrs x))))

  (defthm strip-cdrs-of-last
    (equal (strip-cdrs (last x))
           (last (strip-cdrs x))))

  (defthm strip-cdrs-of-butlast
    (equal (strip-cdrs (butlast x n))
           (butlast (strip-cdrs x) n)))

  (defthm strip-cdrs-of-pairlis$
    (equal (strip-cdrs (pairlis$ x y))
           (if (<= (len x) (len y))
               (take (len x) y)
             (append y (replicate (- (len x) (len y)) nil))))
    :hints(("Goal"
            :induct (pairlis$ x y)
            :in-theory (enable replicate)))))

