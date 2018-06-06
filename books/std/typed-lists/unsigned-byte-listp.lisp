; Standard Typed Lists Library
; unsigned-byte-listp.lisp -- originally part of the Unicode library
; Copyright (C) 2005-2013 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(set-verify-guards-eagerness 2)
(include-book "std/lists/repeat" :dir :system)
(local (include-book "std/lists/take" :dir :system))
(include-book "arithmetic/nat-listp" :dir :system)


(defsection unsigned-byte-listp
  :parents (std/typed-lists unsigned-byte-p)
  :short "Recognizer for lists of @(see unsigned-byte-p)'s."
  :long "<p>BOZO consider switching this book to use deflist.</p>"

  (local (in-theory (disable unsigned-byte-p)))

  (defund unsigned-byte-listp (n x)
    (if (atom x)
        (null x)
      (and (unsigned-byte-p n (car x))
           (unsigned-byte-listp n (cdr x)))))

  (defthm unsigned-byte-listp-when-not-consp
    (implies (not (consp x))
             (equal (unsigned-byte-listp n x)
                    (not x)))
    :hints(("Goal" :in-theory (enable unsigned-byte-listp))))

  (defthm unsigned-byte-listp-of-cons
    (equal (unsigned-byte-listp n (cons a x))
           (and (unsigned-byte-p n a)
                (unsigned-byte-listp n x)))
    :hints(("Goal" :in-theory (enable unsigned-byte-listp))))

  (defthm unsigned-byte-p-of-car-when-unsigned-byte-listp
    (implies (unsigned-byte-listp width x)
             (equal (unsigned-byte-p width (car x))
                    (consp x)))
    :rule-classes (:rewrite :forward-chaining))

  (defthm nat-listp-when-unsigned-byte-listp
    (implies (unsigned-byte-listp width x)
             (nat-listp x))
    :hints(("Goal" :induct (len x))))

  (defthm true-listp-when-unsigned-byte-listp
    (implies (unsigned-byte-listp width x)
             (true-listp x))
    :hints(("Goal" :induct (len x))))

  (defthm unsigned-byte-listp-of-append
    (equal (unsigned-byte-listp width (append x y))
           (and (unsigned-byte-listp width (list-fix x))
                (unsigned-byte-listp width y)))
    :hints(("Goal" :induct (len x))))

  (defthm unsigned-byte-listp-of-list-fix-when-unsigned-byte-listp
    (implies (unsigned-byte-listp width x)
             (unsigned-byte-listp width (list-fix x))))

  (defthm unsigned-byte-listp-of-repeat
    (equal (unsigned-byte-listp width (repeat n x))
           (or (zp n)
               (unsigned-byte-p width x)))
    :hints(("Goal" :in-theory (enable repeat))))

  (defthm unsigned-byte-listp-of-take
    (implies (unsigned-byte-listp width x)
             (equal (unsigned-byte-listp width (take n x))
                    (or (zp n)
                        (<= n (len x))))))

  (defthm unsigned-byte-listp-of-take-past-length
    (implies (and (natp k)
                  (< (len x) k))
             (not (unsigned-byte-listp width (take k x)))))

  (defthm unsigned-byte-listp-of-nthcdr
    (implies (unsigned-byte-listp width x)
             (unsigned-byte-listp width (nthcdr n x))))

  (defthm unsigned-byte-listp-when-take-and-nthcdr
    (implies (and (unsigned-byte-listp width (take n x))
                  (unsigned-byte-listp width (nthcdr n x)))
             (unsigned-byte-listp width x)))

  (defthm unsigned-byte-listp-of-update-nth
    (implies (and (unsigned-byte-listp n l)
                  (< key (len l)))
             (equal (unsigned-byte-listp n (update-nth key val l))
                    (unsigned-byte-p n val)))))



