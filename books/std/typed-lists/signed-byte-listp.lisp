; Standard Typed Lists Library
; signed-byte-listp.lisp -- originally part of the Unicode library
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
(include-book "xdoc/top" :dir :system)

(local (in-theory (disable signed-byte-p)))

(defsection signed-byte-listp
  :parents (std/typed-lists signed-byte-p)
  :short "Recognizer for lists of @(see signed-byte-p)'s."
  :long "<p>BOZO consider switching this book to use deflist.</p>"

  (defund signed-byte-listp (n x)
    (if (atom x)
        (null x)
      (and (signed-byte-p n (car x))
           (signed-byte-listp n (cdr x)))))

  (defthm signed-byte-listp-when-atom
    (implies (atom x)
             (equal (signed-byte-listp n x)
                    (not x)))
    :hints(("Goal" :in-theory (enable signed-byte-listp))))

  (defthm signed-byte-listp-of-cons
    (equal (signed-byte-listp n (cons a x))
           (and (signed-byte-p n a)
                (signed-byte-listp n x)))
    :hints(("Goal" :in-theory (enable signed-byte-listp))))

  (defthm true-listp-when-signed-byte-listp
    (implies (signed-byte-listp width x)
             (true-listp x))
    :hints(("Goal" :induct (len x)))))

