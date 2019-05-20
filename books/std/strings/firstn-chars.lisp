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
(include-book "ieqv")
(local (include-book "arithmetic"))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/equiv" :dir :system))
(local (in-theory (disable acl2::take)))

(defsection firstn-chars
  :parents (substrings)
  :short "Efficient way to take leading characters from a string."

  :long "<p>@(call firstn-chars) is logically equal to:</p>

@({ (take (min n (length x)) (explode x)) })

<p>But it is implemented more efficiently, via @(see char).</p>"

  (defund firstn-chars-aux (x n acc)
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (< n (length x))))
             (type string x)
             (type (integer 0 *) n))
    (if (zp n)
        (cons (char x 0) acc)
      (firstn-chars-aux x
                        (the (integer 0 *) (- n 1))
                        (cons (char x n) acc))))

  (defund firstn-chars (n x)
    (declare (xargs :guard (and (stringp x)
                                (natp n))
                    :verify-guards nil)
             (type string x)
             (type (integer 0 *) n))
    (mbe :logic
         (take (min (nfix n) (len (explode x))) (explode x))
         :exec
         (let ((n (min n (length x))))
           (if (zp n)
               nil
             (firstn-chars-aux x
                               (the (integer 0 *) (- n 1))
                               nil)))))

  (local (in-theory (enable firstn-chars-aux
                            firstn-chars)))

  (defthm firstn-chars-aux-removal
    (implies (and (stringp x)
                  (natp n)
                  (< n (length x)))
             (equal (firstn-chars-aux x n acc)
                    (append (take (+ n 1) (coerce x 'list))
                            acc))))

  (verify-guards firstn-chars)

  (defthm character-listp-of-firstn-chars
    (character-listp (firstn-chars n x)))

  (defcong streqv equal (firstn-chars n x) 2)
  (defcong istreqv icharlisteqv (firstn-chars n x) 2))


(defsection append-firstn-chars

  (defund append-firstn-chars (n x y)
    (declare (xargs :guard (and (natp n)
                                (stringp x))
                    :verify-guards nil))
    (mbe :logic
         (append (firstn-chars n x) y)
         :exec
         (let ((n (min n (length x))))
           (if (zp n)
               y
             (firstn-chars-aux x (- n 1) y)))))

  (local (in-theory (enable append-firstn-chars)))

  (verify-guards append-firstn-chars
    :hints(("Goal" :in-theory (enable firstn-chars))))

  (defthm character-listp-of-append-firstn-chars
    (equal (character-listp (append-firstn-chars n x y))
           (character-listp y)))

  (defcong streqv  equal        (append-firstn-chars n x y) 2)
  (defcong istreqv icharlisteqv (append-firstn-chars n x y) 2
    :hints(("Goal" :in-theory (disable istreqv))))

  (defcong list-equiv list-equiv (append-firstn-chars n x y) 3)
  (defcong charlisteqv charlisteqv (append-firstn-chars n x y) 3)
  (defcong icharlisteqv icharlisteqv (append-firstn-chars n x y) 3))

(defthm consp-of-firstn-chars
  ;; May be expensive, leaving enabled for now
  (equal (consp (firstn-chars n x))
         (and (posp n)
              (consp (explode x))))
  :hints (("Goal" :in-theory (enable firstn-chars length))))

(defthm consp-of-firstn-chars-of-1
  ;; Improved version of a lemma added by David Rager
  (equal (consp (firstn-chars 1 x))
         (consp (explode x)))
  :hints (("Goal" :in-theory (enable firstn-chars length))))


#||

:q

;; 6.82 seconds, 3.68 GB allocated
(time (loop for i fixnum from 1 to 10000000
            do
            (take 5 (coerce "Hello, World!" 'list))))

;; 2.00 seconds, 800 MB allocated
(time (loop for i fixnum from 1 to 10000000
            do
            (str::firstn-chars 5 "Hello, World!")))

||#
