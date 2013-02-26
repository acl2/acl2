; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "eqv")
(local (include-book "arithmetic"))
(local (include-book "std/lists/take" :dir :system))

(defsection firstn-chars
  :parents (str)
  :short "Efficient way to take leading characters from a string."

  :long "<p>@(call firstn-chars) is logically equal to:</p>

@({ (take (min n (length x)) (coerce x 'list)) })

<p>But it is implemented more efficiently, via @(see char).</p>"

  (defund firstn-chars-aux (x n acc)
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (< n (length x))))
             (type string x)
             (type integer n))
    (if (zp n)
        (cons (char x 0) acc)
      (firstn-chars-aux x
                        (- n 1)
                        (cons (char x n) acc))))

  (defund firstn-chars (n x)
    (declare (xargs :guard (and (stringp x)
                                (natp n))
                    :verify-guards nil)
             (type string x))
    (mbe :logic
         (take (min n (length x)) (coerce x 'list))
         :exec
         (let ((n (min n (length x))))
           (if (zp n)
               nil
             (firstn-chars-aux x (- n 1) nil)))))

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
    (implies (force (stringp x))
             (character-listp (firstn-chars n x)))))



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
    (implies (and (force (stringp x))
                  (force (character-listp y)))
             (character-listp (append-firstn-chars n x y)))))


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
