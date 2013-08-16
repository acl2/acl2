; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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
(include-book "ieqv")
(local (include-book "arithmetic"))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/equiv" :dir :system))
(local (in-theory (disable acl2::take-redefinition)))

(defsection firstn-chars
  :parents (str)
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
         (take (min n (len (explode x))) (explode x))
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

(defthm firstn-chars-consp

; I (David Rager) needed this lemma in one of my uses of firstn-chars, so I've
; placed it here in case others find it useful.  I think it will only trigger
; when the term one is trying to prove is (consp (firstn-chars 1 lexeme)) so it
; should be pretty cheap.  Please correct me if I've got it wrong.

  (implies (and (stringp lexeme)
                (< 0 (length lexeme)))
           (consp (firstn-chars 1 lexeme)))
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
