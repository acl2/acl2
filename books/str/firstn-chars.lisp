; ACL2 String Library
; Copyright (C) 2009 Centaur Technology
; Contact: jared@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "STR")
(include-book "doc")
(local (include-book "arithmetic"))
(local (include-book "unicode/take" :dir :system))

(defund firstn-chars-aux (x n acc)
  (declare (xargs :guard (and (stringp x)
                              (natp n)
                              (< n (length x))))
           (type string x)
           (type integer n))
  (if (mbe :logic (zp n)
           :exec (= n 0))
      (cons (char x 0) acc)
    (firstn-chars-aux x 
                      (- n 1)
                      (cons (char x n) acc))))

(defund firstn-chars (n x)

  ":Doc-Section Str 
  Efficient way to take leading characters from a string ~/
 
  This function is logically equal to 
  ~bv[]
    (take (min n (length x)) (coerce x 'list)),
  ~ev[]
  but is implemented more efficiently via ~c[char]. ~/ "

  (declare (xargs :guard (and (stringp x)
                              (natp n))
                  :verify-guards nil)
           (type string x))

  (mbe :logic 
       (take (min n (length x)) (coerce x 'list))
       :exec
       (let ((n (min n (length x))))
         (if (= n 0)
             nil
           (firstn-chars-aux x (- n 1) nil)))))

(local (defthm lemma
         (implies (and (stringp x)
                       (natp n)
                       (< n (length x)))
                  (equal (firstn-chars-aux x n acc)
                         (append (take (+ n 1) (coerce x 'list))
                                 acc)))
         :hints(("Goal" :in-theory (enable firstn-chars-aux)))))

(verify-guards firstn-chars)

(defthm character-listp-of-firstn-chars
  (implies (force (stringp x))
           (character-listp (firstn-chars n x)))
  :hints(("Goal" :in-theory (enable firstn-chars))))



(defund append-firstn-chars (n x y)
  (declare (xargs :guard (and (natp n)
                              (stringp x))
                  :verify-guards nil))
  (mbe :logic 
       (append (firstn-chars n x) y)
       :exec
       (let ((n (min n (length x))))
         (if (= n 0)
             y
           (firstn-chars-aux x (- n 1) y)))))

(verify-guards append-firstn-chars
               :hints(("Goal" 
                       :in-theory (enable firstn-chars))))

(defthm character-listp-of-append-firstn-chars
  (implies (and (force (stringp x))
                (force (character-listp y)))
           (character-listp (append-firstn-chars n x y)))
  :hints(("Goal" :in-theory (enable append-firstn-chars))))




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