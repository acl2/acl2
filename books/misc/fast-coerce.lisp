; fast-coerce.lisp
; Copyright (C) 2008 by Jared Davis <jared@cs.utexas.edu>
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

(in-package "ACL2")

; This is a faster version of coerce.  It is the same as ACL2's regular coerce
; when converting character lists into strings.  It is much faster than ACL2's
; coerce when converting strings into character lists.
;
; On my machine, using CCL, I have:
;
;  - Regular : 36 seconds, 4.6 GB allocated
;  - Fast    : 4  seconds, 2.0 GB allocated
;
; For the following test:
;
;   (time$ (loop for i fixnum from 1 to 10000000 do 
;                (coerce "Hello, World!" 'list)))

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))

(defund fast-coerce-aux1 (x i len)
  (declare (xargs :guard (and (stringp x)
                              (natp i)
                              (natp len)
                              (= len (length x))
                              (<= i len))
                  :guard-debug t
                  :measure (nfix (- (nfix len) (nfix i))))
           ;; BOZO add (type string x)
           (type (signed-byte 30) i)
           (type (signed-byte 30) len))
  (if (mbe :logic (zp (- (nfix len) (nfix i)))
           :exec (= (the-fixnum i)
                    (the-fixnum len)))
      nil
    (cons (the character 
               (char (the string x)
                     (the (signed-byte 30) i)))
          (fast-coerce-aux1 x 
                            (the-fixnum 
                             (+ (the-fixnum 1)
                                (mbe :logic (nfix i) 
                                     :exec (the-fixnum i))))
                            (the-fixnum len)))))

(defund fast-coerce-aux2 (x i len)
  (declare (xargs :guard (and (stringp x)
                              (natp i)
                              (natp len)
                              (= len (length x))
                              (<= i len))
                  :guard-debug t
                  :measure (nfix (- (nfix len) (nfix i))))
           ;; BOZO add (type string x)
           (type integer i)
           (type integer len))
  (if (mbe :logic (zp (- (nfix len) (nfix i)))
           :exec (= (the integer i) (the integer len)))
      nil
    (cons (char x i)
          (fast-coerce-aux2 x 
                            (+ (the integer 1)
                               (mbe :logic (nfix i) 
                                    :exec (the integer i)))
                            len))))

(local (defthm lemma
          (implies (and (natp i) 
                        (< i (len x)))
                   (equal (cons (nth i x)
                                (cdr (nthcdr i x)))
                          (nthcdr i x)))))

(local (defthm lemma2
         (equal (nthcdr i (cdr x))
                (cdr (nthcdr i x)))))

(local (defthm lemma3
         (implies (and (stringp x)
                       (natp i)
                       (<= i (length x)))
                  (equal (fast-coerce-aux2 x i (len (coerce x 'list)))
                         (nthcdr i (coerce x 'list))))
         :hints(("Goal"
                 :in-theory (enable fast-coerce-aux2)))))

(local (defthm fast-coerce-aux2-equiv
         (equal (fast-coerce-aux1 x i len)
                (fast-coerce-aux2 x i len))
         :hints(("Goal" :in-theory (enable fast-coerce-aux2
                                           fast-coerce-aux1)))))

(defun fast-coerce (x y)
  (declare (xargs :guard (case y
                           (list (stringp x))
                           (string (character-listp x)))))
  (mbe :logic (coerce x y)
       :exec (if (eq y 'list)
                 (let ((length (length x)))
                   (if (< (the integer length) 
                          (the integer 536870912))
                       (fast-coerce-aux1 (the string x) 
                                         (the (signed-byte 30) 0)
                                         (the (signed-byte 30) length))
                     (fast-coerce-aux2 (the string x) 
                                       (the integer 0)
                                       (the integer length))))
               (coerce x y))))

