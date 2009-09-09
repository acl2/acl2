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

(defund rpadchars (x len)
  (declare (xargs :guard (and (character-listp x)
                              (natp len))
                  :guard-hints (("Goal" :in-theory (enable acl2::repeat))))
           (type integer len))
  (mbe :logic 
       (append x (make-list (nfix (- (nfix len) (len x)))
                            :initial-element #\Space))
       :exec 
       (let* ((x-len (length (the list x)))
              (diff  (- len x-len)))
         (if (> diff 0)
             (append x (make-list diff :initial-element #\Space))
           x))))

(defthm character-listp-of-rpadchars
  (implies (force (character-listp x))
           (character-listp (rpadchars x len)))
  :hints(("Goal" :in-theory (enable rpadchars))))

(defthm len-of-rpadchars
  (equal (len (rpadchars x len))
         (max (len x) (nfix len)))
  :hints(("Goal" :in-theory (enable rpadchars))))



(defund rpadstr (x len)
  (declare (xargs :guard (and (stringp x)
                              (natp len)))
           (type string x)
           (type integer len))
  (coerce (rpadchars (coerce x 'list) len) 'string))

(defthm stringp-of-rpadstr
  (stringp (rpadstr x len))
  :rule-classes :type-prescription )

(defthm len-of-coerce-of-rpadstr
  (implies (force (stringp x))
           (equal (len (coerce (rpadstr x len) 'list))
                  (max (length x)
                       (nfix len))))
  :hints(("Goal" :in-theory (enable rpadstr))))



(defund lpadchars-aux (x n)
  (declare (xargs :guard (and (character-listp x)
                              (natp n))
                  :guard-hints (("Goal" :in-theory (enable lpadchars-aux acl2::repeat))))
           (type integer n))
  (mbe :logic 
       (append (make-list n :initial-element #\Space)
               x)
       :exec
       (if (= n 0)
           x
         (lpadchars-aux (cons #\Space x) (- n 1)))))

(defund lpadchars (x len)
  (declare (xargs :guard (and (character-listp x)
                              (natp len))
                  :guard-hints (("Goal" :in-theory (enable lpadchars-aux))))
           (type integer len))
  (mbe :logic
       (append (make-list (nfix (- (nfix len) (len x)))
                          :initial-element #\Space)
               x)
       :exec
       (let* ((x-len (length x))
              (diff  (- len x-len)))
         (if (< 0 diff)
             (lpadchars-aux x diff)
           x))))

(defthm character-listp-of-lpadchars
  (implies (force (character-listp x))
           (character-listp (lpadchars x len)))
  :hints(("Goal" :in-theory (enable lpadchars))))

(defthm len-of-lpadchars
  (equal (len (lpadchars x len))
         (max (len x) (nfix len)))
  :hints(("Goal" :in-theory (enable lpadchars))))




(defund lpadstr (x len)
  (declare (xargs :guard (and (stringp x)
                              (natp len)))
           (type string x)
           (type integer len))
  (coerce (lpadchars (coerce x 'list) len) 'string))

(defthm stringp-of-lpadstr
  (stringp (lpadstr x len))
  :rule-classes :type-prescription)

(defthm len-of-coerce-of-lpadstr
  (implies (force (stringp x))
           (equal (len (coerce (lpadstr x len) 'list))
                  (max (length x)
                       (nfix len))))
  :hints(("Goal" :in-theory (enable lpadstr))))