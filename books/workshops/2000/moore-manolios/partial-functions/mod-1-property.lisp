;  Copyright (C) 2000 Panagiotis Manolios and J Strother Moore

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu, moore@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

; (certify-book "mod-1-property")

(in-package "ACL2")

(local (include-book "../../../../ihs/quotient-remainder-lemmas"))
(local (include-book "../../../../arithmetic/top-with-meta"))

(defthm floor-int-1
  (implies (integerp x)
           (equal (floor x 1) x)))

(defthm floor-x-1
  (implies (rationalp x)
           (equal (floor (- x 1) 1)
                  (- (floor x 1) 1)))
  :hints (("Goal" :in-theory (disable floor))))

(defthm mod-1-property
   (implies (and (rationalp x)
                 (not (integerp x)))
            (and (< 0 (mod x 1))
                 (< (mod x 1) 1)))
   :rule-classes nil)
