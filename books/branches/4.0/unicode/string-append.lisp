;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")

(local (include-book "append"))
(local (include-book "coerce"))

(defthm equal-of-string-appends-one
  (implies (and (stringp x)
                (stringp y1)
                (stringp y2))
           (equal (equal (string-append x y1)
                         (string-append x y2))
                  (equal y1 y2))))

(defthm equal-of-string-appends-two
  (implies (and (stringp x1)
                (stringp x2)
                (stringp y))
           (equal (equal (string-append x1 y)
                         (string-append x2 y))
                  (equal x1 x2))))
