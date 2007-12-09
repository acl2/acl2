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

(local (defthm coerce-string-lemma
         (implies (and (character-listp x)
                       (character-listp y)
                       (not (equal x y)))
                  (not (equal (coerce x 'string)
                              (coerce y 'string))))
         :hints(("Goal" :use ((:instance coerce-inverse-1 (x x))
                              (:instance coerce-inverse-1 (x y)))))))

(defthm equal-of-coerce-strings
  (implies (and (character-listp x)
                (character-listp y))
           (equal (equal (coerce x 'string)
                         (coerce y 'string))
                  (equal x y))))

(local (defthm coerce-list-lemma
         (implies (and (stringp x)
                       (stringp y)
                       (not (equal x y)))
                  (not (equal (coerce x 'list)
                              (coerce y 'list))))
         :hints(("Goal" :use ((:instance coerce-inverse-2 (x x))
                              (:instance coerce-inverse-2 (x y)))))))

(defthm equal-of-coerce-lists
  (implies (and (stringp x)
                (stringp y))
           (equal (equal (coerce x 'list)
                         (coerce y 'list))
                  (equal x y))))

(defthm character-listp-of-coerce-list
  (character-listp (coerce x 'list)))