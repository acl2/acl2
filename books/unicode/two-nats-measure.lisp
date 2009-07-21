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

(local (include-book "ordinals/ordinals" :dir :system))

(defund two-nats-measure (a b)
  (declare (xargs :guard (and (natp a)
                              (natp b))))
  (make-ord 2 
            (+ 1 (nfix a))
            (make-ord 1 (+ 1 (nfix b)) 0)))

(in-theory (disable (:executable-counterpart two-nats-measure)))

(defthm o-p-of-two-nats-measure
  (equal (o-p (two-nats-measure a b))
         t)
  :hints(("Goal" :in-theory (enable two-nats-measure))))

(defthm o<-of-two-nats-measure
  (equal (o< (two-nats-measure a b)
             (two-nats-measure c d))
         (or (< (nfix a) (nfix c))
             (and (equal (nfix a) (nfix c))
                  (< (nfix b) (nfix d)))))
  :hints(("Goal" :in-theory (enable two-nats-measure))))

