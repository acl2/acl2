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
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "update-state"))
(local (include-book "open-input-channels"))

;; We introduce the file-measure function and show that it is reduced by the
;; read-byte$, read-char$, and read-object functions.  This is useful for
;; introducing recursive functions based on reading a file.

(defun file-measure (channel state-state)
  (declare (xargs :guard (and (symbolp channel)
                              (state-p1 state-state))))
  (len (cddr (assoc-equal channel (open-input-channels state-state)))))

(local (defthm assoc-eq-is-assoc-equal
         (equal (assoc-eq a x)
                (assoc-equal a x))))

(defthm read-byte$-measure-weak
  (implies (state-p1 state)
           (<= (file-measure channel (mv-nth 1 (read-byte$ channel state)))
               (file-measure channel state)))
  :hints(("Goal" :in-theory (disable statep-functions)))
  :rule-classes ((:rewrite) (:linear)))

(defthm read-byte$-measure-strong
  (implies (and (state-p1 state)
                (mv-nth 0 (read-byte$ channel state)))
           (< (file-measure channel (mv-nth 1 (read-byte$ channel state)))
              (file-measure channel state)))
  :hints(("Goal" :in-theory (disable statep-functions)))
  :rule-classes ((:rewrite) (:linear)))

(defthm read-char$-measure-weak
  (implies (state-p1 state)
           (<= (file-measure channel (mv-nth 1 (read-char$ channel state)))
               (file-measure channel state)))
  :hints(("Goal" :in-theory (disable statep-functions)))
  :rule-classes ((:rewrite) (:linear)))

(defthm read-char$-measure-strong
  (implies (and (state-p1 state)
                (mv-nth 0 (read-char$ channel state)))
           (< (file-measure channel (mv-nth 1 (read-char$ channel state)))
              (file-measure channel state)))
  :hints(("Goal" :in-theory (disable statep-functions)))
  :rule-classes ((:rewrite) (:linear)))

(defthm read-object-measure-weak
  (implies (state-p1 state)
           (<= (file-measure channel (mv-nth 2 (read-object channel state)))
               (file-measure channel state)))
  :hints(("Goal" :in-theory (disable statep-functions)))
  :rule-classes ((:rewrite) (:linear)))

(encapsulate
 ()
 (local (defthm lemma
          (implies (state-p1 state)
                   (equal (consp (cddr (assoc-equal channel (open-input-channels state))))
                          (if (cddr (assoc-equal channel (open-input-channels state)))
                              t
                            nil)))
          :hints(("Goal"
                  :in-theory (disable open-channels-assoc
                                      open-channels-p
                                      open-input-channels)
                  :use ((:instance open-channels-assoc
                                   (x (open-input-channels state))))))))

 (defthm read-object-measure-strong
   (implies (and (state-p1 state)
                 (not (mv-nth 0 (read-object channel state))))
            (< (file-measure channel (mv-nth 2 (read-object channel state)))
               (file-measure channel state)))
   :hints(("Goal" :in-theory (disable statep-functions)))
   :rule-classes ((:rewrite) (:linear))))

(in-theory (disable file-measure))
