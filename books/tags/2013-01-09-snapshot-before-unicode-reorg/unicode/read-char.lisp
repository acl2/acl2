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
(include-book "system/io" :dir :system)

;; (local (include-book "tools/mv-nth" :dir :system))
;; (local (include-book "update-state"))
;; (local (include-book "open-input-channels"))

;; ; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;; ; (local (defthm assoc-eq-is-assoc-equal
;; ;          (equal (assoc-eq a x)
;; ;                 (assoc-equal a x))))

;; (defthm read-char$-state
;;   (implies (and (force (state-p1 state))
;;                 (force (open-input-channel-p1 channel :character state))
;;                 (force (symbolp channel)))
;;            (state-p1 (mv-nth 1 (read-char$ channel state))))
;;   :hints(("Goal" :in-theory (disable statep-functions)
;;           :use ((:instance state-p1
;;                            (x state))
;;                 (:instance state-p1
;;                            (x (mv-nth 1 (read-char$ channel state))))))))

;; (defthm read-char$-open-input-channel-p1
;;   (implies (and (force (state-p1 state))
;;                 (force (open-input-channel-p1 channel :character state))
;;                 (force (symbolp channel)))
;;            (open-input-channel-p1 channel
;;                                   :character
;;                                   (mv-nth 1 (read-char$ channel state))))
;;   :hints(("Goal" :in-theory (disable statep-functions)
;;           :use ((:instance state-p1
;;                            (x state))
;;                 (:instance state-p1
;;                            (x (mv-nth 1 (read-char$ channel state))))))))

;; (local (defthmd car-typed-io-list-char
;;   (implies (and (typed-io-listp x :character)
;;                 (consp x))
;;            (characterp (car x)))))

;; (defthm read-char$-character
;;   (implies (and (mv-nth 0 (read-char$ channel state))
;;                 (force (state-p1 state))
;;                 (force (open-input-channel-p1 channel :character state)))
;;            (characterp (mv-nth 0 (read-char$ channel state))))
;;   :hints(("Goal" :in-theory (disable open-input-channel-p1
;;                                      open-input-channels)
;;           :use (:instance car-typed-io-list-char
;;                           (x (cddr (assoc-equal
;;                                     channel
;;                                     (open-input-channels state))))))))

;; (encapsulate
;;  ()

;;  (local (defthm lemma
;;           (implies (and (typed-io-listp x :character)
;;                         (not (car x)))
;;                    (not (cadr x)))))

;;  (defthm read-char$-after-eof
;;    (implies (and (not (mv-nth 0 (read-char$ channel state)))
;;                  (force (state-p state))
;;                  (force (symbolp channel))
;;                  (force (open-input-channel-p channel :character state)))
;;             (not (mv-nth 0 (read-char$ channel (mv-nth 1 (read-byte$ channel state))))))
;;    :hints(("Goal" :in-theory (e/d (read-char$)
;;                                   (statep-functions))))))


;; (in-theory (disable state-p1 open-input-channel-p1 read-char$))
