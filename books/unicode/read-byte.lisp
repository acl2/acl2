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
;; (local (include-book "unsigned-byte-listp"))
;; (local (include-book "signed-byte-listp"))

;; ; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;; ; (local (defthm assoc-eq-is-assoc-equal
;; ;          (equal (assoc-eq a x)
;; ;                 (assoc-equal a x))))

;; (local (defthm car-of-assoc-equal-when-assoc-equal
;;          (implies (assoc-equal a x)
;;                   (equal (car (assoc-equal a x))
;;                          a))))

;; (defthm state-p1-of-read-byte$
;;   (implies (and (force (state-p1 state))
;;                 (force (open-input-channel-p1 channel :byte state))
;;                 (force (symbolp channel)))
;;            (state-p1 (mv-nth 1 (read-byte$ channel state))))
;;   :hints(("Goal" :in-theory (disable statep-functions)
;;           :use ((:instance state-p1
;;                            (x state))
;;                 (:instance state-p1
;;                            (x (mv-nth 1 (read-byte$ channel state))))))))

;; (defthm open-input-channel-p1-of-read-byte$
;;   (implies (and (force (state-p1 state))
;;                 (force (open-input-channel-p1 channel :byte state))
;;                 (force (symbolp channel)))
;;            (open-input-channel-p1 channel
;;                                   :byte
;;                                   (mv-nth 1 (read-byte$ channel state))))
;;   :hints(("Goal" :in-theory (disable statep-functions)
;;           :use ((:instance state-p1
;;                            (x state))
;;                 (:instance state-p1
;;                            (x (mv-nth 1 (read-byte$ channel state))))))))

;; (local (defthmd car-typed-io-list-byte
;;   (implies (and (typed-io-listp x :byte)
;;                 (consp x))
;;            (and (integerp (car x))
;;                 (<= 0 (car x))
;;                 (< (car x) 256)))))

;; (defthm integerp-of-read-byte$
;;   (implies (and (mv-nth 0 (read-byte$ channel state))
;;                 (force (state-p1 state))
;;                 (force (open-input-channel-p1 channel :byte state)))
;;            (integerp (mv-nth 0 (read-byte$ channel state))))
;;   :hints(("Goal" :in-theory (disable open-input-channel-p1
;;                                      open-input-channels)
;;           :use (:instance car-typed-io-list-byte
;;                           (x (cddr (assoc-equal
;;                                     channel
;;                                     (open-input-channels state))))))))

;; (defthm range-of-read-byte$
;;   (implies (and (mv-nth 0 (read-byte$ channel state))
;;                 (force (state-p1 state))
;;                 (force (open-input-channel-p1 channel :byte state)))
;;            (and (<= 0 (mv-nth 0 (read-byte$ channel state)))
;;                 (< (mv-nth 0 (read-byte$ channel state)) 256)
;;                 (< (mv-nth 0 (read-byte$ channel state)) (expt 2 8))))
;;   :rule-classes :linear
;;   :hints(("Goal" :in-theory (disable open-input-channel-p1
;;                                      open-input-channels)
;;           :use (:instance car-typed-io-list-byte
;;                           (x (cddr (assoc-equal
;;                                     channel
;;                                     (open-input-channels state))))))))

;; (defthm unsigned-byte-p-of-read-byte$
;;   (implies (and (mv-nth 0 (read-byte$ channel state))
;;                 (<= 8 size)
;;                 (integerp size)
;;                 (force (state-p1 state))
;;                 (force (open-input-channel-p1 channel :byte state)))
;;            (unsigned-byte-p size (mv-nth 0 (read-byte$ channel state))))
;;   :hints(("Goal"
;;           :in-theory (e/d (unsigned-byte-p) (read-byte$))
;;           :use (:instance unsigned-byte-promote
;;                           (size1 8)
;;                           (size2 size)
;;                           (x (mv-nth 0 (read-byte$ channel state)))))))

;; (defthm signed-byte-p-of-read-byte$
;;   (implies (and (mv-nth 0 (read-byte$ channel state))
;;                 (<= 9 size)
;;                 (integerp size)
;;                 (force (state-p1 state))
;;                 (force (open-input-channel-p1 channel :byte state)))
;;            (signed-byte-p size (mv-nth 0 (read-byte$ channel state))))
;;   :hints(("Goal"
;;           :in-theory (disable read-byte$)
;;           :use (:instance unsigned-to-signed-promote
;;                           (size1 8)
;;                           (size2 size)
;;                           (x (mv-nth 0 (read-byte$ channel state)))))))


;; (encapsulate
;;  ()

;;  (local (defthm lemma
;;           (implies (and (typed-io-listp x :byte)
;;                         (not (car x)))
;;                    (not (cadr x)))))

;;  (defthm car-of-read-byte$-after-eof
;;    (implies (and (not (mv-nth 0 (read-byte$ channel state)))
;;                  (force (state-p state))
;;                  (force (symbolp channel))
;;                  (force (open-input-channel-p channel :byte state)))
;;             (not (mv-nth 0 (read-byte$ channel (mv-nth 1 (read-byte$ channel state))))))
;;    :hints(("Goal" :in-theory (e/d (read-byte$)
;;                                   (statep-functions))))))


;; (encapsulate
;;  ()

;;  (local (defthm lemma
;;           (equal (equal a (cons x y))
;;                  (and (consp a)
;;                       (equal (car a) x)
;;                       (equal (cdr a) y)))))

;;  (local (defthm lemma2
;;           (implies (and (open-channel1 foo)
;;                         (equal (cadar foo) :byte)
;;                         (not (cadr foo)))
;;                    (equal (equal (cdr foo) (cddr foo))
;;                           t))))

;;  (defthm mv-nth-of-read-byte$-when-eof
;;    (implies (and (not (mv-nth 0 (read-byte$ channel state)))
;;                  (state-p state)
;;                  (symbolp channel)
;;                  (open-input-channel-p channel :byte state))
;;             (equal (mv-nth 1 (read-byte$ channel state))
;;                    state))
;;    :hints(("Goal" :in-theory (e/d (read-byte$)
;;                                   (statep-functions
;;                                    open-channel1
;;                                    open-channels-assoc))
;;            :use ((:instance open-channels-assoc
;;                             (x (open-input-channels state))))))))


;; (in-theory (disable state-p1 open-input-channel-p1 read-byte$))



