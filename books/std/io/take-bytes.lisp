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
(include-book "read-byte")
(include-book "read-file-bytes")
(include-book "nthcdr-bytes")
(set-state-ok t)

(defund take-bytes (n channel state)
  (declare (xargs :guard (and (natp n)
                              (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))))
  (if (zp n)
      (mv nil state)
    (mv-let (a state)
            (read-byte$ channel state)
            (mv-let (x state)
                    (take-bytes (1- n) channel state)
                    (mv (cons a x) state)))))

(defthm state-p1-of-take-bytes
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (state-p1 (mv-nth 1 (take-bytes n channel state))))
  :hints(("Goal" :in-theory (enable take-bytes))))

(defthm open-input-channel-p1-of-take-bytes
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (open-input-channel-p1 channel :byte (mv-nth 1 (take-bytes n channel state))))
  :hints(("Goal" :in-theory (enable take-bytes))))

(defthm car-of-take-bytes
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (equal (mv-nth 0 (take-bytes n channel state))
                  (simpler-take n (mv-nth 0 (read-byte$-all channel state)))))
  :hints(("Goal"
          :in-theory (enable simpler-take take-bytes read-byte$-all)
          :induct (take-bytes n channel state))))

(defthm mv-nth1-of-take-bytes$
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (equal (mv-nth 1 (take-bytes n channel state))
                  (nthcdr-bytes n channel state)))
  :hints(("Goal" :in-theory (enable take-bytes nthcdr-bytes))))