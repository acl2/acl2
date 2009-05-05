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
(set-state-ok t)

(defund nthcdr-bytes (n channel state)
  (declare (xargs :guard (and (natp n)
                              (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))))
  (if (zp n)
      state
    (mv-let (byte state)
            (read-byte$ channel state)
            (declare (ignore byte))
            (nthcdr-bytes (+ n -1) channel state))))

(defthm state-p1-of-nthcdr-bytes
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (state-p1 (nthcdr-bytes n channel state)))
  :hints(("Goal" :in-theory (enable nthcdr-bytes))))

(defthm open-input-channel-p1-of-nthcdr-bytes
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (open-input-channel-p1 channel :byte (nthcdr-bytes n channel state)))
  :hints(("Goal" :in-theory (enable nthcdr-bytes))))

(defthm read-byte$-all-of-nthcdr-bytes
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (equal (car (read-byte$-all channel (nthcdr-bytes n channel state)))
                  (nthcdr n (car (read-byte$-all channel state)))))
  :hints(("Goal" 
          :in-theory (enable nthcdr-bytes nthcdr read-byte$-all)
          :induct (nthcdr-bytes n channel state))))

(defthm nthcdr-bytes-1
  (equal (nthcdr-bytes 1 channel state)
         (mv-nth 1 (read-byte$ channel state)))
  :hints(("Goal" 
          :in-theory (enable nthcdr-bytes)
          :expand ((nthcdr-bytes 1 channel state)))))

(defthm nthcdr-bytes-2
  (equal (nthcdr-bytes 2 channel state)
         (mv-nth 1 (read-byte$ channel
                               (mv-nth 1 (read-byte$ channel state)))))
  :hints(("Goal" :in-theory (enable nthcdr-bytes))))

(defthm nthcdr-bytes-3
  (equal (nthcdr-bytes 3 channel state)
         (mv-nth 1 (read-byte$ 
                    channel
                    (mv-nth 1 (read-byte$ 
                               channel
                               (mv-nth 1 (read-byte$ channel state)))))))
  :hints(("Goal" :in-theory (enable nthcdr-bytes))))

(defthm nthcdr-bytes-4
  (equal (nthcdr-bytes 4 channel state)
         (mv-nth 1 (read-byte$ 
                    channel
                    (mv-nth 1 (read-byte$ 
                               channel
                               (mv-nth 1 (read-byte$ 
                                          channel
                                          (mv-nth 1 (read-byte$ channel state)))))))))
  :hints(("Goal" :in-theory (enable nthcdr-bytes))))

(defthm nthcdr-bytes-measure-weak
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel)))
           (<= (file-measure channel (nthcdr-bytes n channel state))
               (file-measure channel state)))
  :rule-classes (:rewrite :linear)
  :hints(("Goal" :in-theory (enable nthcdr-bytes))))

(defthm nthcdr-bytes-measure-strong
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-byte$ channel state))
                (not (zp n)))
           (< (file-measure channel (nthcdr-bytes n channel state))
              (file-measure channel state)))
  :rule-classes (:rewrite :linear)
  :hints(("Goal" :in-theory (enable nthcdr-bytes))))
