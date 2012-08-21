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
(include-book "file-measure")
(include-book "unsigned-byte-listp")
(local (include-book "open-input-channel"))
(local (include-book "close-input-channel"))
(local (include-book "read-byte"))
(local (include-book "tools/mv-nth" :dir :system))
(set-state-ok t)

(defun tr-read-byte$-all (channel state acc)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state)
                              (true-listp acc))
                  :measure (file-measure channel state)))
  (if (mbt (state-p state))
      (mv-let (byte state)
              (read-byte$ channel state)
              (if (eq byte nil)
                  (mv (reverse acc) state)
                (tr-read-byte$-all channel state (cons byte acc))))
    (mv nil state)))

(defun read-byte$-all (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :measure (file-measure channel state)
                  :verify-guards nil))
  (mbe
   :logic (if (state-p state)
              (mv-let (byte state)
                      (read-byte$ channel state)
                      (if (null byte)
                          (mv nil state)
                        (mv-let (rest state)
                                (read-byte$-all channel state)
                                (mv (cons byte rest) state))))
            (mv nil state))
   :exec (tr-read-byte$-all channel state nil)))

(defun read-file-bytes (filename state)
  (declare (xargs :guard (and (state-p state)
                              (stringp filename))
                  :verify-guards nil))
  (mv-let (channel state)
          (open-input-channel filename :byte state)
          (if channel
              (mv-let (data state)
                      (read-byte$-all channel state)
                      (let ((state (close-input-channel channel state)))
                        (mv data state)))
            (mv "Error opening file." state))))


(encapsulate
 ()
 (local (defthm lemma-decompose-impl
          (equal (tr-read-byte$-all channel state acc)
                 (list (mv-nth 0 (tr-read-byte$-all channel state acc))
                       (mv-nth 1 (tr-read-byte$-all channel state acc))))
          :rule-classes nil))

 (local (defthm lemma-decompose-spec
          (equal (read-byte$-all channel state)
                 (list (mv-nth 0 (read-byte$-all channel state))
                       (mv-nth 1 (read-byte$-all channel state))))
          :rule-classes nil))

 (local (defthm lemma-data-equiv
          (implies (and (state-p1 state)
                        (symbolp channel)
                        (open-input-channel-p1 channel :byte state)
                        (true-listp acc))
                   (equal (mv-nth 0 (tr-read-byte$-all channel state acc))
                          (revappend acc (mv-nth 0 (read-byte$-all channel state)))))))

 (local (defthm lemma-state-equiv
          (equal (mv-nth 1 (tr-read-byte$-all channel state acc))
                 (mv-nth 1 (read-byte$-all channel state)))))

 (local (defthm lemma-equiv
          (implies (and (state-p1 state)
                        (symbolp channel)
                        (open-input-channel-p1 channel :byte state))
                   (equal (tr-read-byte$-all channel state nil)
                          (read-byte$-all channel state)))
          :hints(("Goal" :in-theory (disable tr-read-byte$-all read-byte$-all)
                  :use ((:instance lemma-decompose-impl (acc nil))
                        (:instance lemma-decompose-spec)
                        (:instance lemma-data-equiv (acc nil)))))))

 (verify-guards read-byte$-all))

(defthm state-p1-of-read-byte$-all
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (state-p1 (mv-nth 1 (read-byte$-all channel state)))))

(defthm open-input-channel-p1-of-read-byte$-all
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (open-input-channel-p1 channel :byte
                                  (mv-nth 1 (read-byte$-all channel state)))))

(defthm integer-listp-of-read-byte$-all
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (integer-listp (mv-nth 0 (read-byte$-all channel state)))))

(defthm unsigned-byte-listp-of-read-byte$-all
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (unsigned-byte-listp 8 (mv-nth 0 (read-byte$-all channel state))))
  :hints(("Goal" :in-theory (enable read-byte$-all))))

(defthm true-listp-of-read-byte$-all
  (true-listp (mv-nth 0 (read-byte$-all channel state)))
  :rule-classes (:rewrite :type-prescription)
  :hints(("Goal" :in-theory (enable read-byte$-all))))

(verify-guards read-file-bytes)

(defthm state-p1-of-read-file-bytes
  (implies (and (force (state-p1 state))
                (force (stringp filename)))
           (state-p1 (mv-nth 1 (read-file-bytes filename state)))))

(defthm integer-listp-of-read-file-bytes
  (implies (and (not (stringp (mv-nth 0 (read-file-bytes filename state))))
                (force (state-p1 state))
                (force (stringp filename)))
           (integer-listp (mv-nth 0 (read-file-bytes filename state)))))

(defthm unsigned-byte-listp-of-read-file-bytes
  (implies (and (not (stringp (mv-nth 0 (read-file-bytes filename state))))
                (force (state-p1 state))
                (force (stringp filename)))
           (unsigned-byte-listp 8 (mv-nth 0 (read-file-bytes filename state))))
  :hints(("Goal" :in-theory (enable read-file-bytes))))

(defthm true-listp-of-read-file-bytes
  (implies (and (not (stringp (mv-nth 0 (read-file-bytes filename state))))
                (force (state-p1 state))
                (force (stringp filename)))
           (true-listp (mv-nth 0 (read-file-bytes filename state))))
  :hints(("Goal" :in-theory (enable read-file-bytes))))

(in-theory (disable tr-read-byte$-all read-byte$-all read-file-bytes))

