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
(set-state-ok t)

(include-book "file-measure")
(local (include-book "open-input-channel"))
(local (include-book "read-char"))
(local (include-book "close-input-channel"))

(defun tr-read-char$-all (channel state acc)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :character state)
                              (true-listp acc))
                  :measure (file-measure channel state)))
  (if (mbt (state-p state))
      (mv-let (char state)
              (read-char$ channel state)
              (if (eq char nil)
                  (mv (reverse acc) state)
                (tr-read-char$-all channel state (cons char acc))))
    (mv nil state)))
                 
(defun read-char$-all (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :character state))
                  :measure (file-measure channel state)
                  :verify-guards nil))
  (mbe :logic (if (state-p state)
                  (mv-let (char state)
                          (read-char$ channel state)
                          (if (null char)
                              (mv nil state)
                            (mv-let (rest state)
                                    (read-char$-all channel state)
                                    (mv (cons char rest) state))))
                (mv nil state))
       :exec (tr-read-char$-all channel state nil)))

(defun read-file-characters (filename state)
  (declare (xargs :guard (and (state-p state)
                              (stringp filename))
                  :verify-guards nil))
  (mv-let (channel state)
          (open-input-channel filename :character state)
          (if channel
              (mv-let (data state)
                      (read-char$-all channel state)
                      (let ((state (close-input-channel channel state)))
                        (mv data state)))
            (mv "Error opening file." state))))

(local (defthm lemma-decompose-impl
         (equal (tr-read-char$-all channel state acc)
                (list (car (tr-read-char$-all channel state acc))
                      (mv-nth 1 (tr-read-char$-all channel state acc))))
         :rule-classes nil))
      
(local (defthm lemma-decompose-spec
         (equal (read-char$-all channel state)
                (list (car (read-char$-all channel state))
                      (mv-nth 1 (read-char$-all channel state))))
         :rule-classes nil))

(local (defthm lemma-data-equiv
         (implies (and (state-p1 state)
                       (symbolp channel)
                       (open-input-channel-p1 channel :character state)
                       (true-listp acc))
                  (equal (car (tr-read-char$-all channel state acc))
                         (revappend acc (car (read-char$-all channel state)))))))

(local (defthm lemma-state-equiv
         (equal (mv-nth 1 (tr-read-char$-all channel state acc))
                (mv-nth 1 (read-char$-all channel state)))))
  
(local (defthm lemma-equiv
         (implies (and (state-p1 state)
                       (symbolp channel)
                       (open-input-channel-p1 channel :character state))
                  (equal (tr-read-char$-all channel state nil)
                         (read-char$-all channel state)))
         :hints(("Goal" :in-theory (disable tr-read-char$-all read-char$-all)
                 :use ((:instance lemma-decompose-impl (acc nil))
                       (:instance lemma-decompose-spec)
                       (:instance lemma-data-equiv (acc nil)))))))

(verify-guards read-char$-all)

(defthm read-char$-all-preserves-state
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :character state)))
           (state-p1 (mv-nth 1 (read-char$-all channel state)))))

(defthm read-char$-all-preserves-open-input-channel-p1
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :character state)))
           (open-input-channel-p1 channel :character
                                  (mv-nth 1 (read-char$-all channel state)))))

(defthm read-char$-all-character-listp
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :character state)))
           (character-listp (car (read-char$-all channel state)))))

(verify-guards read-file-characters)

(defthm read-file-characters-preserves-state
  (implies (and (force (state-p1 state))
                (force (stringp filename)))
           (state-p1 (mv-nth 1 (read-file-characters filename state)))))

(defthm read-file-characters-error-or-character-list
  (implies (and (force (state-p1 state))
                (force (stringp filename))
                (not (stringp (car (read-file-characters filename state)))))
           (character-listp (car (read-file-characters filename state)))))

(in-theory (disable tr-read-char$-all read-char$-all read-file-characters))

