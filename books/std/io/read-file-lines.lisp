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
;; (local (include-book "open-input-channel"))
;; (local (include-book "read-byte"))
;; (local (include-book "close-input-channel"))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(include-book "tools/bstar" :dir :system)
(set-state-ok t)

; BOZO this currently just looks for newlines.  It should probably be extended
; to also handle carriage return stuff or whatever is used on Windows, if that
; sort of thing hasn't been addressed in some other way.

(defund read-file-lines-aux (line lines channel state)
  ;; Line is a character list, the current line in reverse order
  ;; Lines are a string list, the previously read lines in reverse order
  ;; Channel is the BYTE channel we're reading from.
  (declare (xargs :guard (and (character-listp line)
                              (string-listp lines)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :stobjs state
                  :measure (file-measure channel state)))
  (b* (((unless (mbt (state-p state)))
        (mv nil state))
       ((mv byte state)
        (read-byte$ channel state))
       ((unless byte)
        (let ((lines (cons (reverse (coerce line 'string)) lines)))
          (mv lines state)))
       (char (code-char byte))
       (line (cons char line)))
      (if (eql char #\Newline)
          (let ((lines (cons (reverse (coerce line 'string)) lines)))
            (read-file-lines-aux nil lines channel state))
        (read-file-lines-aux line lines channel state))))

(defthm state-p1-of-read-file-lines-aux
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (state-p1 (mv-nth 1 (read-file-lines-aux line lines channel state))))
  :hints(("Goal" :in-theory (enable read-file-lines-aux))))

(defthm open-input-channel-p1-of-read-file-lines-aux
  (implies (and (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (open-input-channel-p1 channel :byte
                                  (mv-nth 1 (read-file-lines-aux line lines channel state))))
  :hints(("Goal" :in-theory (enable read-file-lines-aux))))

(defthm string-listp-of-read-file-lines-aux
  (implies (and (force (character-listp line))
                (force (string-listp lines))
                (force (state-p1 state))
                (force (symbolp channel))
                (force (open-input-channel-p1 channel :byte state)))
           (string-listp (mv-nth 0 (read-file-lines-aux line lines channel state))))
  :hints(("Goal" :in-theory (enable read-file-lines-aux))))

(defthm true-listp-of-read-file-lines-aux
  (implies (true-listp lines)
           (true-listp (mv-nth 0 (read-file-lines-aux line lines channel state))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable read-file-lines-aux))))




(defund read-file-lines (filename state)
  "Returns (MV ERRMSG/LINES STATE)"
  (declare (xargs :guard (stringp filename)
                  :stobjs state
                  :guard-debug t))
  (b* (((mv channel state)
        (open-input-channel filename :byte state))
       ((unless channel)
        (mv "Error opening file." state))
       ((mv data state)
        (read-file-lines-aux nil nil channel state))
       (state
        (close-input-channel channel state)))
      (mv (reverse data) state)))

(defthm state-p1-of-read-file-lines
  (implies (and (force (stringp filename))
                (force (state-p1 state)))
           (state-p1 (mv-nth 1 (read-file-lines filename state))))
  :hints(("Goal" :in-theory (enable read-file-lines))))

(local (defthm crock
         (implies (string-listp x)
                  (string-listp (rev x)))))

(defthm string-listp-of-read-file-lines
  (implies (and (force (stringp filename))
                (force (state-p state))
                (not (stringp (mv-nth 0 (read-file-lines filename state)))))
           (string-listp (mv-nth 0 (read-file-lines filename state))))
  :hints(("Goal" :in-theory (enable read-file-lines))))
