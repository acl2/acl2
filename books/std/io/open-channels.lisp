; ACL2 Standard Library
; Copyright (C) 2017 Keshav Kini
;
; Contact: Keshav Kini <keshav.kini@gmail.com>
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Keshav Kini <keshav.kini@gmail.com>

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

(local
 (defthm assoc-after-delete-assoc
   ;; borrowed from projects/filesystems/file-system-lemmas.lisp --
   ;; should probably be in std/alists somewhere, I guess?
   (implies (not (equal name1 name2))
            (equal (assoc-equal name1 (delete-assoc name2 alist))
                   (assoc-equal name1 alist)))))

(local (in-theory (e/d

                   (put-global
                    open-input-channel-p1
                    open-output-channel-p1

; Below are the functions which we are proving will not affect the list
; of open / closed channels, under appropriate assumptions.

                    open-input-channel
                    open-output-channel
                    close-input-channel
                    close-output-channel
                    read-char$
                    read-byte$
                    read-object
                    princ$
                    write-byte$
                    print-object$
                    set-serialize-character)

                   (open-channels-p
                    ordered-symbol-alistp
                    plist-worldp
                    symbol-alistp
                    timer-alistp
                    known-package-alistp
                    true-listp
                    32-bit-integer-listp
                    integer-listp
                    readable-files-p
                    written-files-p
                    read-files-p
                    writeable-files-p
                    true-list-listp
                    all-boundp
                    nth
                    update-nth
                    make-input-channel
                    make-output-channel))))

; NOTE: Several of the lemmas below have some weird hypotheses, marked
; with a (*).  These hypotheses should all be unconditionally true
; when dealing with the real ACL2 state, but currently `state-p1' is
; not strong enough to imply them.  If the definition of `state-p1' is
; strengthened in the future, a (state-p1 state) hypothesis could be
; added where necessary, and these weird hypotheses could be removed.

;;;;;;;;;;;;;;;;
;;;; The built-in I/O functions preserve openness of input channels
;;;;;;;;;;;;;;;;

(defthm open-input-channel-p1-under-open-input-channel
  ;; Desired version:
  ;; (implies (and (open-input-channel-p1 channel type state)
  ;;               (state-p1 state))
  ;;          (b* (((mv & state)
  ;;                (open-input-channel fname other-type state)))
  ;;            (open-input-channel-p1 channel type state)))
  (implies (open-input-channel-p1 channel type state)
           (b* (((mv other-channel state)
                 (open-input-channel fname other-type state)))
             (implies (implies (equal other-channel channel) ; (*)
                               (equal other-type type))
                      (open-input-channel-p1 channel type state)))))

(defthm open-input-channel-p1-under-open-output-channel
  (implies (open-input-channel-p1 channel type state)
           (b* (((mv & state)
                 (open-output-channel fname other-type state)))
             (open-input-channel-p1 channel type state))))

(defthm open-input-channel-p1-under-close-input-channel
  ;; Desired version:
  ;; (implies (and (open-input-channel-p1 channel type state)
  ;;               (state-p1 state))
  ;;          (b* ((state (close-input-channel other-channel state)))
  ;;            (iff (open-input-channel-p1 channel type state)
  ;;                 (not (equal channel other-channel)))))
  (implies (and (open-input-channel-p1 channel type state)
                (not (equal channel other-channel))) ; (*)
           (b* ((state (close-input-channel other-channel state)))
             (open-input-channel-p1 channel type state))))

(defthm open-input-channel-p1-under-close-output-channel
  (implies (open-input-channel-p1 channel type state)
           (b* ((state (close-output-channel other-channel state)))
             (open-input-channel-p1 channel type state))))

(defthm open-input-channel-p1-under-read-char$
  (implies (open-input-channel-p1 channel type state)
           (b* (((mv & state) (read-char$ other-channel state)))
             (open-input-channel-p1 channel type state))))

(defthm open-input-channel-p1-under-read-byte$
  (implies (open-input-channel-p1 channel type state)
           (b* (((mv & state) (read-byte$ other-channel state)))
             (open-input-channel-p1 channel type state))))

(defthm open-input-channel-p1-under-read-object
  (implies (open-input-channel-p1 channel type state)
           (b* (((mv & & state) (read-object other-channel state)))
             (open-input-channel-p1 channel type state))))

(defthm open-input-channel-p1-under-princ$
  (implies (open-input-channel-p1 channel type state)
           (b* ((state (princ$ x other-channel state)))
             (open-input-channel-p1 channel type state))))

(defthm open-input-channel-p1-under-write-byte$
  (implies (open-input-channel-p1 channel type state)
           (b* ((state (write-byte$ byte other-channel state)))
             (open-input-channel-p1 channel type state))))

(defthm open-input-channel-p1-under-print-object$
  (implies (open-input-channel-p1 channel type state)
           (b* ((state (print-object$ byte other-channel state)))
             (open-input-channel-p1 channel type state))))

(defthm open-input-channel-p1-under-set-serialize-character
  (implies (open-input-channel-p1 channel type state)
           (b* ((state (set-serialize-character c state)))
             (open-input-channel-p1 channel type state))))

;;;;;;;;;;;;;;;;
;;;;
;;;;;;;;;;;;;;;;

(defthm open-output-channel-p1-under-open-input-channel
  (implies (open-output-channel-p1 channel type state)
           (b* (((mv & state)
                 (open-input-channel fname other-type state)))
             (open-output-channel-p1 channel type state))))

(defthm open-output-channel-p1-under-open-output-channel
  ;; Desired version:
  ;; (implies (and (open-output-channel-p1 channel type state)
  ;;               (state-p1 state))
  ;;          (b* (((mv & state)
  ;;                (open-output-channel fname other-type state)))
  ;;            (open-output-channel-p1 channel type state)))
  (implies (open-output-channel-p1 channel type state)
           (b* (((mv other-channel state)
                 (open-output-channel fname other-type state)))
             (implies (implies (equal other-channel channel) ; (*)
                               (equal other-type type))
                      (open-output-channel-p1 channel type state)))))

(defthm open-output-channel-p1-under-close-input-channel
  (implies (open-output-channel-p1 channel type state)
           (b* ((state (close-input-channel other-channel state)))
             (open-output-channel-p1 channel type state))))

(defthm open-output-channel-p1-under-close-output-channel
  ;; Desired version:
  ;; (implies (and (open-output-channel-p1 channel type state)
  ;;               (state-p1 state))
  ;;          (b* ((state (close-output-channel other-channel state)))
  ;;            (iff (open-output-channel-p1 channel type state)
  ;;                 (not (equal channel other-channel)))))
  (implies (and (open-output-channel-p1 channel type state)
                (not (equal channel other-channel))) ; (*)
           (b* ((state (close-output-channel other-channel state)))
             (open-output-channel-p1 channel type state))))

(defthm open-output-channel-p1-under-read-char$
  (implies (open-output-channel-p1 channel type state)
           (b* (((mv & state) (read-char$ other-channel state)))
             (open-output-channel-p1 channel type state))))

(defthm open-output-channel-p1-under-read-byte$
  (implies (open-output-channel-p1 channel type state)
           (b* (((mv & state) (read-byte$ other-channel state)))
             (open-output-channel-p1 channel type state))))

(defthm open-output-channel-p1-under-read-object
  (implies (open-output-channel-p1 channel type state)
           (b* (((mv & & state) (read-object other-channel state)))
             (open-output-channel-p1 channel type state))))

(defthm open-output-channel-p1-under-princ$
  (implies (open-output-channel-p1 channel type state)
           (b* ((state (princ$ x other-channel state)))
             (open-output-channel-p1 channel type state))))

(defthm open-output-channel-p1-under-write-byte$
  (implies (open-output-channel-p1 channel type state)
           (b* ((state (write-byte$ byte other-channel state)))
             (open-output-channel-p1 channel type state))))

(defthm open-output-channel-p1-under-print-object$
  (implies (open-output-channel-p1 channel type state)
           (b* ((state (print-object$ byte other-channel state)))
             (open-output-channel-p1 channel type state))))

(defthm open-output-channel-p1-under-set-serialize-character
  (implies (open-output-channel-p1 channel type state)
           (b* ((state (set-serialize-character c state)))
             (open-output-channel-p1 channel type state))))
