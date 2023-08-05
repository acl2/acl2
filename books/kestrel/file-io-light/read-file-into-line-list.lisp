; Reading a file into a list of lines (strings)
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also read-file-lines and read-file-lines-no-newlines.  This utility is
;; intended to be more lightweight than those.

(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))
(local (include-book "read-char-dollar"))
(local (include-book "open-input-channel"))
(local (include-book "open-input-channel-p"))
(local (include-book "close-input-channel"))
(local (include-book "channels"))
(local (include-book "channels2"))
(local (include-book "typed-io-listp"))
(local (include-book "kestrel/utilities/state" :dir :system))

;; (local (in-theory (disable mv-nth)))

;; Returns (mv lines state) where LINES is a list of strings representing the
;; lines of the file.  NEWLINESP determines whether newlines are included at
;; the end of the lines that have them (the last line may not have one).
(defund read-channel-into-line-list (channel newlinesp chars-acc lines-acc state)
  (declare (xargs :guard (and (symbolp channel)
                              (open-input-channel-p channel :character state)
                              (booleanp newlinesp)
                              (character-listp chars-acc)
                              (string-listp lines-acc))
                  :stobjs state
                  :measure (len (cddr (assoc-equal channel (open-input-channels state))) ;;(channel-contents channel state)
                                )
                  :hints (("Goal" :in-theory (enable channel-contents)))
                  :guard-hints (("Goal" :in-theory (enable open-input-channel-p)))))
  (if (not (mbt (and (open-input-channel-p channel :character state) ; for termination
                     (state-p state))))
      (mv nil state)
    (mv-let (maybe-char state)
      (read-char$ channel state)
      (if (not maybe-char)
          ;; No more characters:
          (if (endp chars-acc)
              ;; Suppress empty final line:
              (mv (reverse lines-acc) state)
            (let ((lines-acc (cons (coerce (reverse chars-acc) 'string) lines-acc)))
              (mv (reverse lines-acc) state)))
        ;; At least one more char:
        (if (eql #\Newline maybe-char)
            (let ((chars-acc (if newlinesp (cons maybe-char chars-acc) chars-acc)))
              (read-channel-into-line-list channel newlinesp
                                       nil ; empty char-acc for next line
                                       (cons (coerce (reverse chars-acc) 'string) lines-acc)
                                       state))
          ;; normal char:
          (read-channel-into-line-list channel newlinesp (cons maybe-char chars-acc) lines-acc state))))))

(defthm string-listp-of-mv-nth-0-of-read-channel-into-line-list
  (implies (string-listp lines-acc)
           (string-listp (mv-nth 0 (read-channel-into-line-list channel newlinesp chars-acc lines-acc state))))
  :hints (("Goal" :in-theory (enable read-channel-into-line-list
                                     ;; channel-contents
                                     read-char$ ;todo
                                     ))))

(defthm state-p1-of-mv-nth-1-of-read-channel-into-line-list
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (read-channel-into-line-list channel newlinesp chars-acc lines-acc state))))
  :hints (("Goal" :in-theory (enable read-channel-into-line-list
                                     ;; channel-contents
                                     read-char$ ;todo
                                     ))))

(defthm state-p-of-mv-nth-1-of-read-channel-into-line-list
  (implies (state-p state)
           (state-p (mv-nth 1 (read-channel-into-line-list channel newlinesp chars-acc lines-acc state)))))

;; Gen the typ?
(defthm open-input-channel-p1-of-mv-nth-1-of-read-channel-into-line-list
  (implies (open-input-channel-p1 channel :character state)
           (open-input-channel-p1 channel :character (mv-nth 1 (read-channel-into-line-list channel newlinesp chars-acc lines-acc state))))
  :hints (("Goal" :in-theory (enable read-channel-into-line-list
                                     ;; channel-contents
                                     read-char$ ;todo
                                     ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reads the file indicated by PATH-TO-FILE into a list of strings, one for
;; each line of the file.  If NEWLINESP is nil, the newlines at the end of
;; lines are dropped (the last line may not have one).
;; Returns (mv erp lines state).
(defund read-file-into-line-list (path-to-file newlinesp state)
  (declare (xargs :guard (and (stringp path-to-file)
                              (booleanp newlinesp))
                  :stobjs state))
  (mv-let (channel state)
    (open-input-channel path-to-file :character state)
    (if (not channel)
        ;; Error:
        (mv `(:could-not-open-channel ,path-to-file) nil state)
      (mv-let (lines state)
        (read-channel-into-line-list channel newlinesp nil nil state)
        (let ((state (close-input-channel channel state)))
          (mv nil ; no error
              lines
              state))))))

(defthm string-listp-of-mv-nth-1-of-read-file-into-line-list
  (string-listp (mv-nth 1 (read-file-into-line-list path-to-file newlinesp state)))
  :hints (("Goal" :in-theory (enable read-file-into-line-list))))

(defthm state-p1-of-mv-nth-2-of-read-file-into-line-list
  (implies (and (state-p1 state)
                (stringp path-to-file))
           (state-p1 (mv-nth 2 (read-file-into-line-list path-to-file newlinesp state))))
  :hints (("Goal" :in-theory (enable read-file-into-line-list))))

(defthm state-p-of-mv-nth-2-of-read-file-into-line-list
  (implies (and (state-p state)
                (stringp path-to-file))
           (state-p (mv-nth 2 (read-file-into-line-list path-to-file newlinesp state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv lines state).  This wrapper does not pass back errors, but it
;; may throw one.
(defund read-file-into-line-list-no-error (path-to-file newlinesp state)
  (declare (xargs :guard (and (stringp path-to-file)
                              (booleanp newlinesp))
                  :stobjs state))
  (mv-let (erp lines state)
    (read-file-into-line-list path-to-file newlinesp state)
    (if erp
        (prog2$ (er hard? 'read-file-into-line-list-no-error "Error reading lines from ~x0." path-to-file)
                (mv nil state))
      (mv lines state))))

(defthm string-listp-of-mv-nth-0-of-read-file-into-line-list-no-error
  (string-listp (mv-nth 0 (read-file-into-line-list-no-error path-to-file newlinesp state)))
  :hints (("Goal" :in-theory (enable read-file-into-line-list-no-error))))

(defthm state-p1-of-mv-nth-1-of-read-file-into-line-list-no-error
  (implies (and (state-p1 state)
                (stringp path-to-file))
           (state-p1 (mv-nth 1 (read-file-into-line-list-no-error path-to-file newlinesp state))))
  :hints (("Goal" :in-theory (enable read-file-into-line-list-no-error))))

(defthm state-p-of-mv-nth-1-of-read-file-into-line-list-no-error
  (implies (and (state-p state)
                (stringp path-to-file))
           (state-p (mv-nth 1 (read-file-into-line-list-no-error path-to-file newlinesp state)))))
