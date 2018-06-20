; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.





(in-package "ACL2")

(include-book "regex-exec")
(include-book "regex-parse")
;; (include-book "../../io-0.2/io-core")
(program)

(set-state-ok t)


(in-theory (disable state-p1
                    open-input-channel-p1))

;; Call with (read-line channel nil state);
;; beg is an accumulator variable.
;; Returns triplet (line file-still-good state).
(defun read-line$ (channel beg state)
  (declare (xargs

; Matt K. mod 2/20/2016: file-measure is undefined, and we no longer allow
; undefined measures even for :program mode functions.
;           :measure (file-measure channel state)
            :guard (and (character-listp beg)
                        (state-p state)
                        (symbolp channel)
                        (open-input-channel-p channel
                                              :character
                                              state))))
  (if (mbt (state-p state))
      (mv-let (ch state)
              (read-char$ channel state)
              (if (null ch)
                  (mv nil (coerce (revappend beg nil) 'string) state)
                (if (equal ch #\Newline)
                    (mv t (coerce (revappend beg nil) 'string) state)
                  (read-line$ channel (cons ch beg) state))))
    (mv nil nil state)))


(defthm read-line$-measure-weak
  (<= (file-measure channel
                    (mv-nth 2 (read-line$ channel beg state)))
      (file-measure channel state))
  :rule-classes (:rewrite :linear))

(defthm read-line$-measure-strong
  (implies (car (read-line$ channel beg state))
           (< (file-measure channel
                            (mv-nth 2 (read-line$ channel beg state)))
              (file-measure channel state)))
  :rule-classes (:rewrite :linear))

(defthm read-line$-stringp
  (implies (and (state-p1 state)
                (symbolp channel)
                (open-input-channel-p1 channel
                                      :character
                                      state)
                (character-listp beg))
           (stringp (mv-nth 1 (read-line$ channel beg state)))))

(defthm read-line$-open-input-channel
  (implies (and (symbolp channel)
                (open-input-channel-p1 channel :character state))
           (open-input-channel-p1
            channel :character
            (mv-nth 2 (read-line$ channel beg state)))))


(defthm read-line$-state
  (implies (and (state-p1 state)
                (symbolp channel)
                (open-input-channel-p1 channel :character state))
           (state-p1 (mv-nth 2 (read-line$ channel beg state)))))



;; (defun grep-through-file (regex channel opts matches lines state)
;;   (declare (xargs :measure (file-measure channel state)
;;                   :guard (and (regex-p regex)
;;                               (state-p state)
;;                               (symbolp channel)
;;                               (open-input-channel-p channel
;;                                                     :character
;;                                                     state)
;;                               (consp opts)
;;                               (string-listp matches)
;;                               (string-listp lines))))
;;   (if (mbt (state-p state))
;;       (mv-let (more line state) (read-line$ channel nil state)
;;               (if more
;;                   (mv-let (have-match matchstr backrefs)
;;                           (match-regex regex line line)
;;                           (declare (ignore backrefs))
;;                           (if have-match
;;                               (grep-through-file
;;                                regex channel opts (cons matchstr matches)
;;                                (cons line lines)  state)
;;                             (grep-through-file regex channel opts
;;                                                matches lines state)))
;;                 (mv (reverse matches) (reverse lines) state)))
;;     (mv (reverse matches) (reverse lines) state))))


;; (defthm grep-through-open-input-channel
;;   (implies (and (symbolp channel)
;;                 (open-input-channel-p1 channel :character state))
;;            (open-input-channel-p1
;;             channel :character
;;             (mv-nth 2 (grep-through-file regex channel opts matches lines state)))))



;; (defthm grep-through-state
;;   (implies (and (state-p1 state)
;;                 (symbolp channel)
;;                 (open-input-channel-p1 channel :character state))
;;            (state-p1 (mv-nth 2 (grep-through-file regex channel opts
;;                                                   matches lines state)))))






;; (defun grep-file (regex file opts state)
;;   (declare (xargs :guard (and (stringp regex)
;;                               (stringp file)
;;                               (state-p state)
;;                               (consp opts))))
;;   (if (state-p state)
;;       (let ((regex (regex-do-parse regex (parse-options 'ere t nil nil nil))))
;;         (if (stringp regex)
;;             (mv 2 nil nil state)
;;           (mv-let (channel state) (open-input-channel file :character state)
;;                   (if (and (symbolp channel)
;;                            (open-input-channel-p channel :character state))
;;                       (mv-let (matches lines state)
;;                               (grep-through-file regex channel opts nil nil state)
;;                               (let ((state (close-input-channel channel state)))
;;                                 (mv (if matches 0 1) matches lines state)))
;;                     (mv 2 nil nil state)))))
;;     (mv 2 nil nil state)))

;; (defmacro grep (regex file &optional print-whole-line)
;;   `(grep-fun ,regex ,file `(,,(not print-whole-line)) state))

