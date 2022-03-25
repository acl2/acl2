; Utilities about the LD-HISTORY
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (in-theory (disable weak-ld-history-entry-p get-global
                           ;;boundp-global
                           )))

;; Recognize a true list of ld-history-entries.
(defun weak-ld-history-entry-list-p (entries)
  (declare (xargs :guard t))
  (if (atom entries)
      (null entries)
    (and (weak-ld-history-entry-p (first entries))
         (weak-ld-history-entry-list-p (rest entries)))))

;; Returns the most recent THM or DEFTHM submitted by the user, or throws an error is there isn't one.
(defund most-recent-theorem-aux (ld-history whole-ld-history)
  (declare (xargs :guard (weak-ld-history-entry-list-p ld-history)))
  (if (endp ld-history)
      (er hard? 'most-recent-theorem-aux "Can't find a theorem in the history, which is ~x0" whole-ld-history)
    (let* ((most-recent-command (first ld-history))
           (most-recent-command-input (ld-history-entry-input most-recent-command)))
      (let ( ;; Strip must-fail, if present:
            (most-recent-command-input (if (and (consp most-recent-command-input)
                                                (eq 'must-fail (car most-recent-command-input))
                                                (= 1 (len (cdr most-recent-command-input))))
                                           (cadr most-recent-command-input)
                                         most-recent-command-input)))
        (if (and (consp most-recent-command-input)
                 (member-eq (car most-recent-command-input) '(thm defthm defthmd))) ;todo: support defrule? rule? verify-termination?  verify-guards? what about other kinds of proofs?
            most-recent-command-input
          ;; Keep looking:
          (most-recent-theorem-aux (rest ld-history) whole-ld-history))))))

;; Returns the most recent THM or DEFTHM submitted by the user, or throws an error is there isn't one.
(defund most-recent-theorem (state)
  (declare (xargs :stobjs state
                  ;; is this implied by statep?:
                  :guard (and (boundp-global 'ld-history state)
                              (weak-ld-history-entry-list-p (get-global 'ld-history state)))))
  (let ((ld-history (ld-history state)))
    (most-recent-theorem-aux ld-history ld-history)))

;; We are in multiple entry mode IFF the ld-history has length at least 2.
(defund multiple-ld-history-entry-modep (state)
  (declare (xargs :stobjs state
                  :guard-hints (("Goal" :in-theory (enable state-p1))) ; todo: Drop?
                  ))
  (< 1 (len (ld-history state))))
