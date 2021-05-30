; A utility to get the PID of the ACL2 process
;
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "call-script") ;introduces a trust tag
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

(local (in-theory (disable boundp-global get-global put-global)))

; This is a stronger version of the built-in theorem
; UPDATE-ACL2-ORACLE-PRESERVES-STATE-P1. See also
; books/system/update-state.lisp.
(defthm state-p1-of-update-acl2-oracle
  (implies (state-p1 state)
           (equal (state-p1 (update-acl2-oracle x state))
                  (true-listp x)))
  :hints (("Goal" :in-theory (enable update-acl2-oracle state-p1 open-output-channels))))

;; this about updating the global-table
(defthm state-p1-of-update-nth-2-of-add-pair-of-nth-2
  (implies (and (state-p1 state)
                (symbolp key)
                (not (member-equal key '(current-acl2-world timer-alist))))
           (state-p1 (update-nth 2 (add-pair key value (nth 2 state)) state)))
  :hints (("Goal" :in-theory (e/d (state-p1) (all-boundp assoc-equal)))))

(defthm state-p1-of-update-global-table-of-add-pair-of-global-table
  (implies (and (state-p1 state)
                (symbolp key)
                (not (member-equal key '(current-acl2-world timer-alist))))
           (state-p1 (update-global-table (add-pair key value (global-table state)) state)))
  :hints (("Goal" :in-theory (e/d (update-global-table global-table) ()))))

(defthm state-p1-of-put-global
  (implies (and (state-p1 state)
                (symbolp key)
                (not (member-equal key '(current-acl2-world timer-alist))))
           (state-p1 (put-global key value state)))
  :hints (("Goal" :in-theory (enable put-global))))

;dup?
(defun string-butlast (str n)
  (declare (xargs :guard (and (stringp str)
                              (natp n))))
  (let* ((chars (explode-atom str 10))
         (new-chars (butlast chars n))
         (str (coerce new-chars 'string)))
    str))

(defund strip-final-newline (str)
  (declare (xargs :guard (stringp str)))
  (string-butlast str 1))

;; ;returns (mv pid state) where pid is the process ID of the current Lisp/ACL2 process
;; ;because the exit status of a bash script can only be in the range 0-255, this gets the low 8 bits and the high 8 bits separately and then puts them together
;; ;TODO: how to make this portable, without having to have the axe/ dir on your path?
;; (defun get-process-id (state)
;;   (declare (xargs :stobjs state :mode :program))
;;   (mv-let (pidlowbits state)
;;           (call-script "pidlowslice.bash" nil state)
;;           (mv-let (pidhighbits state)
;;                   (call-script "pidhighslice.bash" nil state)
;;                   (mv (+ pidlowbits (* 256 pidhighbits))
;;                       state))))

;; Get the process-id (pid) of the current process (represented as a string)
;; and also store it in a state globalto make subsequent calls fast.  Returns
;; (mv pid state).  Throws a hard error if something goes wrong.
(defund get-process-id (state)
  (declare (xargs :stobjs state
                  :guard-hints (("Goal" :in-theory (enable boundp-global)))))
  (if (boundp-global 'process-id state)
      (let ((pid (f-get-global 'process-id state)))
        (if (not (stringp pid)) ;todo: check that this is a string containing only digits?
            (prog2$ (er hard? 'get-process-id "Invalid stored process ID: ~x0." pid)
                    (mv "ERROR-BAD-PROCESS-ID" state))
          (mv pid state)))
    (mv-let (erp pid state)
      (call-script "get-process-id.sh" nil state)
      (if erp
          (mv-let (erp acl2_root state)
            (getenv$ "ACL2_ROOT" state)
            (declare (ignore erp)) ;always nil in practice
            (prog2$ (er hard? 'get-process-id "Error getting process ID.  PID is ~x0. ACL2_ROOT is ~x1" pid acl2_root)
                    (mv "ERROR-BAD-PROCESS-ID" state)))
        (let* ((pid (strip-final-newline pid))
               ;; Store it so the next call is fast:
               (state (f-put-global 'process-id pid state)))
          (progn$ (cw "(Process ID is: ~x0.)~%" pid)
                  (mv pid state)))))))

(defthm stringp-of-mv-nth-of-get-process-id
  (stringp (mv-nth 0 (get-process-id state)))
  :hints (("Goal" :in-theory (enable get-process-id))))

(defthm state-p1-of-mv-nth-of-get-process-id
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (get-process-id state))))
  :hints (("Goal" :in-theory (enable get-process-id))))
