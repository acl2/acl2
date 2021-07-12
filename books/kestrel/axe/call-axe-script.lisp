; A tool to call Axe-related scripts
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/include-book-dir-dollar" :dir :system)

(defttag call-axe-script) ; because we call sys-call+

(local (in-theory (disable sys-call+ state-p get-global)))

; Returns (mv status state) where status is the numeric exits status of calling
; SCRIPT-NAME on SCRIPT-ARGS.  A status of 0 indicates no error.
(defund call-axe-script (script-name ; wrt the axe/ dir
                         script-args
                         state)
  (declare (xargs :guard (and (stringp script-name)
                              (string-listp script-args))
                  :stobjs state))
  (let* ((system-books-dir (include-book-dir$ :system state)) ; trailing slash
         (script-path (concatenate 'string system-books-dir "kestrel/axe/" script-name)))
    (mv-let (erp output state)
      (sys-call+ script-path script-args state)
      (prog2$ (cw "(Output from ~s0: ~X12)~%" script-name output nil)
              (if erp
                  (if (not (natp erp))
                      (prog2$ (er hard? 'call-axe-script "Unexpected (non-natp) exit status from script: ~x0." erp)
                              (mv 1 state))
                    (prog2$ nil ;; (er hard? 'call-axe-script "Error calling script (see output above).")
                            (mv erp state)))
                (mv 0 ; ensure 0 exit status if no error
                    state))))))

(defthm natp-of-mv-nth-0-of-call-axe-script
  (natp (mv-nth 0 (call-axe-script script-name
                                   script-args
                                   state)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable call-axe-script))))

;; Example: (call-axe-script "ls.sh" (list "call-axe-script.lisp") state)
