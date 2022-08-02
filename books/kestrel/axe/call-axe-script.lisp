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
(include-book "centaur/misc/tshell" :dir :system)

(defttag call-axe-script) ; because we call sys-call+

(local (in-theory (disable sys-call+ state-p get-global)))

;move
;optimize
(defund concatenate-strings-with-spaces (strings)
  (declare (xargs :guard (string-listp strings)))
  (if (endp strings)
      ""
    (if (endp (rest strings))
        (first strings)
      (concatenate 'string
                   (first strings)
                   " "
                   (concatenate-strings-with-spaces (rest strings))))))

(defthm stringp-of-concatenate-strings-with-spaces
  (implies (string-listp strings)
           (stringp (concatenate-strings-with-spaces strings)))
  :hints (("Goal" :in-theory (enable concatenate-strings-with-spaces))))

; Returns (mv status state) where status is the numeric exits status of calling
; SCRIPT-NAME on SCRIPT-ARGS.  A status of 0 indicates no error.
(defund call-axe-script (script-name ; wrt the axe/ dir
                         script-args
                         state)
  (declare (xargs :guard (and (stringp script-name)
                              (string-listp script-args))
                  :stobjs state))
  (let* ((system-books-dir (include-book-dir$ :system state)) ; trailing slash
         (script-path (concatenate 'string system-books-dir "kestrel/axe/" script-name))
         (res (tshell-ensure) ; fast after the first time
              ))
    (declare (ignore res))
    ;; (mv-let (erp output state)
    ;;   (sys-call+ script-path script-args state)
    ;;   (declare (ignore output))
    (mv-let (status output)
      (tshell-call (concatenate 'string script-path " " (concatenate-strings-with-spaces script-args)) :save nil)
      (declare (ignore output)) ; not captured, since :save is nil
      ;; todo: check the output directly instead of re-directing to a file?
      (progn$
       ;; (cw "(Status from ~s0: ~X12)~%" script-name status nil) ; todo; add debug option and check it here?
       ;; (cw "(Output from ~s0: ~X12)~%" script-name output nil) ; todo; add debug option and check it here?
       (if (not (= 0 status))
           (if (not (natp status))
               (prog2$ (er hard? 'call-axe-script "Unexpected (non-natp) exit status, ~x0, from script ~x0." status script-name)
                       (mv 1 state))
             (progn$ (cw "WARNING: Non-zero exit status, ~x0, from script ~x1." status script-name)
                     (mv status state)))
         (mv status ; 0 exit status means no error
             state))))))

(defthm natp-of-mv-nth-0-of-call-axe-script
  (natp (mv-nth 0 (call-axe-script script-name script-args state)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable call-axe-script))))

;; Example: (call-axe-script "ls.sh" (list "call-axe-script.lisp") state)
