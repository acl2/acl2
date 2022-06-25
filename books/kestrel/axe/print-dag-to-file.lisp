; Printing DAGs to files
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "misc/file-io" :dir :system)
(include-book "kestrel/utilities/strings" :dir :system) ;for newline-string
(include-book "kestrel/utilities/temp-dirs" :dir :system)

(defttag print-to-file) ;this lets us call open-output-channel!

;returns state
(defun print-dag-to-file-aux (dag-lst channel state)
  (declare (xargs :mode :program ; because of PPRINT-OBJECT-OR-STRING (calling FMT would also require :program mode)
                  :stobjs state))
  (if (endp dag-lst)
      state
    (let ((entry (car dag-lst)))
      (pprogn (princ$ " " channel state)
              (pprint-object-or-string entry channel state) ; todo: call something faster or nicer here?  Try print-object$.
              ;; (fmt "~F0" (acons #\0 entry nil) channel state nil)
              (princ$ (newline-string) channel state)
              (print-dag-to-file-aux (rest dag-lst) channel state)))))

;returns state
(defun print-dag-to-file (dag-lst fname state)
  (declare (xargs :mode :program ;drop?
                  :guard (stringp fname)
                  :stobjs state))
  (mv-let (channel state)
	  (open-output-channel! fname :character state)
          (if (not channel)
              (prog2$ (hard-error 'print-dag-to-file "Unable to open file ~s0 for :character output." (acons #\0 fname nil))
                      state)
            (prog2$ (cw "Writing DAG to file:~%~s0~%.~%" fname)
                    (if (quotep dag-lst)
                        (pprogn (pprint-object-or-string dag-lst channel state)
                                (close-output-channel channel state))
                      (pprogn (princ$ "(" channel state)
                              (print-dag-to-file-aux dag-lst channel state)
                              (princ$ ")" channel state)
                              (close-output-channel channel state)))))))

;; Returns state
(defun print-dag-to-temp-file (dag-lst base-filename state)
  (declare (xargs :stobjs state
                  :mode :program
                  :guard (stringp base-filename)))
  (mv-let (temp-dir-name state)
    (maybe-make-temp-dir state)
    (print-dag-to-file dag-lst (concatenate 'string temp-dir-name "/" base-filename) state)))
