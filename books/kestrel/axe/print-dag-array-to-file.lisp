; Printing dag-arrays to files
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
(include-book "dag-arrays")
(include-book "kestrel/utilities/strings" :dir :system) ;for newline-string
(include-book "kestrel/utilities/temp-dirs" :dir :system)

(defttag print-to-file) ;this lets us call open-output-channel!

;returns state
;;elements after the first are preceded by a newline and a space:
(defun print-dag-array-to-file-aux (dag-array-name dag-array nodenum channel state)
  (declare (xargs :mode :program ; because this calls pprint-object-or-string
                  :stobjs state))
  (if (not (natp nodenum))
      state
    (let ((expr (aref1 dag-array-name dag-array nodenum)))
      (pprogn (princ$ (newline-string) channel state)
              (princ$ " " channel state)
              (pprint-object-or-string (cons nodenum expr) channel state) ;fixme call something faster? ;fixme save this cons?
              (print-dag-array-to-file-aux dag-array-name dag-array (+ -1 nodenum) channel state)))))

;returns state
;move to acl2-arrays book? maybe not, because of the trust-tag..
;remove dag from name?
(defun print-dag-array-to-file (dag-array-name dag-array dag-len fname state)
  (declare (xargs :mode :program ; because this calls pprint-object-or-string
                  :guard (stringp fname)
                  :stobjs state))
  (mv-let (channel state)
	  (open-output-channel! fname :character state)
          (if (not channel)
              (prog2$ (hard-error 'print-dag-array-to-file "Unable to open file ~s0 for :character output." (acons #\0 fname nil))
                      state)
            (prog2$ (cw "Writing DAG to file:~%~s0~%" fname)
                    (if (zp dag-len)
                        ;;empty array:
                        (pprogn (princ$ "()" channel state)
                                (close-output-channel channel state))
                      ;;non-empty-array
                    (pprogn (princ$ "(" channel state)
                            ;the first node is printed with no whitespace before it:
                            (let ((top-nodenum (+ -1 dag-len)))
                              (pprint-object-or-string
                               (cons top-nodenum (aref1 dag-array-name dag-array top-nodenum)) channel state)) ; TODO: save this cons?
                            ;; Print the rest of the nodes:
                            (print-dag-array-to-file-aux dag-array-name dag-array (+ -2 dag-len) channel state)
                            (princ$ ")" channel state)
                            (close-output-channel channel state)))))))

;; Returns state
(defun print-dag-array-to-temp-file (array-name array array-len base-filename state)
  (declare (xargs :stobjs state
                  :mode :program
                  :guard (stringp base-filename)))
  (mv-let (temp-dir-name state)
    (maybe-make-temp-dir state)
    (print-dag-array-to-file array-name array array-len (concatenate 'string temp-dir-name "/" base-filename) state)))
