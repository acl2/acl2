; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "LRAT")

(include-book "incremental")

(program)
(set-state-ok t)

(defun check-formula-with-increasing-keys (formula)
  (declare (xargs :guard t))
  (cond ((atom formula)
         (or (null formula)
             (er hard? 'check-formula-with-increasing-keys
                 "Alleged formula is not a true list!")))
        ((atom (car formula))
         (er hard? 'check-formula-with-increasing-keys
             "Alleged formula is not an alist!  Offending member:~|~x0"
             (car formula)))
        ((not (and (posp (caar formula))
                   (integer-listp (cdar formula))
                   (not (member 0 (cdar formula)))))
         (er hard? 'check-formula-with-increasing-keys
             "Alleged formula has bad entry:~|~x0~|This entry fails to be ~
              a nil-terminated list of non-zero integers starting with a ~
              positive integer."
             (car formula)))
        ((and (cdr formula)
              (not (< (caar formula) (caadr formula))))
         (er hard? 'check-formula-with-increasing-keys
             "Formula does not have indices in strictly increasing order: ~
              it has an index ~x0 followed immediately by index ~x1."
             (caar formula) (caadr formula)))
        (t (check-formula-with-increasing-keys (cdr formula)))))

(defun print-clause (clause channel state)
  (cond ((endp clause) state)
        (t (pprogn (princ$ (car clause) channel state)
                   (princ$ " " channel state)
                   (cond ((cdr clause)
                          state)
                         (t (pprogn (princ$ "0" channel state)
                                    (newline channel state))))
                   (print-clause (cdr clause) channel state)))))

(defun print-clause-lst (clause-lst channel state)
  (cond ((endp clause-lst) state)
        (t (pprogn (print-clause (car clause-lst) channel state)
                   (print-clause-lst (cdr clause-lst) channel state)))))

(defun print-cnf-header (formula channel state)
  (mv-let (col state)
    (fmt1 "p cnf ~x0 ~x1~|"
          (list (cons #\0 (formula-max-var formula 0))
                (cons #\1 (length formula)))
          0 channel state nil)
    (declare (ignore col))
    state))

(defun print-formula-fn1 (formula channel header-p state)
  (pprogn (if header-p
              (print-cnf-header formula channel state)
            state)
          (print-clause-lst (strip-cdrs formula) channel state)))

(defun print-formula-fn (formula filename header-p ctx state)
  (prog2$
   (check-formula-with-increasing-keys formula)
   (cond
    ((eq filename t) ; print to standard output
     (pprogn (print-formula-fn1 formula (standard-co state) header-p state)
             (value :invisible)))
    ((not (stringp filename))
     (er soft ctx
         "The filename argument for ~x0 must be either a string or (for ~
          standard output) ~x1.  The argument ~x2 is thus illegal."
         'print-formula t filename))
    (t
     (mv-let
       (channel state)
       (open-output-channel filename :character state)
       (cond ((null channel)
              (er soft ctx
                  "Unable to open file ~x0 for output."
                  filename))
             (t (pprogn (print-formula-fn1 formula channel header-p state)
                        (close-output-channel channel state)
                        (value filename)))))))))

(defmacro print-formula (formula &key
                                 filename
                                 (header-p 't)
                                 (ctx ''print-formula))

; Print the given formula to the given file, unless filename is nil in which
; case print to standard output.

  `(print-formula-fn ,formula ,filename ,header-p ,ctx state))
