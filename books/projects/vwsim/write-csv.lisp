
; write-csv.lisp

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; Written by Matt Kaufmann
; Modified (very little) by Vivek Ramanathan

; This is a raw-Lisp only file, because of print-row.

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

#||
For example:

(write-csv '((a 1 2 3) (b 4 5 6)) "foo" state)

then "foo" will look as follows:

a,b
1,4
2,5
3,6

||#

(program)
(set-state-ok t) ; avoids repeated (declare (xargs :stobjs state))

(defun print-row (lst chan state)

; Using a do loop$ here as shown below doesn't help over a more naive
; implementation.  Consider:

; (time$ (vwsim "Testing/test-circuits/cirs/dualRailTest.cir"
;               :time-step (* 1/4 *pico*)
;               :time-stop (* 1000 *pico*)
;               :save-var 'full-sim
;               :output-file "xx"))

; Here is our naive code.

  (cond ((endp lst) (newline chan state))
        ((endp (cdr lst))
         (pprogn (princ$ (car lst) chan state)
                 (newline chan state)))
        (t (pprogn (princ$ (car lst) chan state)
                   (princ$ "," chan state)
                   (print-row (cdr lst) chan state))))

; The result was as follows with that naive code.

; (VWSIM "Testing/test-circuits/cirs/dualRailTest.cir" ...) took 
; 25.29 seconds realtime, 25.27 seconds runtime
; (23,193,275,104 bytes allocated).

; With the do loop$ code below, we have gotten this:

; 25.39 seconds realtime, 25.37 seconds runtime
; (23,193,291,440 bytes allocated).

; What follows is that do loop$ code, which only works if we include the
; following events above.

; (include-book "projects/apply/top" :dir :system)
; #-raw
; (defbadge princ$)
; #-raw
; (defbadge newline)

#|
  (loop$ with tail = lst do
         :values (state)
         (progn (setq state (princ$ (car tail) chan state))
                (cond ((cdr tail)
                       (progn (setq tail (cdr tail))
                              (setq state (princ$ #\, chan state))))
                      (t (loop-finish))))
         finally (progn (setq state (newline chan state))
                        (return state)))
|#

; We also tried the following, but it was worse.

#|
  (cond ((endp lst) (newline chan state))
        (t (mv-let (col state)
             (fmt1! "~x0~s1"
                    (list (cons #\0 (car lst))
                          (cons #\1 (if (cdr lst) "," "")))
                    0 chan state nil) ; float or rational
             (declare (ignore col))
             (print-row (cdr lst) chan state))))
|#

; That gave us:

; (VWSIM "Testing/test-circuits/cirs/dualRailTest.cir" ...) took 
; 28.30 seconds realtime, 28.28 seconds runtime
; (24,906,280,912 bytes allocated).

; Another thing I tried, with the present body of this function, was to print
; to a string and then write the string to a file.  That didn't help:

; (VWSIM "Testing/test-circuits/cirs/dualRailTest.cir" ...) took 
; 26.26 seconds realtime, 26.25 seconds runtime
; (25,323,543,344 bytes allocated).

  )

(defun write-csv1 (alist chan state)
  (cond ((endp (car alist))
         (close-output-channel chan state))
        (t (b* ((cars (strip-cars alist))
                (cdrs (strip-cdrs alist))
                (state (print-row cars chan state)))
             (write-csv1 cdrs chan state)))))

(defun write-csv
    (alist    ;; a VWSIM simulation record
     filename ;; the csv file that the simulation is written to.
     state    ;; ACL2 state
     )

; Note: Filename can be overwritten.

  (declare (xargs :guard (and (alistp alist)
                              (true-list-listp alist) ; all of the same length
                              (stringp filename))))
  (state-global-let*
   ((fmt-hard-right-margin 100000 set-fmt-hard-right-margin)
    (fmt-soft-right-margin 100000 set-fmt-soft-right-margin))
   (b* (((mv channel state)
         (open-output-channel filename :character state))
        ((when (null channel))
         (er soft 'write-csv
             "Unable to open a channel to output file ~x0."
             filename))
        (state (write-csv1 alist channel state)))
     (value (list :WROTE filename)))))
