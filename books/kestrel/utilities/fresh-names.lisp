; Utilities for making fresh names
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "kestrel/utilities/pack" :dir :system)

;rename fresh-symbol-aux ?
(defun fresh-var-name (base-name current-num syms-to-avoid)
  (declare (type (integer 0 *) current-num)
           (xargs :measure (len syms-to-avoid)
                  :guard (true-listp syms-to-avoid)))
  (let ((candidate (pack$ base-name current-num)))
    (if (not (member-eq candidate syms-to-avoid))
        candidate
      (fresh-var-name base-name
                      (+ 1 current-num)
                      (remove-eq candidate
                                 syms-to-avoid)))))

;rename fresh-symbol ?
;example: (make-fresh-name 'x '(x x1 x2 x3 x5)) = x4
(defun make-fresh-name (desired-name names-to-avoid)
  (declare (xargs :guard (and (symbolp desired-name)
                              (symbol-listp names-to-avoid))))
  (if (not (member-eq desired-name names-to-avoid))
      desired-name
    (fresh-var-name desired-name 1 names-to-avoid)))

(defun fresh-var-names (num starting-name vars-to-avoid)
  (declare (type (integer 0 *) num)
           (xargs :guard (true-listp vars-to-avoid)))
  (if (zp num)
      nil
    (let ((fresh-name (fresh-var-name starting-name 0 vars-to-avoid))) ;should this return a new starting-num?
      (cons fresh-name (fresh-var-names (+ -1 num) starting-name (cons fresh-name vars-to-avoid))))))
