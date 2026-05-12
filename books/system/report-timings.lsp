; Copyright (C) 2026, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For instructions on how to use this file, see comments in the definition of
; the constant *pass2-def-time-info* in the ACL2 sources.

(in-package "ACL2")

(defun pos-order (positions x y)
  (cond ((null positions) nil)
        ((< (nth (car positions) x) (nth (car positions) y))
         t)
        ((> (nth (car positions) x) (nth (car positions) y))
         nil)
        (t
         (pos-order (cdr positions) x y))))

(defun my-print-tuple (str tuple)
  (let ((x0 (car tuple))
        (x1 (cadr tuple))
        (x2 (caddr tuple))
        (x3 (cadddr tuple)))
    (format str "(~8,4f " x0)
    (format str "~8,4f " x1)
    (format str "~8,4f " x2)
    (if (and (sysfile-p x3)
             (eq (car x3) :system))
        (format str "[~a])~%" (cdr x3))
      (format str "~a)~%" x3))))

(defun report-timings (infile outfile &optional (positions '(0 1 2)))
; E.g.:
; (report-timings "pass2-def-stats.lsp" "pass2-def-report.txt")
  (assert (and (true-listp positions)
               (subsetp positions '(0 1 2))))
  (let* ((tuples (with-open-file (str infile :direction :input)
                   (let ((new-cons (cons nil nil))
                         (ans nil))
                     (loop (let ((val (read str nil new-cons)))
                             (if (eq val new-cons)
                                 (return ans)
                               (push val ans)))))))
         (tuples (sort tuples
                       #'(lambda (x y) (pos-order positions x y))))
         (total-defs (loop for x in tuples sum (cadr x)))
         (total-cert (loop for x in tuples sum (caddr x)))
         (total-percent (* (/ total-defs total-cert) 100.0)))
    (with-open-file (str outfile
                         :direction :output
                         :if-exists :supersede)
      (format
       str
       "~12,4f  = Total time in pass 2 definitions.~%~
        ~12,4f  = Total time in certification.~%~
        ~12,4f% = Percentage of certification time in pass 2 definitions.~%~
        ------------------------------~%~
        Times per book sorted by positions ~s are below.~%~
        Each tuple is as follows.~%~
        Position 0: Percentage of certification time in pass 2 definitions~%~
        Position 1: Time in pass 2 definitions~%~
        Position 2: Time for certification~%~
        Position 3: The book, where [name] abbreviates (:SYSTEM . \"name\")~%~
        ------------------------------~%"
       total-defs total-cert total-percent positions)
      (loop for tuple in tuples do
            (my-print-tuple str tuple)))))
