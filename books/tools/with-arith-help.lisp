; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book supports the use of with-arith1-help and also the use of
; with-arith5-help.

(in-package "ACL2")

(include-book "rulesets")
(include-book "with-arith5-help")
(include-book "with-arith1-help")

(defun allow-arith-help-fn (world)
  (cond
   ((check-for-arith1-rulesets world)
    (cond
     ((check-for-arith5-rulesets world)
      '(value-triple :redundant-allow-arith-help))
     (t *allow-arith5-help-form*)))
   ((check-for-arith5-rulesets world)
    *allow-arith5-help-form*)
   (t ; define both rulesets
    `(local
      (progn
        ,*allow-arith1-help-form*
        ,*allow-arith5-help-form*
        (include-book "arithmetic/top-with-meta" :dir :system)
        (in-theory (current-theory 'before-including-arithmetic-1)))))))

(defmacro allow-arith-help ()
  '(make-event (allow-arith-help-fn (w state))))
