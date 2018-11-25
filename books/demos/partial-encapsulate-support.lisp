; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; This handy book makes it easy to redefine a function in raw Lisp after a
; trust tag is introduced.
(include-book "tools/include-raw" :dir :system)

; We introduce a constrained function that is intended to be a rational
; approximation to the natural log function.  Note that supporters = nil: this
; is fine, since each implicit constraint equates a call of ln-constrained on
; explicit arguments with its result.
(partial-encapsulate
 (((ln-constrained *) => *))
 nil ; supporters (see the comment above)
 (local (defun ln-constrained (x)
          x))
 (defthm ln-monotone-on-positives
   (implies (and (real/rationalp x)
                 (real/rationalp y)
                 (<= x y))
            (<= (ln-constrained x)
                (ln-constrained y)))))

; Now we introduce a little wrapper for the function above.  Note that ACL2
; will refuse to execute explicit calls of ln-constrained, because it is a
; constrained function.  This wrapper gets around that problem.
(defun ln (x)
  (declare (xargs :guard (and (real/rationalp x)
                              (< 0 x))))
  (ln-constrained x))

; Now we define a macro that smashes the definition of ln-constrained in raw
; Lisp, by calling the Common Lisp natural log function, log.  See
; partial-encapsulate-support-raw.lsp.
(defmacro install-ln ()
  `(progn (defttag :partial-encap-ex)
          (include-raw "partial-encapsulate-support-raw.lsp")))
