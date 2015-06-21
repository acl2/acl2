; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

(in-package "ACL2")

(make-event
 (prog2$
  (observation-cw
   'non-linear-arithmetic
   "To turn on non-linear arithmetic:~|~%~Y01"
   '(set-default-hints '((nonlinearp-default-hint
                          stable-under-simplificationp hist pspv)))
   nil)
  '(value-triple nil))
 :check-expansion t)
