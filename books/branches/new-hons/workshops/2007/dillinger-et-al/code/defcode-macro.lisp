#|$ACL2s-Preamble$;
(include-book "hacker")

(acl2::begin-book t :ttags ((defcode)));$ACL2s-Preamble$|#

; NOTE: this should only be included by defcode.lisp.  this is a
; separate book only because of wacky compilation issues.

(in-package "ACL2")

(program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; defcode macro
;
; to facilitate future incorporation into ACL2, this should directly
; defer to defcode-fn (but through a progn! for now, so that it is an
; embedded event).

(defmacro defcode (&whole event-form &key loop extend retract compile)
  (declare (ignore compile))
  `(progn!
    (defcode-fn ',loop
                ',extend
                ',retract
                state
                ',event-form)))

(defttag defcode)

(in-raw-mode
 (defmacro defcode (&whole event-form &key loop extend retract compile)
   (declare (ignore loop extend retract event-form))
   (if (and (consp compile)
            (consp (car compile))
            (not (eq 'lambda (caar compile))))
     `(progn . ,compile)
     compile)))
