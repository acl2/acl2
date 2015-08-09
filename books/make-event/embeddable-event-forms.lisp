; Started by David Rager; extended by Matt Kaufmann and anyone else who cares to
; do so.

(in-package "ACL2")

(defmacro assign$ (name value)
  `(with-output
    :off summary
    (make-event (pprogn (f-put-global
                         (quote ,name)
                         ,value
                         state)
                        (value '(value-triple nil))))))

(defmacro cw$ (comment)
  `(value-triple (cw ,comment)))

(defmacro observe$ (&rest args)
  `(with-output
    :off summary
    (make-event (pprogn (observation 'top-level ,@args)
                        (value '(value-triple :invisible))))))
