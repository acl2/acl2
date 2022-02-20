; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(program)

(defun preceding-theory-fn (logical-name wrld)

; This definition is based on that of ACL2 source function current-theory-fn.

; Warning: Keep this in sync with union-current-theory-fn and
; set-difference-current-theory-fn.

; We return the theory that was enabled in the world created by the
; event immediately preceding that introduced by logical-name.

  (let ((wrld1 (decode-logical-name logical-name wrld)))
    (prog2$
     (or wrld1
         (er hard 'current-theory
             "The name ~x0 was not found in the current ACL2 logical ~
              world; hence no current-theory can be computed for that name."
             logical-name))
     (let ((wrld2 (scan-to-event (cdr wrld1))))
       (current-theory-fn1 wrld2 wrld)))))

(defmacro preceding-theory (name &optional (world 'world))
; This gives the current-theory as of the immediately preceding event.
  (list 'preceding-theory-fn name world))
