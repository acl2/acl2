; Copyright (C) 2026, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Matt Kaufmann (matthew.j.kaufmann@gmail.com)

; The macro (bind-to-bool var) is useful as a hypothesis when var would
; otherwise be a free variable and we want to instantiate it to itself, 't, or
; 'nil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defmacro bind-to-bool (var)
  `(bind-free '(((,var . ,var)) ((,var . 't)) ((,var . 'nil)))))
