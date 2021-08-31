; Turning off removal of trivial equivalences by the prover
;
; Copyright (C) 2018-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This is needed because ACL2 can get rid of a var that is known equal to
;; something else, which is a problem if a later hint (e.g., when stable under
;; simplification) will refer to the var that has been removed (the equality
;; will have also been removed and the hint's conditions may be impossible to
;; establish).  This event is always inherently local, because defattach-system
;; is.
(defmacro dont-remove-trivial-equivalences ()
  '(with-output
     :off :all
     (defattach-system (remove-trivial-equivalences-enabled-p constant-nil-function-arity-0))))
