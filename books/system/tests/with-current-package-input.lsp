; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; There are some calls made to cw, which prints to *standard-co*.  So we
; redefine that ouptut channel to be the current value of 'standard-co.

(redef+)
(make-event `(defconst *standard-co* ',(standard-co state)))
(redef-)

;;;;;;;;;;

; prints ACL2::ABCD
(with-current-package
 "ACL2-USER"
 (value (cw "~x0~%" 'abcd)))

; prints DEFUN
(with-current-package
 "ACL2-USER"
 (value (cw "~x0~%" 'defun)))

; prints COMMON-LISP::DEFUN
(with-current-package
 "ACL2-USER"
 (er-progn (set-current-package "ACL2-PC" state)
           (value (cw "~x0~%" 'defun))))

; error
(with-current-package
 "FOO" ; undefined
 (er-progn (set-current-package "ACL2-PC" state)
           (value (cw "~x0~%" 'defun))))

; prints ACL2::ABCD
(with-current-package
 "MY-PKG"
 (value (cw "~x0~%" 'abcd)))

;;;;;;;;;;

; Eliminate the redefinition to avoid certify-book failure due to redefinition,
; and which also restores *standard-co* to its original value so that we don't
; get an error from attempting to close it.  But leave identical-files-p
; defined.
(ubt 2)
