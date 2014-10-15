; define-u-package -- the package for utilities
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com) and Bishop Brock
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(defpkg "U" (union-eq *acl2-exports*
		      *common-lisp-symbols-from-main-lisp-package*))
