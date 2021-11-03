; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pos-list
  :parents (fty::fty-extensions fty::specific-types pos-listp)
  :short "Fixtype of lists of positive integers."

  ;; We put the DEFLIST in a DEFSECTION to avoid generating
  ;; an XDOC for POS-LISTP, which would shadow the built-in one.

  (fty::deflist pos-list
    :elt-type pos
    :true-listp t
    :elementp-of-nil nil
    :pred pos-listp))
