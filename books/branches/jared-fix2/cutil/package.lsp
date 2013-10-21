(in-package "ACL2")
(ld "std/package.lsp" :dir :system)

(defpkg "CUTIL" *std-pkg-symbols*)

(defmacro cutil::moved ()
  '(with-output
    :off (summary event)
    (make-event
     (progn$
      (cw "~%Warning: CUTIL has moved!  Please update your include-books ~
         to use std/util/* instead of cutil/*, and update uses of cutil:: ~
         to std::.  The cutil/ wrappers will be removed in a future ACL2 ~
         release.~%")
      '(value-triple :invisible))
     :check-expansion t)))

#!CUTIL
(defconst *cutil-exports*
  STD::*std-exports*)
