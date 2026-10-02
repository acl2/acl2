; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection msg-fixtype
  :parents (fty::fty-extensions fty::specific-types message-utilities)
  :short "Fixtype of messages."
  :long
  (xdoc::topstring-p
   "The recognizer is @(tsee msgp)
    and the fixer is @('msg-fix').")

  (fty::deffixtype msg
    :pred msgp
    :fix msg-fix
    :equiv msg-equiv
    :define t
    :forward t))
