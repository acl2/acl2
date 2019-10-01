; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define macro-symbolp ((sym symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/event-name-queries)
  :short "Check if a symbol names a macro,
          i.e. it has a @('macro-args') property."
  :long
  (xdoc::topstring-p
   "This function is named in analogy to
    the @(tsee function-symbolp) built-in system utility.")
  (not (eq (getpropc sym 'macro-args t wrld) t))
  ///

  (defthm macro-symbolp-forward-to-symbolp
    (implies (and (macro-symbolp fn wrld)
                  (plist-worldp wrld))
             (symbolp fn))
    :rule-classes :forward-chaining))
