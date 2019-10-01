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

(define theorem-symbolp ((sym symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/event-name-queries)
  :short "Check if a symbol names a theorem,
          i.e. it has a @('theorem') property."
  :long
  (xdoc::topstring-p
   "This function is named in analogy to
    the @(tsee function-symbolp) built-in system utility.")
  (not (eq (getpropc sym 'theorem t wrld) t))
  ///

  (defthm theorem-symbolp-forward-to-symbolp
    (implies (and (theorem-symbolp fn wrld)
                  (plist-worldp wrld))
             (symbolp fn))
    :rule-classes :forward-chaining))
