; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/computation-states")
(include-book "../symbolic-computation-states")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-object-designator-rules
  :short "Rules about object designators."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only need the following rule,
     in order to handle access to static objects.
     We need to reduce @(tsee objdesign-of-var),
     which arises when opening @(tsee exec-ident),
     to the object designator of the static object,
     under the hypothesis that
     @(tsee read-static-var) on that variable yields a value
     and that the variable is not in automatic storage."))

  (defruled objdesign-of-var-when-static
    (implies (and (valuep (read-static-var id compst))
                  (not (var-autop id compst)))
             (equal (objdesign-of-var id compst)
                    (objdesign-static id)))
    :enable (objdesign-of-var
             var-autop
             read-static-var)
    :disable omap::in-when-in-tail
    :prep-lemmas
    ((defrule lemma
       (iff (objdesign-of-var-aux var frame scopes)
            (var-in-scopes-p var scopes))
       :induct t
       :enable (objdesign-of-var-aux
                var-in-scopes-p))))

  (defval *atc-object-designator-rules*
    '(objdesign-of-var-when-static
      objdesignp-of-objdesign-of-var-when-valuep-of-read-var)))
