(in-package "ACL2")

(defpkg "ACL2S-INTERFACE-INTERNAL" *common-lisp-symbols-from-main-lisp-package*)

(defpkg "ACL2S-INTERFACE"
  (union-eq
   '(
     acl2s-interface-internal::get-captured-output
     acl2s-interface-internal::add-quiet-mode-on-hook
     acl2s-interface-internal::add-quiet-mode-off-hook
     acl2s-interface-internal::quiet-mode-on
     acl2s-interface-internal::quiet-mode-off
     acl2s-interface-internal::set-quiet-mode
     acl2s-interface-internal::capture-output-on
     acl2s-interface-internal::capture-output-off
     acl2s-interface-internal::set-capture-output
     acl2s-interface-internal::acl2s-compute
     acl2s-interface-internal::acl2s-query
     acl2s-interface-internal::acl2s-event
     acl2s-interface-internal::acl2s-interface
     acl2s-interface-internal::itest?-query
     )
   *common-lisp-symbols-from-main-lisp-package*))

(defpkg "ACL2S-INTERFACE-EXTRAS"
  (union-eq
   '(
     acl2s-interface-internal::get-prover-step-limit
     acl2s-interface-internal::get-captured-output
     acl2s-interface-internal::add-quiet-mode-on-hook
     acl2s-interface-internal::add-quiet-mode-off-hook
     acl2s-interface-internal::quiet-mode-on
     acl2s-interface-internal::quiet-mode-off
     acl2s-interface-internal::set-quiet-mode
     acl2s-interface-internal::capture-output-on
     acl2s-interface-internal::capture-output-off
     acl2s-interface-internal::set-capture-output
     acl2s-interface-internal::acl2s-compute
     acl2s-interface-internal::acl2s-query
     acl2s-interface-internal::acl2s-event
     acl2s-interface-internal::acl2s-interface
     acl2s-interface-internal::itest?-query
     )
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))
