(in-package "MILAWA")
:ubt! 1
(ACL2::include-book "../levels/level11" :ttags :all)
(ACL2::reset-prehistory)
:q
;; We get about a 1.5% speed improvement on rewriting by disabling
;; the ephemeral garabage collector on OpenMCL.
#+openmcl
(CCL::egc nil)
(ACL2::save-exec "../acl2-images/interface-acl2" "All tactics pre-loaded.")
