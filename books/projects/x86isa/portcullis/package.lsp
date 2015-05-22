;; Shilpi Goel
;; ======================================================================

(in-package "ACL2")

(include-book "centaur/bitops/portcullis" :dir :system)

(defpkg "X86ISA"
  (union-eq
   '(
     binary-logand
     binary-logior
     binary-logxor

     ;; Commenting out letters g and s to avoid name clashes, for
     ;; e.g., acl2::g and x86isa::g would refer to the same function
     ;; in x86isa/portcullis/records-0.lisp, which would have name
     ;; clashes with the function acl2::g in misc/records.lisp.

     a b c d e f 
     ;; g 
     h i j k l m n o p q r 
     ;; s 
     t u v w x y z
     lst

     definline
     def-gl-thm
     b*
     include-raw

     ;; STD
     define
     defconsts
     defrule
     defruled

     ;; XDOC
     defsection
     defxdoc
     top

     ;; TOOLS
     defprod
     def-ruleset
     def-ruleset!
     add-to-ruleset
     ruleset-theory
     enable*
     disable*
     e/d*

     x86isa ; so that top-level :doc topic is also in "ACL2" package

     )
   (union-eq *acl2-exports*
             *bitops-exports*
             *common-lisp-symbols-from-main-lisp-package*)))

;; ======================================================================
