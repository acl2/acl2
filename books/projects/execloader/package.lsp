(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/defrstobj2/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)

(defpkg "EXLD"
  (union-eq
   '(
     binary-logand
     binary-logior
     binary-logxor

     ;; TOOLS
     fty::defprod
     b*
     def-ruleset
     def-ruleset!
     add-to-ruleset
     ruleset-theory
     enable*
     disable*
     e/d*
     ;; XDOC
     defsection
     defxdoc
     top
     el ; so that top-level :doc topic is also in "ACL2" package

     a b c d e f g h i j k l m n o p q r s t u v w x y z

     str::hexify
     str::cat
     str::natstr

     acl2::byte-listp
     acl2::ubyte64p)
   
   (union-eq *acl2-exports*
             acl2::*bitops-exports*
             std::*std-exports*             
             *common-lisp-symbols-from-main-lisp-package*)))

#!EXLD
(defconst *exld-exports*
  '(elf
    populate-elf
    mach-o
    populate-mach-o))

;; ----------------------------------------------------------------------
