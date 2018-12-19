; Memory Package Definition File

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "MEM"
  (union-eq '(signed-byte-p the-fixnum
              a b c d e f g h i j k l m n o p q r s t u v w x y z
              defxdoc defsection memory)
            (set-difference-eq
             (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*)
             '(load debug))))
