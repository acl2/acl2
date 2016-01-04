; Memory Package Definition File

(defpkg "MEM"
  (union-eq '(signed-byte-p the-fixnum
              a b c d e f g h i j k l m n o p q r s t u v w x y z
              defxdoc defsection memory)
            (set-difference-eq
             (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*)
             '(load debug))))
