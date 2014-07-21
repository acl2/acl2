
(in-package "ACL2")

(ld "std/package.lsp" :dir :system)

(defpkg "FTY"
  (append *std-pkg-symbols*
          '(std::def-primitive-aggregate
             std::extract-keywords
             std::getarg)
          #!ACL2
          '(a b c d e f g h i j k l m n o p q r s t u v w x y z)))
          
