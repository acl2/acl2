;; Cuong Chau <ckcuong@cs.utexas.edu>

;; ======================================================================

(defpkg "ADE"
  (union-eq
   '(a b c d e f g h i j k l m n o p q r s t u v w x y z

       add-to-ruleset

       b*
       bash
       bash-fn
       bool-fix

       def-gl-thm
       def-ruleset
       define
       definline
       disable*

       e/d*
       enable*
       explode

       find-lemmas

       include-raw

       list-fix
       logext

       make-flag
       make-list-ac-removal

       nonlinearp-default-hint

       pos-listp
       prefixp
       prefixp-of-cons-left
       prefixp-when-equal-lengths
       proof-by-arith

       repeat
       rev

       signed-byte-p
       suffixp

       take-of-len-free
       take-of-take-split
       take-of-too-many
       take-redefinition

       unsigned-byte-p

       zp-open)

   (union-eq *acl2-exports*
	     *common-lisp-symbols-from-main-lisp-package*)))

;; ======================================================================
