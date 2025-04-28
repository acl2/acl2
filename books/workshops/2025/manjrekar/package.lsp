(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "rtl/rel11/portcullis" :dir :system)

(defpkg "COMPRESS"
  (union-eq
   (set-difference-eq *acl2-exports*
; Matt K. mod: sum$ is defined in books/projects/curve25519/.
                      '(sum$))
   *common-lisp-symbols-from-main-lisp-package*
   (remove1-equal 'std::deflist STD::*std-exports*)
   '(local-defun local-defund local-defthm local-defthmd local-in-theory
     defxdoc defsection
     rtl                   ; simplifies dealing with this xdoc topic name
     *default-step-limit*  ; should perhaps be in *acl2-exports*
     binary-logand binary-logior binary-logxor binary-logeqv ; used in lib/log.lisp
     b*
     pseudo-term-substp
     symbol-fix
     def-meta-extract
     fn-get-def
     flambda-applicationp
     ffn-symb
     lambda-formals
     lambda-body
     fargs
     match-tree-opener-theory
     match-tree-alist-opener-theory
     match-tree-alist
     match-tree
     match-tree-binders
     match-tree-!vars
     match-tree-initial-alist-term
     match-tree-obj-equals-subst-when-successful
     match-tree-obj-equals-subst-and-open-when-successful
     patbind-assocs
     prefix-?-vars
     disjoin
     conjoin-clauses
     clauses-result
     rtl::ag
     rtl::as
     rtl::add-3
     rtl::arith-5-for-rtl
     rtl::bits-plus-mult-2-meta
     rtl::bits-bits-sum
     rtl::bitn-bits
     rtl::bitn-plus-bits
     rtl::bits-plus-bits
     rtl::bits-bits
     rtl::bitn-cat
     rtl::bitn-logand
     rtl::bitn-logior
     rtl::bitn-logxor
     rtl::if1
     rtl::setbitn
     rtl::setbits
     rtl::bitn
     rtl::bits
     fty::deffixtype
     fty::deftagsum
     fty::defprod
     fty::deflist
     fty::defoption
     const-fns-gen
     expand-reduce-cp
     alt-const-fns-gen
     def-gl-rule
     def-gl-thm
     defundd
     find-lemmas
     loop-fns-gen
     nonlinearp-default-hint
     nonlinearp-default-hint++
     proof-by-arith
     a b c d e f g h i j k l m n o p q r s t u v w x y z
     a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1
     n1 o1 p1 q1 r1 s1 t1 u1 v1 w1 x1 y1 z1
     a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 m2
     n2 o2 p2 q2 r2 s2 t2 u2 v2 w2 x2 y2 z2)))
