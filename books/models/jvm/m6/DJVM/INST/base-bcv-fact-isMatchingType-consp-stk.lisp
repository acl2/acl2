(in-package "BCV")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")

(include-book "base-bind-free")

(local 
 (defthm isMatchingType-consp
    (implies (and (bcv::isMatchingType type stk env)
                  type)
             (consp stk))
    :hints (("Goal" :in-theory (enable bcv::isMatchingType)))
    :rule-classes :forward-chaining))


(defthm isMatchingType-consp-b-INT
  (implies (and (bind-free (acl2::default-bind-free 'env 'env1
                                                    (acl2::pkg-witness "DJVM"))
                           (env))
                (bcv::isMatchingType 'INT stk env))
           (consp stk)))



(defthm isMatchingType-consp-b-AARRAY
  (implies (and (bind-free (acl2::default-bind-free 'env 'env1
                                                    (acl2::pkg-witness "DJVM"))
                           (env))
                (bcv::isMatchingType '(array (class "java.lang.Object")) stk env))
           (consp stk)))



(defthm isMatchingType-consp-b-java-lang-Object
  (implies (and (bind-free (acl2::default-bind-free 'env 'env1
                                                    (acl2::pkg-witness "DJVM"))
                           (env))
                (bcv::isMatchingType '(class "java.lang.Object") stk env))
           (consp stk)))
;----------------------------------------------------------------------


(defthm isMatchingType-consp-b-REFERENCE
  (implies (and (bind-free (acl2::default-bind-free 'env 'env1
                                                    (acl2::pkg-witness "DJVM"))
                           (env))
                (bcv::isMatchingType 'REFERENCE stk env))
           (consp stk)))
