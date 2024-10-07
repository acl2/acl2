(in-package "DJVM")
(include-book "base")
(include-book "base-skip-proofs")

(skip-proofs 
 (defthm consistent-state-not-method-native-topstackguard-implies-wff-instrs
   (implies (consistent-state s)
            (wff-insts (method-code (current-method s))))))


(skip-proofs 
 (defthm consistent-state-not-method-native-topstackguard-implies-wff-code
   (implies (consistent-state s)
            (WFF-CODE (METHOD-CODE (DEREF-METHOD (CURRENT-METHOD-PTR S)
                                                 (INSTANCE-CLASS-TABLE S)))))))

  