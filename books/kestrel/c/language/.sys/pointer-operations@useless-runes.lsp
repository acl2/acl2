(C::VALUE-POINTER-NULL)
(C::VALUEP-OF-VALUE-POINTER-NULL)
(C::VALUE-KIND-OF-VALUE-POINTER-NULL)
(C::VALUE-POINTER-NULL-OF-TYPE-FIX-REFTYPE)
(C::VALUE-POINTER-NULL-TYPE-EQUIV-CONGRUENCE-ON-REFTYPE)
(C::VALUE-POINTER-NULLP)
(C::BOOLEANP-OF-VALUE-POINTER-NULLP)
(C::VALUE-POINTER-NULLP-OF-VALUE-FIX-PTR
 (10 1 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (5 1 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::VALUEP))
 (2 2 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (2 2 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (2 1 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 )
(C::VALUE-POINTER-NULLP-VALUE-EQUIV-CONGRUENCE-ON-PTR)
(C::VALUE-POINTER->DESIGNATOR
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 )
(C::OBJDESIGNP-OF-VALUE-POINTER->DESIGNATOR)
(C::VALUE-POINTER->DESIGNATOR-OF-VALUE-FIX-PTR)
(C::VALUE-POINTER->DESIGNATOR-VALUE-EQUIV-CONGRUENCE-ON-PTR)