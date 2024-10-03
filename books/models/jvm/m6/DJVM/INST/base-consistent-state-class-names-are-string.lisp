(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")


(local 
 (defthm consistent-class-decls-implies-stringp
   (implies (and (consistent-class-decls cl1 cl hp)
                 (wff-instance-class-table cl1)
                 (class-by-name name cl1))
            (stringp name))
   :hints (("Goal" :in-theory (enable consistent-class-decl)))
   :rule-classes :forward-chaining))


(defthm consistent-state-class-name-is-stringp
  (implies (and (class-by-name name (instance-class-table s))
                (consistent-state s))
           (stringp name))
  :rule-classes :forward-chaining)
