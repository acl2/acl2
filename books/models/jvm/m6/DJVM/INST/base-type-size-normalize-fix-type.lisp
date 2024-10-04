(in-package "DJVM")
(include-book "../../M6-DJVM-shared/jvm-class-table")
(include-book "../../DJVM/consistent-state-to-sig-state")
(include-book "base-valid-type-s")


(local 
 (encapsulate () 
              (defthm type-size-equal
                (implies (or (not (equal (car type) 'class))
                             (stringp (cadr type)))
                         (equal (type-size (normalize-type-rep type))
                                (type-size type)))
                :hints (("Goal" :in-theory (enable type-size
                                                   primitive-type?
                                                   array-type?
                                                   make-array-type
                                                   normalize-type-rep))))



              (defthm valid-type-s-mode-0-implies-car-fix-sig-array
                (implies (valid-type-s type cl 0)
                         (equal (car (fix-sig type)) 'ARRAY))
                :hints (("Goal" :in-theory (enable fix-sig primitive-type?
                                                   isarraytype
                                                   wff-array-type))))

              (defthm type-size-equal-lemma
                (implies (and (valid-type-strong type cl)
                              (equal (car (fix-sig type)) 'class))
                         (isClassTerm (class-by-name type cl)))
                :hints (("Goal" :in-theory (e/d (class-exists?
                                                 fix-sig
                                                 isarraytype
                                                 ARRAY-COMPONENT-TYPE
                                                 classname
                                                 wff-array-type
                                                 primitive-type?
                                                 class-loaded?)
                                                (isClassTerm)))))

              (defthm isClassTerm-implies-class-by-name
                (implies (isClassTerm (class-by-name type cl))
                         (class-by-name type cl))
                :rule-classes :forward-chaining)


              (encapsulate () 
                           (local (include-book "base-consistent-state-class-names-are-string"))
                           (defthm consistent-state-class-name-is-stringp
                             (implies (and (class-by-name name (instance-class-table s))
                                           (consistent-state s))
                                      (stringp name))
                             :rule-classes :forward-chaining))


              (defthm type-size-equal-lemma2
                (implies  (stringp type)
                          (EQUAL (TYPE-SIZE (FIX-SIG TYPE))
                                 (TYPE-SIZE TYPE)))
                :hints (("Goal" :in-theory (enable fix-sig type-size
                                                   primitive-type?))))

              (defthm valid-type-strong-implies-cadr-fix-sig
                (implies (and (valid-type-strong type cl)
                              (equal (car (fix-sig type)) 'class))
                         (equal (cadr (fix-sig type)) type))
                :hints (("Goal" :in-theory (e/d (fix-sig valid-type-strong
                                                         primitive-type?)
                                                ())
                         :expand (fix-sig type))))

              (defthm type-size-equal-when-class-type
                (implies (and (valid-type-strong type (instance-class-table s))
                              (consistent-state s)
                              (equal (car (fix-sig type)) 'class))
                         (equal (type-size (normalize-type-rep (fix-sig type)))
                                (type-size type)))
                :hints (("Goal" :in-theory (e/d (type-size) (normalize-type-rep
                                                             valid-type-strong
                                                             consistent-state
                                                             isClassTerm))
                         :use ((:instance consistent-state-class-name-is-stringp
                                          (name type))
                               (:instance type-size-equal-lemma
                                          (cl (instance-class-table s)))
                               (:instance isClassTerm-implies-class-by-name
                                          (cl (instance-class-table s)))
                               (:instance type-size-equal
                                          (type (fix-sig type)))
                               (:instance valid-type-strong-implies-cadr-fix-sig
                                          (cl (instance-class-table s)))))))


;;; not really thinking!! just want to get over it!! 
;;; Mon Jun 20 21:06:32 2005

              (defthm not-car-equal-class-primitive-type-or-array-type
                (implies (and (valid-type-strong type cl)
                              (not (equal (car (fix-sig type)) 'class))
                              (not (primitive-type? type)))
                         (isarraytype type)))


              (defthm isArrayType-type-size-equal
                (implies (isarraytype type)
                         (equal (type-size (normalize-type-rep (fix-sig type))) 1))
                :hints (("Goal" :in-theory (enable type-size primitive-type? 
                                                   fix-sig
                                                   isarraytype))))


              (defthm isArrayType-type-size-equal-2
                (implies (isarraytype type)
                         (equal (type-size type) 1))
                :hints (("Goal" :in-theory (enable type-size primitive-type? 
                                                   fix-sig
                                                   isarraytype))))


              (defthm primitive-type-fix-type-no-change
                (implies (primitive-type? type)
                         (equal (fix-sig type) type))
                :hints (("Goal" :in-theory (enable type-size primitive-type? 
                                                   fix-sig
                                                   isarraytype))))


              (defthm normalize-type-rep-type-no-change
                (implies (primitive-type? type)
                         (equal (normalize-type-rep type) type))
                :hints (("Goal" :in-theory (enable type-size primitive-type? 
                                                   fix-sig
                                                   isarraytype))))))




(defthm type-size-equal-specific
  (implies (and (consistent-state s)
                (valid-type-strong type (instance-class-table s)))
           (equal (type-size (normalize-type-rep (fix-sig type)))
                  (type-size type)))
  :hints (("Goal" :in-theory (e/d () (type-size 
                                      consistent-state
                                      normalize-type-rep
                                      valid-type-strong))
           :cases ((equal (car (fix-sig type)) 'class)))
          ("Subgoal 2" :cases ((primitive-type? type)))))

