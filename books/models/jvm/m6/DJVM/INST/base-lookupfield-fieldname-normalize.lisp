(in-package "DJVM")
(include-book "../../M6-DJVM-shared/jvm-linker")
(include-book "../../M6-DJVM-shared/jvm-class-table")




(local 
  (defthm field-fieldname-search-fields
    (implies (searchfields field-ptr fields)
             (equal (field-fieldname (searchfields field-ptr fields))
                    (field-ptr-fieldname field-ptr)))))



(defthm field-fieldname-reduce
  (implies (LOOKUPFIELD field-ptr s)
           (equal (FIELD-FIELDNAME (LOOKUPFIELD field-ptr s))
                  (field-ptr-fieldname field-ptr)))
  :hints (("Goal" :in-theory (e/d (lookupfield) (LOOKUPFIELD-INV
                                                 searchfields 
                                                 fields
                                                 field-fieldname 
                                                 isClassTerm
                                                 superclass-no-loop))
           :do-not '(generalize))))





(local 
  (defthm field-fieldtype-search-fields
    (implies (searchfields field-ptr fields)
             (equal (field-fieldtype (searchfields field-ptr fields))
                    (field-ptr-type field-ptr)))))




(defthm field-fieldtype-reduce
  (implies (LOOKUPFIELD field-ptr s)
           (equal (FIELD-FIELDTYPE (LOOKUPFIELD field-ptr s))
                  (field-ptr-type field-ptr)))
  :hints (("Goal" :in-theory (e/d (lookupfield) (LOOKUPFIELD-INV
                                                 searchfields 
                                                 fields
                                                 field-fieldtype
                                                 isClassTerm
                                                 superclass-no-loop))
           :do-not '(generalize))))