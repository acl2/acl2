(in-package "DJVM")
(include-book "base")


(local (include-book "base-consistent-object-m6-getfield"))

;; (i-am-here) ;; Thu Jul 21 16:58:01 2005




;; (local 
;;  (defthm search-field-field-type-equal-get-field-type
;;   (implies (and (searchfields field-ptr fields)
;;                 (equal (field-ptr-fieldname field-ptr)
;;                        fieldname))
;;            (equal (get-field-type1 fieldname fields)
;;                   (field-fieldtype 
;;   :hints (("Goal" :do-not '(generalize)))))

;;
;; the difficulty lies in the fact that search field search for the exact match
;; however get-field-type1 looks for the first match!! 
;;


(local 
 (defthm get-field-type1-is-fieldtype-field-decl-with-name
   (equal (get-field-type1 fieldname field-decls)
          (field-fieldtype (field-decl-with-name fieldname field-decls)))))



(local 
 (encapsulate ()
   (local (include-book "base-consistent-object-m6-getfield"))
   (defthm field-decl-with-name-equal-lookupfield-specific
     (implies (and (lookupfield (fieldcp-to-field-ptr fieldcp) s)
                   (consistent-state s))
           (EQUAL
            (FIELD-DECL-WITH-NAME
             (fieldcp-fieldname fieldcp)
             (FIELDS (CLASS-BY-NAME
                      (FIELD-CLASSNAME (LOOKUPFIELD (fieldcp-to-field-ptr fieldcp) s))
                      (INSTANCE-CLASS-TABLE S))))
            (LOOKUPFIELD (fieldcp-to-field-ptr fieldcp) s))))))




(local 
 (encapsulate () 
   (local (include-book "base-lookupfield-fieldname-normalize"))
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
              :do-not '(generalize))))))

(local 
 (defthm field-ptr-type-fieldcp-to-ptr
   (equal (field-ptr-type (fieldcp-to-field-ptr fieldcp))
          (fieldcp-fieldtype fieldcp))
   :hints (("Goal" :in-theory (enable fieldcp-to-field-ptr fieldcp-to-field-ptr
                                      make-field-ptr
                                      field-ptr-type)))))





(defthm lookupfield-field-type-equal
  (implies (and (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp) S)
                (consistent-state s))
           (equal (get-field-type 
                   (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                 S))
                   (fieldcp-fieldname fieldcp)
                   (instance-class-table s))
                  (fieldcp-fieldtype fieldcp)))
  :hints (("Goal" :in-theory (disable lookupfield 
                                      field-classname
                                      fieldcp-classname
                                      FIELDCP-TO-FIELD-PTR
                                      field-fieldtype
                                      fields
                                      fieldcp-fieldtype
                                      fieldcp-fieldname
                                      get-field-type1))))
                                      

