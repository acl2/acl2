; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "values")
(include-book "flexible-array-member-removal")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ structure-operations
  :parents (language)
  :short "Operations on C structures."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-struct-read ((name identp) (struct valuep))
  :guard (value-case struct :struct)
  :returns (val value-resultp)
  :short "Read a member of a structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look up the members in order;
     given that the members have distinct names (see @(tsee value)),
     the search order is immaterial."))
  (value-struct-read-aux name (value-struct->members struct))
  :hooks (:fix)

  :prepwork
  ((define value-struct-read-aux ((name identp) (members member-value-listp))
     :returns (val value-resultp)
     :parents nil
     (b* (((when (endp members))
           (error (list :member-not-found (ident-fix name))))
          ((member-value member) (car members))
          ((when (equal member.name (ident-fix name)))
           member.value))
       (value-struct-read-aux name (cdr members)))
     :hooks (:fix)

     ///

     (defruled value-struct-read-aux-when-member-type-lookup
       (implies (equal memtypes (member-types-of-member-values memvals))
                (b* ((type (member-type-lookup name memtypes))
                     (val (value-struct-read-aux name memvals)))
                  (implies (typep type)
                           (and (valuep val)
                                (equal (type-of-value val)
                                       type)))))
       :prep-lemmas
       ((defrule lemma
          (b* ((type (member-type-lookup name
                                         (member-types-of-member-values memvals)))
               (val (value-struct-read-aux name memvals)))
            (implies (typep type)
                     (and (valuep val)
                          (equal (type-of-value val)
                                 type))))
          :induct t
          :enable (value-struct-read-aux
                   member-type-lookup
                   member-types-of-member-values
                   member-type-of-member-value)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-struct-write ((name identp) (val valuep) (struct valuep))
  :guard (value-case struct :struct)
  :returns (new-struct value-resultp)
  :short "Write a member of a structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look up the members in order;
     given that the members have distinct names (see @(tsee value)),
     the search order is immaterial.
     The new value must have the same type as the old value.")
   (xdoc::p
    "Prior to storing the value, we remove its flexible array member, if any.
     See @(tsee remove-flexible-array-member)."))
  (b* ((new-members
        (value-struct-write-aux name val (value-struct->members struct)))
       ((when (errorp new-members)) new-members))
    (change-value-struct struct :members new-members))
  :hooks (:fix)

  :prepwork
  ((define value-struct-write-aux ((name identp)
                                   (val valuep)
                                   (members member-value-listp))
     :returns
     (new-members
      member-value-list-resultp
      :hints
      (("Goal"
        :induct t
        :in-theory
        (enable
         member-value-listp-when-member-value-list-resultp-and-not-errorp))))
     :parents nil
     (b* (((when (endp members))
           (error (list :member-not-found (ident-fix name))))
          ((member-value member) (car members))
          ((when (equal member.name (ident-fix name)))
           (if (equal (type-of-value member.value)
                      (type-of-value val))
               (cons (make-member-value
                      :name name
                      :value (remove-flexible-array-member val))
                     (member-value-list-fix (cdr members)))
             (error (list :mistype-member (ident-fix name)
                          :old-value member.value
                          :new-value (value-fix val)))))
          (new-cdr-members (value-struct-write-aux name val (cdr members)))
          ((when (errorp new-cdr-members)) new-cdr-members))
       (cons (member-value-fix (car members))
             new-cdr-members))
     :hooks (:fix)

     ///

     (defruled member-value-listp-of-value-struct-write-aux
       (b* ((old (value-struct-read-aux name memvals))
            (memvals1 (value-struct-write-aux name new memvals)))
         (implies (and (valuep old)
                       (equal (type-of-value new)
                              (type-of-value old)))
                  (member-value-listp memvals1)))
       :induct t
       :enable value-struct-read-aux)

     (defruled member-value-list->name-list-of-struct-write-aux
       (b* ((old (value-struct-read-aux name memvals))
            (memvals1 (value-struct-write-aux name new memvals)))
         (implies (and (valuep old)
                       (equal (type-of-value new)
                              (type-of-value old)))
                  (equal (member-value-list->name-list memvals1)
                         (member-value-list->name-list memvals))))
       :induct t
       :enable value-struct-read-aux)

     (defruled value-struct-read-aux-of-value-struct-write-aux
       (b* ((old (value-struct-read-aux name memvals))
            (memvals1 (value-struct-write-aux name new memvals)))
         (implies (and (valuep old)
                       (equal (type-of-value new)
                              (type-of-value old)))
                  (equal (value-struct-read-aux name1 memvals1)
                         (if (ident-equiv name1 name)
                             (remove-flexible-array-member new)
                           (value-struct-read-aux name1 memvals)))))
       :induct t
       :enable value-struct-read-aux)

     (defruled value-struct-write-aux-when-member-type-lookup
       (implies (equal memtypes (member-types-of-member-values memvals))
                (b* ((type (member-type-lookup name memtypes))
                     (new-memvals (value-struct-write-aux name val memvals)))
                  (implies (and (typep type)
                                (valuep val)
                                (equal (type-of-value val)
                                       type))
                           (and (member-value-listp new-memvals)
                                (equal (member-types-of-member-values new-memvals)
                                       memtypes)))))
       :prep-lemmas
       ((defrule lemma
          (b* ((type (member-type-lookup name
                                         (member-types-of-member-values memvals)))
               (new-memvals (value-struct-write-aux name val memvals)))
            (implies (and (typep type)
                          (valuep val)
                          (equal (type-of-value val)
                                 type))
                     (and (member-value-listp new-memvals)
                          (equal (member-types-of-member-values new-memvals)
                                 (member-types-of-member-values memvals)))))
          :induct t
          :enable (value-struct-write-aux
                   member-type-lookup
                   member-types-of-member-values
                   member-type-of-member-value))))

     (defruled not-errorp-of-value-struct-read-aux-when-not-write-error
       (implies (not (errorp (value-struct-write-aux name val members)))
                (not (errorp (value-struct-read-aux name members))))
       :induct t
       :enable value-struct-read-aux)))

  ///

  (defret value-kind-of-value-struct-write
    (implies (not (errorp new-struct))
             (equal (value-kind new-struct)
                    :struct)))

  (defruled valuep-of-value-struct-write
    (b* ((old (value-struct-read name struct))
         (struct1 (value-struct-write name new struct)))
      (implies (and (valuep old)
                    (equal (type-of-value new)
                           (type-of-value old)))
               (valuep struct1)))
    :enable (value-struct-read
             member-value-listp-of-value-struct-write-aux))

  (defruled value-struct-read-of-value-struct-write
    (b* ((old (value-struct-read name struct))
         (struct1 (value-struct-write name new struct)))
      (implies (and (valuep old)
                    (equal (type-of-value new)
                           (type-of-value old)))
               (equal (value-struct-read name1 struct1)
                      (if (ident-equiv name1 name)
                          (remove-flexible-array-member new)
                        (value-struct-read name1 struct)))))
    :enable (value-struct-read
             value-struct-read-aux-of-value-struct-write-aux))

  (defruled not-errorp-of-value-struct-read-when-not-write-error
    (implies (not (errorp (value-struct-write name val struct)))
             (not (errorp (value-struct-read name struct))))
    :enable (value-struct-write
             value-struct-read
             not-errorp-of-value-struct-read-aux-when-not-write-error)))
