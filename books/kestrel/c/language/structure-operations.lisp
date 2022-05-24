; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ structure-operations
  :parents (language)
  :short "Some operations on C structures."
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
     given that the members have distinct names (see @(tsee value),
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
     :hooks (:fix))))

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
     The new value must have the same type as the old value."))
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
               (cons (make-member-value :name name :value val)
                     (member-value-list-fix (cdr members)))
             (error (list :mistype-member (ident-fix name)
                          :old-value member.value
                          :new-value (value-fix val)))))
          (new-cdr-members (value-struct-write-aux name val (cdr members)))
          ((when (errorp new-cdr-members)) new-cdr-members))
       (cons (member-value-fix (car members))
             new-cdr-members))
     :hooks (:fix)))

  ///

  (defret value-kind-of-value-struct-write
    (implies (not (errorp new-struct))
             (equal (value-kind new-struct)
                    :struct))))
