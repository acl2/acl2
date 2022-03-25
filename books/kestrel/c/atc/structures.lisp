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
(include-book "tag-environments")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-structures
  :parents (atc-dynamic-semantics)
  :short "A model of C structures for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a model of structures (i.e. values of structure types).
     A structure is modeled as consisting of a tag
     and of a sequence of named members.
     For now each member has one of the values in @(tsee value),
     i.e. either an integer value or a pointer value."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod member
  :short "Fixtype of structure members."
  :long
  (xdoc::topstring
   (xdoc::p
    "A member consists of a name and a value."))
  ((name ident)
   (value value))
  :tag :member
  :pred memberp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist member-list
  :short "Fixtype of lists of structure members."
  :elt-type member
  :true-listp t
  :elementp-of-nil nil
  :pred member-listp)

;;;;;;;;;;;;;;;;;;;;

(std::defprojection member-list->name-list (x)
  :guard (member-listp x)
  :returns (names ident-listp)
  :short "Lift @(tsee member->name) to lists."
  (member->name x)
  ///
  (fty::deffixequiv member-list->name-list
    :args ((x member-listp))))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection member-list->value-list (x)
  :guard (member-listp x)
  :returns (values value-listp)
  :short "Lift @(tsee member->value) to lists."
  (member->value x)
  ///
  (fty::deffixequiv member-list->value-list
    :args ((x member-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult member-list "lists of structure members")

;;;;;;;;;;;;;;;;;;;;

(defruled not-errorp-when-member-listp
  (implies (member-listp x)
           (not (errorp x)))
  :enable (member-listp errorp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod struct
  :short "Fixtype of structures [C:6.2.5/20]."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be at least one member.
     The members must have distinct names.
     These requirements are currently not captured in this fixtype."))
  ((tag ident)
   (members member-list))
  :tag :struct
  :pred structp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult struct "structures")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-read-member ((struct structp) (name identp))
  :returns (val value-resultp)
  :short "Read a member of a structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look up the members in order;
     given that the members have distinct names (see @(tsee struct),
     the search order is immaterial."))
  (struct-read-member-aux (struct->members struct) name)
  :hooks (:fix)

  :prepwork
  ((define struct-read-member-aux ((members member-listp) (name identp))
     :returns (val value-resultp)
     :parents nil
     (b* (((when (endp members))
           (error (list :member-not-found (ident-fix name))))
          ((member member) (car members))
          ((when (equal member.name (ident-fix name)))
           member.value))
       (struct-read-member-aux (cdr members) name))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-write-member ((struct structp) (name identp) (val valuep))
  :returns (new-struct struct-resultp)
  :short "Write a member of a structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look up the members in order;
     given that the members have distinct names (see @(tsee struct)),
     the search order is immaterial.
     The new value must have the same type as the old value."))
  (b* ((new-members (struct-write-member-aux (struct->members struct) name val))
       ((when (errorp new-members)) new-members))
    (change-struct struct :members new-members))
  :hooks (:fix)

  :prepwork
  ((define struct-write-member-aux ((members member-listp)
                                    (name identp)
                                    (val valuep))
     :returns (new-members
               member-list-resultp
               :hints
               (("Goal"
                 :in-theory
                 (enable
                  member-listp-when-member-list-resultp-and-not-errorp))))
     :parents nil
     (b* (((when (endp members))
           (error (list :member-not-found (ident-fix name))))
          ((member member) (car members))
          ((when (equal member.name (ident-fix name)))
           (if (equal (type-of-value member.value)
                      (type-of-value val))
               (cons (make-member :name name :value val)
                     (member-list-fix (cdr members)))
             (error (list :mistype-member (ident-fix name)
                          :old-value member.value
                          :new-value (value-fix val)))))
          (new-cdr-members (struct-write-member-aux (cdr members) name val))
          ((when (errorp new-cdr-members)) new-cdr-members))
       (cons (member-fix (car members))
             new-cdr-members))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define member-to-info ((member memberp))
  :returns (meminfo member-infop)
  :short "Turn a member into its information."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @(tsee member-info) is the static counterpart of a @(tsee member)."))
  (make-member-info :name (member->name member)
                    :type (type-of-value (member->value member)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection members-to-infos (x)
  :guard (member-listp x)
  :returns (infos member-info-listp)
  :short "Lift @(tsee member-to-info) to lists."
  (member-to-info x)
  ///
  (fty::deffixequiv members-to-infos
    :args ((x member-listp))))
