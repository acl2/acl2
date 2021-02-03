; JSON Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (json)
  :short "An abstract syntax of JSON."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define fixtypes for an abstract syntax of JSON.
     This is just a first version;
     we plan to make this more rich and precise."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes values
  :short "Fixtypes of JSON values."
  :long
  (xdoc::topstring
   (xdoc::p
    "A JSON value is
     an object,
     an array,
     a number,
     a string,
     @('true'),
     @('false'), or
     @('null').")
   (xdoc::p
    "We model an object as a list of members,
     where a member consists of a name and a value.
     For now we use ACL2 strings for the names, which are ISO-8859-1;
     JSON allows Unicode here,
     so we may generalize this aspect of our JSON abstract syntax in the future.
     Despite the recommendation of avoiding members with the same name,
     such duplications are not strictly illegal in JSON:
     this is why we use a list of members,
     instead of an omap from names to values;
     this way, we can handle duplicates if they ever occur,
     and we also preserve information about the ordering.")
   (xdoc::p
    "We model an array as a list of values.")
   (xdoc::p
    "We model numbers as rationals,
     which suffices to represent the value of all JSON numbers,
     but it abstracts away a bit of information from the JSON text.
     Thus, we may change our model of numbers
     to preserve more information from the JSON text.")
   (xdoc::p
    "We model strings as ACL2 strings, similarly to object member names.
     The remarks made above, about ISO-8859-1 vs. Unicode,
     and therefore possible extensions of our model of strings,
     apply here as well."))

  (fty::deftagsum value
    (:object ((members member-list)))
    (:array ((elements value-list)))
    (:number ((get rational)))
    (:string ((get string)))
    (:true ())
    (:false ())
    (:null ())
    :pred valuep
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist value-list
    :elt-type value
    :true-listp t
    :elementp-of-nil nil
    :pred value-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod member
    ((name string)
     (value value))
    :pred memberp
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist member-list
    :elt-type member
    :true-listp t
    :elementp-of-nil nil
    :pred member-listp
    :measure (two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-value
  value
  :short "Fixtype of JSON values and @('nil')."
  :pred maybe-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define object-member-values ((name stringp) (object valuep))
  :guard (value-case object :object)
  :returns (values value-listp)
  :short "Retrieve the values associated to a member name in a JSON object."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(tsee values),
     our abstract syntax does not assume that JSON objects
     have members with unique names.
     Accordingly, given a member name,
     there may be 0, 1, or more values associated with that name.
     This function returns the list of such values,
     in the order in which they occur in the object;
     member order is captured and significant in our JSON abstract syntax,
     as also described in @(tsee values).")
   (xdoc::p
    "Note that if the JSON object has two duplicate members
     (meaning not just the same name, but also the same value),
     the list returned here has correspondingly duplicate values."))
  (object-member-values-aux name (value-object->members object))

  :prepwork
  ((define object-member-values-aux ((name stringp) (members member-listp))
     :returns (values value-listp)
     (cond ((endp members) nil)
           ((equal name (member->name (car members)))
            (cons (member->value (car members))
                  (object-member-values-aux name (cdr members))))
           (t (object-member-values-aux name (cdr members)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define object-member-value? ((name stringp) (object valuep))
  :guard (value-case object :object)
  :returns (value? maybe-valuep)
  :short "Return the unique value associated to a member name in a JSON object,
          if the object has a member with that name."
  :long
  (xdoc::topstring
   (xdoc::p
    "While @(tsee object-member-values) is a general operation that never fails,
     in some cases a JSON object is expected to have no duplicate member names;
     indeed, the JSON standards recommend the absence of duplicate member names.
     In such cases, then, attempting to retrieve
     the value associated to a member name
     should result in at most one value.
     This operation can be used in these cases:
     it returns an optional value (i.e. a value or no value),
     but it conservatively checks that
     there are no other members with the same name;
     it does so by ensuring that
     the list returned by @(tsee object-member-values)
     contains at most one element.
     If there are duplicate member names, an error occurs."))
  (b* ((values (object-member-values name object)))
    (cond ((endp values) nil)
          ((= (len values) 1) (car values))
          (t (raise "The JSON object ~x0 ~
                     has multiple members with name ~x1."
                    object name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define object-member-value ((name stringp) (object valuep))
  :guard (value-case object :object)
  :returns (value valuep)
  :short "Return the unique value associated to a member name in a JSON object."
  :long
  (xdoc::topstring
   (xdoc::p
    "Sometimes a JSON object is expected to have
     exactly one member with a given name.
     In such cases, this operation can be used,
     instead of the more general
     @(tsee object-member-values) and @(tsee object-member-value?).
     This operation conservatively checks that there is indeed
     exactly one member in the JSON object with the given name,
     returning the associated value.
     If the conservative check fails, an error occurs."))
  (b* ((values (object-member-values name object)))
    (cond ((endp values) (prog2$ (raise "The JSON object ~x0 ~
                                         has no member with name ~x1."
                                        object name)
                                 (ec-call (value-fix :irrelevant))))
          ((= (len values) 1) (car values))
          (t (prog2$ (raise "The JSON object ~x0 ~
                             has multiple members with name ~x1."
                            object name)
                     (ec-call (value-fix :irrelevant)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define object-has-member-p ((name stringp) (object valuep))
  :guard (value-case object :object)
  :returns (yes/no booleanp)
  :short "Check if a JSON object has some member with a given name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The member may not be unique,
     i.e. if there are multiple members with the same name,
     this predicate returns @('t')."))
  (consp (object-member-values name object)))
