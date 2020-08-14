; JSON Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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
     we may generalize this aspect of our JSON abstract syntax in the future.
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
     as also described in @(tsee values)."))
  (object-member-values-aux name (value-object->members object))

  :prepwork
  ((define object-member-values-aux ((name stringp) (members member-listp))
     :returns (values value-listp)
     (cond ((endp members) nil)
           ((equal name (member->name (car members)))
            (cons (member->value (car members))
                  (object-member-values-aux name (cdr members))))
           (t (object-member-values-aux name (cdr members)))))))
