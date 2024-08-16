; JSON Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ values
  :parents (json)
  :short "JSON values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define fixtypes for JSON values.
     This is just a first version;
     we plan to make this more rich and precise."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes value/valuelist/member/memberlist
  :short "Fixtypes of JSON
          values, lists of values, members, and lists of members."
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
     so we may generalize this aspect of our JSON values in the future.
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
     but it abstracts away some information from the JSON syntax.
     Thus, in the future we may change our model of numbers
     to preserve more information from the JSON syntax.")
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

(fty::defoption value-option
  value
  :short "Fixtype of optional JSON values."
  :pred value-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-value
  :short "An irrelevant value."
  :type valuep
  :body (value-null))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-member
  :short "An irrelevant member."
  :type memberp
  :body (make-member :name "" :value (irr-value)))
