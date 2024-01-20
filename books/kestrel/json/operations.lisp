; JSON Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define object-member-values ((name stringp) (object valuep))
  :guard (value-case object :object)
  :returns (values value-listp)
  :short "Retrieve the values associated to a member name in a JSON object."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(tsee values),
     our model of JSON values does not assume or enforce that JSON objects
     have members with unique names.
     Accordingly, given a member name,
     there may be 0, 1, or more values associated with that name.
     This function returns the list of such values,
     in the order in which they occur in the object;
     member order is captured and significant in our JSON values.")
   (xdoc::p
    "Note that if the JSON object has two duplicate members
     (meaning not just the same name, but also the same value),
     the list returned here has correspondingly duplicate values."))
  (object-member-values-aux name (value-object->members object))

  :prepwork
  ((define object-member-values-aux ((name stringp) (members member-listp))
     :returns (values value-listp)
     :parents nil
     (cond ((endp members) nil)
           ((equal name (member->name (car members)))
            (cons (member->value (car members))
                  (object-member-values-aux name (cdr members))))
           (t (object-member-values-aux name (cdr members)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define object-member-value? ((name stringp) (object valuep))
  :guard (value-case object :object)
  :returns (value? value-optionp)
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
                                 (irr-value)))
          ((= (len values) 1) (car values))
          (t (prog2$ (raise "The JSON object ~x0 ~
                             has multiple members with name ~x1."
                            object name)
                     (irr-value))))))

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
