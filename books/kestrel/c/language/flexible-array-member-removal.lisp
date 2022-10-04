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

(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ flexible-array-member-removal
  :parents (language)
  :short "Removal of flexible array members."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a structure with a flexible array member is copied,
     as in most other uses of structures with flexible array members,
     the flexible array member is ignored [C:6.7.2.1/18].
     This means that, when the structure is copied (e.g. in an assignment),
     the flexible array member is dropped.")
   (xdoc::p
    "Here we introduce an ACL2 function to do that.
     This function operates on all values,
     leaving them unchanged unless the value is a structure
     with a flexible array member.
     By operating over all values,
     this function can be used uniformly when values are copies."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flexible-array-member-p ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is a structure with a flexible array member."
  (and (value-case val :struct)
       (value-struct->flexiblep val))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove-flexible-array-member ((val valuep))
  :returns (new-val valuep)
  :short "Remove the flexible array member,
          if the value is a structure and has such a member."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our model of structure values includes a flag
     indicating whether a structure has a flexible array member or not,
     which we consult to determine whether the last member should be removed
     (in fact, the flag is part of the model of structure values
     exactly to support this operation in a simple and clear way).
     Besides removing the member, we clear the flag,
     because the structure no longer has the flexible array member.
     It should be an invariant that,
     if the flag is set, the structure has at least two members:
     thus, removing a flexible array member never fails,
     and results in a new structure value
     that still has at least one member,
     as required by the invariant captured in @(tsee values).
     However, our current model of values does not capture
     the previously mentioned variant,
     i.e. that if the flag is set there are at least two members.
     Thus, this ACL2 function may receive an input structure value
     with the flag set and with just one member;
     in order to avoid returning errors and maintain the other invariant,
     in this case we just clear the flag without removing members.
     This should never happen,
     and we plan to add this other invariant to @(tsee values),
     and to remove this special case from this ACL2 function."))
  (if (flexible-array-member-p val)
      (b* ((members (value-struct->members val))
           ((unless (consp (cdr members)))
            (change-value-struct val :flexiblep nil))
           (new-members (butlast members 1)))
        (change-value-struct val
                             :members new-members
                             :flexiblep nil))
    (value-fix val))
  :guard-hints (("Goal" :in-theory (enable flexible-array-member-p)))
  :hooks (:fix)
  ///

  (defrule remove-flexible-array-member-when-absent
    (implies (not (flexible-array-member-p val))
             (equal (remove-flexible-array-member val)
                    (value-fix val)))))
