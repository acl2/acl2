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
     This means that, when the structure is copied
     (in a declaration, assignment, or function call),
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

(define remove-flexible-array-member ((val valuep))
  :returns (new-val value-resultp)
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
     If the member is removed,
     we ensure that there is at least another member
     in order to maintain the invariant in @(tsee value);
     this should be always the case,
     but currently @(tsee value) does not capture the invariant that
     there are at least two members if the flag is set.
     If the member is removed, we unset the flag,
     because the structure no longer has the flexible array member."))
  (b* (((unless (and (value-case val :struct)
                     (value-struct->flexiblep val)))
        (value-fix val))
       (members (value-struct->members val))
       ((unless (consp (cdr members))) (error :impossible))
       (new-members (butlast members 1)))
    (change-value-struct val
                         :members new-members
                         :flexiblep nil))
  :hooks (:fix))
