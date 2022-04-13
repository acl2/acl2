; Documentation for defstobj+
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/xdoc-paras" :dir :system)

(defxdoc defstobj+
  :short "A wrapper for defstobj"
  :parents (stobj defstobj)
  :long
  (xdoc::topstring
   (xdoc::topparas
    "The @('defstobj+') utility is a drop-in replacement for defstobj that disables the stobj-related functions and proves many rules about them, such as read-over-write properties.

    Currently only scalar and array fields are supported.

    Properties proved, given suitable assumptions, include:")
   (xdoc::ul-from-string
    "That the stobj creation function returns a well-formed stobj.

    That each scalar field update function preserves well-formedness of the stobj.

    That each array element update function preserves well-formedness of the stobj.

    That each array element resize function preserves well-formedness of the stobj.

    For scalar fields, that the field accessor returns a value of the appropriate type (except when this is trivial because the type is @('t')).

    For scalar fields, that accessing the field after writing it gives back the value written.

    For scalar fields, that updating the field twice is equivalent to just doing the outer update.


    For array fields, that the element accessor returns a value of the appropriate type (except when this is trivial because the type is @('t')).

    For array fields, that writing to an index and then accessing the element at that index gives back the value written.

    For array fields, that writing to an index is irrelevant when accessing the element at a different index.

    (For array fields, a rule combining the previous two rules, splitting into cases depending on whether the two indices are the same or different.)

    For array fields, that writing to the same index twice is the same as just doing the outer write.

    For array fields, that writes to different indices can be reordered, to bring outward the write whose index is a syntactically smaller term.

    (For array fields, a variant of the rule just above that splits into cases depending on whether the two indices are the same or different.)

    For array fields, that two writes of the same value (at possibly different indices) can be reordered, to bring outward the write whose index is a syntactically smaller term.

    For array fields, that getting the array length after resizing the field returns the supplied length.

    For array fields, that writing an element does not affect the array length.

    For array fields, that accessing an element after resizing the array returns either what was there before or the initial array element value.

    For array fields, that resizing the array after writing an element either discards the write (if the index written is beyond the new length), or is the same as resizing first and then writing.

    That reads of a field of the stobj are unaffected by writes to other fields.  Here, 'reads' include reading a scalar field, reading an element of an array field, and getting the length of an array field, and 'writes' include writing a scalar field, writing an element of an array field, and setting the length of an array field.

    That writes to different fields can be reordered, to respect the order in which the fields were declared.  Here again, 'writes' including writing scalar fields, writing array elements, and resizing array fields."
    )
   (xdoc::topparas
    "In some cases, @('defstobj+') generates theorems with fewer hypotheses when the predicate involved is satisfied by the value @('nil'), because reading beyond the bounds of an array gives @('nil').

    The @('defstobj+') tool attempts to generate nice names for rules, based on the @(tsee type-spec) declarations involved.  For example, a typespec of @('(integer 0 *)') can give rise to a theorem mentioning @('natp')."
    )))
