(in-package "SYNTHETO")

(include-book "../translation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An example from Vanderbilt, shown during the weekly call.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(translate-to-acl2
 (LIST
  (toplevel-type ; added by hand
   (MAKE-TYPE-DEFINITION
    :NAME (MAKE-IDENTIFIER :NAME "positive2")
    :BODY
    (MAKE-TYPE-DEFINER-PRODUCT
     :GET (MAKE-TYPE-PRODUCT
           :FIELDS (LIST (MAKE-FIELD :NAME (MAKE-IDENTIFIER :NAME "y")
                                     :TYPE (MAKE-TYPE-INTEGER)))
           :INVARIANT NIL))))
  (toplevel-type ; added by hand
   (MAKE-TYPE-DEFINITION
    :NAME (MAKE-IDENTIFIER :NAME "positive3")
    :BODY
    (MAKE-TYPE-DEFINER-PRODUCT
     :GET
     (MAKE-TYPE-PRODUCT
      :FIELDS
      (LIST
       (MAKE-FIELD
        :NAME (MAKE-IDENTIFIER :NAME "z")
        :TYPE (MAKE-TYPE-DEFINED :NAME (MAKE-IDENTIFIER :NAME "positive2"))))
      :INVARIANT NIL))))))
