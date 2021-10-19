; A nicer interface to defevaluator
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defevaluator-plus")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (defevaluator+ myev binary-*)
  ;; expected result:
  (must-be-redundant
   ;; the main call to defevaluator generated:
   (defevaluator myev myev-list ((binary-* x y)) :namedp t)

   ;; additional theorems generated:
   (DEFTHM MYEV-LIST-OF-APPEND
     (EQUAL (MYEV-LIST (APPEND TERMS1 TERMS2) A)
            (APPEND (MYEV-LIST TERMS1 A)
                    (MYEV-LIST TERMS2 A)))
     :HINTS (("Goal" :IN-THEORY (ENABLE APPEND))))
   (DEFTHM LEN-OF-MYEV-LIST
     (EQUAL (LEN (MYEV-LIST TERMS A))
            (LEN TERMS))
     :HINTS (("Goal" :IN-THEORY (ENABLE APPEND (:I LEN)))))
   (DEFTHM MYEV-LIST-OF-TRUE-LIST_FIX
     (EQUAL (MYEV-LIST (TRUE-LIST-FIX TERMS) A)
            (MYEV-LIST TERMS A))
     :HINTS (("Goal" :IN-THEORY (ENABLE APPEND (:I LEN)))))
   )

  ;; Improved versions of the constraints:
  (DEFTHM MYEV-OF-LAMBDA-BETTER
    (IMPLIES (CONSP (CAR X))
             (EQUAL (MYEV X A)
                    (MYEV (CADDR (CAR X))
                          (PAIRLIS$ (CADR (CAR X))
                                    (MYEV-LIST (CDR X) A))))))

  ;; additional check:
  (defthm test (equal (myev '(binary-* '2 x) '((x . 3))) 6)))

(deftest
  (defevaluator+ math-and-if-ev binary-+ binary-* if))
