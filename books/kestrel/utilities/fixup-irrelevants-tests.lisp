(in-package "ACL2")

(include-book "std/testing/assert-bang-stobj" :dir :system)
(include-book "fixup-irrelevants")

(assert-event
 (equal (fixup-irrelevants-in-mutual-recursion-form
         '(mutual-recursion
           (defun even-natp (x irrelevant1 irrelevant2)
             (if (zp x)
                 t
               (not (odd-natp (+ -1 x) irrelevant1 irrelevant2))))
           (defun odd-natp (x irrelevant3 irrelevant4)
             (if (zp x)
                 nil
               (not (even-natp (+ -1 x) irrelevant3 irrelevant4)))))
         state)
        '(MUTUAL-RECURSION
          (DEFUN EVEN-NATP (X IRRELEVANT1 IRRELEVANT2)
            (DECLARE (IRRELEVANT IRRELEVANT1 IRRELEVANT2))
            (IF (ZP X)
                T
                (NOT (ODD-NATP (+ -1 X)
                               IRRELEVANT1 IRRELEVANT2))))
          (DEFUN ODD-NATP (X IRRELEVANT3 IRRELEVANT4)
            (DECLARE (IRRELEVANT IRRELEVANT3 IRRELEVANT4))
            (IF (ZP X)
                NIL
                (NOT (EVEN-NATP (+ -1 X)
                                IRRELEVANT3 IRRELEVANT4)))))))

(assert-event
 (equal (fixup-irrelevants-in-defun-form
         '(defun my-len (lst irrel)
            (if (endp lst)
                0
              (+ 1 (my-len (rest lst) (+ 7 irrel)))))
         state)
        '(defun my-len (lst irrel)
           (declare (irrelevant irrel))
           (if (endp lst)
               0
             (+ 1 (my-len (rest lst) (+ 7 irrel)))))))
