; Tests of defmap
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmap")
(include-book "std/testing/must-be-redundant" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmap-simple fix)

(must-be-redundant
  (DEFUND MAP-FIX (X)
    (IF (ATOM X)
        NIL
      (CONS (FIX (CAR X)) (MAP-FIX (CDR X)))))

  (DEFTHM MAP-FIX-OF-NIL
    (EQUAL (MAP-FIX 'NIL) NIL))

  (DEFTHM MAP-FIX-OF-CONS
    (EQUAL (MAP-FIX (CONS X0 X))
           (CONS (FIX X0) (MAP-FIX X))))

  (DEFTHM MAP-FIX-OF-TRUE-LIST-FIX
    (EQUAL (MAP-FIX (TRUE-LIST-FIX X))
           (MAP-FIX X)))

  (DEFTHMD MAP-FIX-OPENER
    (IMPLIES (CONSP (DOUBLE-REWRITE X))
             (EQUAL (MAP-FIX X)
                    (CONS (FIX (CAR (DOUBLE-REWRITE X)))
                          (MAP-FIX (CDR X))))))

  (DEFTHM MAP-FIX-OF-APPEND
    (EQUAL (MAP-FIX (APPEND X X0))
           (APPEND (MAP-FIX X) (MAP-FIX X0))))

  (DEFTHM CAR-OF-MAP-FIX
    (EQUAL (CAR (MAP-FIX X))
           (IF (CONSP (DOUBLE-REWRITE X))
               (FIX (CAR (DOUBLE-REWRITE X)))
             NIL)))

  (DEFTHM CDR-OF-MAP-FIX
    (EQUAL (CDR (MAP-FIX X))
           (MAP-FIX (CDR X))))

  (DEFTHM LEN-OF-MAP-FIX
    (EQUAL (LEN (MAP-FIX X))
           (LEN (DOUBLE-REWRITE X))))

  (DEFTHM CONSP-OF-MAP-FIX
    (EQUAL (CONSP (MAP-FIX X))
           (CONSP (DOUBLE-REWRITE X))))

  (DEFTHM MAP-FIX-IFF
    (IFF (MAP-FIX X)
         (CONSP (DOUBLE-REWRITE X))))

  (DEFTHM TRUE-LISTP-OF-MAP-FIX
    (EQUAL (TRUE-LISTP (MAP-FIX X)) 'T))

  (DEFTHM FIRSTN-OF-MAP-FIX
    (EQUAL (FIRSTN X0 (MAP-FIX X))
           (MAP-FIX (FIRSTN X0 (DOUBLE-REWRITE X)))))

  (DEFTHM TAKE-OF-MAP-FIX
    (IMPLIES (<= X0 (LEN (DOUBLE-REWRITE X)))
             (EQUAL (TAKE X0 (MAP-FIX X))
                    (MAP-FIX (TAKE X0 (DOUBLE-REWRITE X))))))

  (DEFTHM NTH-OF-MAP-FIX
    (IMPLIES (NATP X0)
             (EQUAL (NTH X0 (MAP-FIX X))
                    (IF (< X0 (LEN (DOUBLE-REWRITE X)))
                        (FIX (NTH X0 (DOUBLE-REWRITE X)))
                      'NIL))))

  (DEFTHM NTHCDR-OF-MAP-FIX
    (EQUAL (NTHCDR X0 (MAP-FIX X))
           (MAP-FIX (NTHCDR X0 X)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmap map-fix2 (x) (fix x))

(must-be-redundant

  (DEFUN MAP-FIX2 (X)
    (IF (ATOM X)
        NIL
      (CONS (FIX (CAR X))
            (MAP-FIX2 (CDR X)))))
  ;; and theorems ...
  )
