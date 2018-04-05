; Copyright (C) 2018, J Strother Moore
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Appendix A. Function Definitions

; This section is the PLTP(A) version of the definitions in Appendix A of the
; JACM paper.  The order of some definitions has been rearranged because
; PLTP(A) insists that every function called in the body of a DEFINE (except
; the symbol being defined) be previously defined.

; The following PLTP(A) command defines: ADD1, AND, BOOLEAN, CONSTTRUE,
; IMPLIES, NOT, NUMBERP, OR, SUB1, and ZEROP as they are shown in Appendix A.
; (CONSTTRUE is not mentioned in Appendix A.)  These non-primitive function
; symbols are mentioned in the code for PLTP(A) and must be defined this way in
; every extension of the theory.

(BOOT-STRAP)

; This causes us to print IF as COND as we did in 14 September, 1973.  It also
; untranslates numeric constants, e.g., (cons nil (cons nil nil)), to their
; counterparts, e.g., 2, so output more closely resembles the 1973 conventions.

(SET-FEATURE :ALL :PLTP-NOTATION)

; These two DCLs are not in the JACM paper because PLTP did not require
; undefined functions to have known arities.

(DCL
 (APPLY (X Y)))

(DCL
 (APPLY2 (X Y Z)))

; LENGTH out of order

(DEFINE
  (LENGTH
   (LAMBDA (X)
           (COND X
                 (ADD1 (LENGTH (CDR X)))
                 0))))

(DEFINE
  (ADD
   (LAMBDA (X Y)
           (COND (ZEROP X)
                 (LENGTH Y)
                 (ADD1 (ADD (SUB1 X) Y))))))

; ADD1 introduced by BOOT-STRAP

; LTE out of order

(DEFINE
  (LTE
   (LAMBDA (X Y)
           (COND (ZEROP X)
                 T
                 (COND (ZEROP Y)
                       NIL
                       (LTE (SUB1 X) (SUB1 Y)))))))

(DEFINE
  (ADDTOLIST
   (LAMBDA (X Y)
           (COND Y
                 (COND (LTE X (CAR Y))
                       (CONS X Y)
                       (CONS (CAR Y) (ADDTOLIST X (CDR Y))))
                 (CONS X NIL)))))

; AND introduced by BOOT-STRAP

(DEFINE
  (APPEND
   (LAMBDA (X Y)
           (COND X
                 (CONS (CAR X)
                       (APPEND (CDR X) Y))
                 Y))))

(DEFINE
  (ASSOC
   (LAMBDA (X Y)
           (COND Y
                 (COND (CAR Y)
                       (COND (EQUAL X (CAR (CAR Y)))
                             (CAR Y)
                             (ASSOC X (CDR Y)))
                       (ASSOC X (CDR Y)))
                 NIL))))

; BOOLEAN introduced by BOOT-STRAP

(DEFINE
  (CDRN
   (LAMBDA (X Y)
           (COND Y
                 (COND (ZEROP X)
                       Y
                       (CDRN (SUB1 X) (CDR Y)))
                 NIL))))

(DEFINE
  (CONSNODE
   (LAMBDA (X Y)
           (CONS NIL (CONS X Y)))))

(DEFINE
  (COPY
   (LAMBDA (X)
           (COND X
                 (CONS (COPY (CAR X))
                       (COPY (CDR X)))
                 NIL))))

(DEFINE
  (COUNT
   (LAMBDA (X Y)
           (COND Y
                 (COND (EQUAL X (CAR Y))
                       (ADD1 (COUNT X (CDR Y)))
                       (COUNT X (CDR Y)))
                 0))))

(DEFINE
  (DOUBLE
   (LAMBDA (X)
           (COND (ZEROP X)
                 0
                 (ADD 2 (DOUBLE (SUB1 X)))))))

(DEFINE
  (ELEMENT
   (LAMBDA (X Y)
           (COND Y
                 (COND (ZEROP X)
                       (CAR Y)
                       (ELEMENT (SUB1 X) (CDR Y)))
                 NIL))))

(DEFINE
  (EQUALP
   (LAMBDA (X Y)
           (COND X
                 (COND Y
                       (COND (EQUALP (CAR X) (CAR Y))
                             (EQUALP (CDR X) (CDR Y))
                             NIL)
                       NIL)
                 (COND Y NIL T)))))

; Major Discrepancy: In Appendix A, EVEN1 is defined mutually recursively with
; ODD.  A theorem in Appendix B, reproduced below, shows PLTP proving that its
; EVEN1 is EVEN2.  PLTP(A) insists that all subfunctions be previously defined,
; so mutual-recursion is not permitted.  This precludes us from defining
; Appendix A's EVEN1.  But so that we can show a similar theorem relating to
; EVEN2, we introduce a similar algorithm here:

(DEFINE
  (EVEN1
   (LAMBDA (PARITY X)
           (COND (ZEROP X)
                 (IF PARITY T NIL)
                 (EVEN1 (NOT PARITY) (SUB1 X))))))

(DEFINE
  (EVEN2
   (LAMBDA (X)
           (COND (ZEROP X)
                 T
                 (COND (ZEROP (SUB1 X))
                       NIL
                       (EVEN2 (SUB1 (SUB1 X))))))))

; NODE out of order

(DEFINE
  (NODE
   (LAMBDA (X)
           (COND X
                 (COND (CAR X)
                       NIL
                       (COND (CDR X) T NIL))
                 NIL))))

(DEFINE
  (FLATTEN
   (LAMBDA (X)
           (COND (NODE X)
                 (APPEND (FLATTEN (CAR (CDR X)))
                         (FLATTEN (CDR (CDR X))))
                 (CONS X NIL)))))

(DEFINE
  (GT
   (LAMBDA (X Y)
           (COND (ZEROP X)
                 NIL
                 (COND (ZEROP Y)
                       T
                       (GT (SUB1 X) (SUB1 Y)))))))

(DEFINE
  (HALF
   (LAMBDA (X)
           (COND (ZEROP X)
                 0
                 (COND (ZEROP (SUB1 X))
                       0
                       (ADD1 (HALF (SUB1 (SUB1 X)))))))))

; IMPLIES introduced by BOOT-STRAP

; MEMBER out of order

(DEFINE
  (MEMBER
   (LAMBDA (X Y)
           (COND Y
                 (COND (EQUAL X (CAR Y))
                       T
                       (MEMBER X (CDR Y)))
                 NIL))))

(DEFINE
  (INTERSECT
   (LAMBDA (X Y)
           (COND X
                 (COND (MEMBER (CAR X) Y)
                       (CONS (CAR X) (INTERSECT (CDR X) Y))
                       (INTERSECT (CDR X) Y))
                 NIL))))

(DEFINE
  (LAST
   (LAMBDA (X)
           (COND X
                 (COND (CDR X)
                       (LAST (CDR X))
                       (CAR X))
                 NIL))))

; LENGTH moved up

; Note: PLTP abused the arity of its APPLY: it was sometimes given 2 arguments
; (as in MAPLIST below) and sometimes 3 (as in LIT here).  PLTP(A) insists that
; function symbols have fixed arities.  So we use APPLY2 instead of APPLY here.

(DEFINE
  (LIT
   (LAMBDA (X Y Z)
           (COND X
                 (APPLY2 Z (CAR X) (LIT (CDR X) Y Z))
                 Y))))

; LTE moved up

(DEFINE
  (MAPLIST
   (LAMBDA (X Y)
           (COND X
                 (CONS (APPLY Y (CAR X))
                       (MAPLIST (CDR X) Y))
                 NIL))))

; MEMBER moved up

(DEFINE
  (MONOT1
   (LAMBDA (X)
           (COND X
                 (COND (CDR X)
                       (COND (EQUAL (CAR X) (CAR (CDR X)))
                             (MONOT1 (CDR X))
                             NIL)
                       T)
                 T))))

(DEFINE
  (MONOT2
   (LAMBDA (X Y)
           (COND Y
                 (COND (EQUAL X (CAR Y))
                       (MONOT2 X (CDR Y))
                       NIL)
                 T))))

(DEFINE
  (MONOT2P
   (LAMBDA (X)
           (COND X
                 (MONOT2 (CAR X) (CDR X))
                 T))))

(DEFINE
  (MULT
   (LAMBDA (X Y)
           (COND (ZEROP X)
                 0
                 (ADD Y (MULT (SUB1 X) Y))))))

; NODE moved up

; NOT introduced by BOOT-STRAP

; NUMBERP introduced by BOOT-STRAP

(DEFINE
  (OCCUR
   (LAMBDA (X Y)
           (COND (EQUAL X Y)
                 T
                 (COND Y
                       (COND (OCCUR X (CAR Y))
                             T
                             (OCCUR X (CDR Y)))
                       NIL)))))

; ODD omitted as explained in EVEN1 above

; OR introduced by BOOT-STRAP

(DEFINE
  (ORDERED
   (LAMBDA (X)
           (COND X
                 (COND (CDR X)
                       (COND (LTE (CAR X) (CAR (CDR X)))
                             (ORDERED (CDR X))
                             NIL)
                       T)
                 T))))

(DEFINE
  (PAIRLIST
   (LAMBDA (X Y)
           (COND X
                 (COND Y
                       (CONS (CONS (CAR X) (CAR Y))
                             (PAIRLIST (CDR X) (CDR Y)))
                       (CONS (CONS (CAR X) NIL)
                             (PAIRLIST (CDR X) NIL)))
                 NIL))))

(DEFINE
  (REVERSE
   (LAMBDA (X)
           (COND X
                 (APPEND (REVERSE (CDR X)) (CONS (CAR X) NIL))
                 NIL))))

(DEFINE
  (SORT
   (LAMBDA (X)
           (COND X
                 (ADDTOLIST (CAR X) (SORT (CDR X)))
                 NIL))))

; SUB1 introduced by BOOT-STRAP

(DEFINE
  (SUBSET
   (LAMBDA (X Y)
           (COND X
                 (COND (MEMBER (CAR X) Y)
                       (SUBSET (CDR X) Y)
                       NIL)
                 T))))

(DEFINE
  (SUBST
   (LAMBDA
    (X Y Z)
    (COND (EQUAL Y Z)
          X
          (COND Z
                (CONS (SUBST X Y (CAR Z))
                      (SUBST X Y (CDR Z)))
                NIL)))))

(DEFINE
  (SWAPTREE
   (LAMBDA (X)
           (COND (NODE X)
                 (CONSNODE (SWAPTREE (CDR (CDR X)))
                           (SWAPTREE (CAR (CDR X))))
                 X))))

(DEFINE
  (TIPCOUNT
   (LAMBDA (X)
           (COND (NODE X)
                 (ADD (TIPCOUNT (CAR (CDR X)))
                      (TIPCOUNT (CDR (CDR X))))
                 1))))

(DEFINE
  (UNION
   (LAMBDA (X Y)
           (COND X
                 (COND (MEMBER (CAR X) Y)
                       (UNION (CDR X) Y)
                       (CONS (CAR X) (UNION (CDR X) Y)))
                 Y))))

; ZEROP introduced by BOOT-STRAP


; Appendix B. Theorems Proved

(PROVE JACM-1
       (EQUAL (APPEND A (APPEND B C)) (APPEND (APPEND A B) C)))

(PROVE JACM-2
       (IMPLIES (EQUAL (APPEND A B) (APPEND A C)) (EQUAL B C)))

(PROVE JACM-3
       (EQUAL (LENGTH (APPEND A B)) (LENGTH (APPEND B A))))

(PROVE JACM-4
       (EQUAL (REVERSE (APPEND A B)) (APPEND (REVERSE B) (REVERSE A))))

(PROVE JACM-5
       (EQUAL (LENGTH (REVERSE D)) (LENGTH D)))

(PROVE JACM-6
       (EQUAL (REVERSE (REVERSE A)) A))

(PROVE JACM-7
       (IMPLIES A (EQUAL (LAST (REVERSE A)) (CAR A))))

(PROVE JACM-8
       (IMPLIES (MEMBER A B) (MEMBER A (APPEND B C))))

(PROVE JACM-9
       (IMPLIES (MEMBER A B) (MEMBER A (APPEND C B))))

(PROVE JACM-10
       (IMPLIES (AND (NOT (EQUAL A (CAR B))) (MEMBER A B)) (MEMBER A (CDR B))))

(PROVE JACM-11
       (IMPLIES (OR (MEMBER A B) (MEMBER A C)) (MEMBER A (APPEND B C))))

(PROVE JACM-12
       (IMPLIES (AND (MEMBER A B) (MEMBER A C)) (MEMBER A (INTERSECT B C))))

(PROVE JACM-13
       (IMPLIES (OR (MEMBER A B) (MEMBER A C)) (MEMBER A (UNION B C))))

(PROVE JACM-14
       (IMPLIES (SUBSET A B) (EQUAL (UNION A B) B)))

(PROVE JACM-15
       (IMPLIES (SUBSET A B) (EQUAL (INTERSECT A B) A)))

(PROVE JACM-16
       (EQUAL (MEMBER A B) (NOT (EQUAL (ASSOC A (PAIRLIST B C)) NIL))))

(PROVE JACM-17
       (EQUAL (MAPLIST (APPEND A B) C) (APPEND (MAPLIST A C) (MAPLIST B C))))

(PROVE JACM-18
       (EQUAL (LENGTH (MAPLIST A B)) (LENGTH A)))

(PROVE JACM-19
       (EQUAL (REVERSE (MAPLIST A B)) (MAPLIST (REVERSE A) B)))

(PROVE JACM-20
       (EQUAL (LIT (APPEND A B) C D) (LIT A (LIT B C D) D)))

(PROVE JACM-21
       (IMPLIES (AND (BOOLEAN A) (BOOLEAN B))
         (EQUAL (AND (IMPLIES A B) (IMPLIES B A)) (EQUAL A B))))

(PROVE JACM-22
       (EQUAL (ELEMENT B A) (ELEMENT (APPEND C B) (APPEND C A))))

(PROVE JACM-23
       (IMPLIES (ELEMENT B A) (MEMBER (ELEMENT B A) A)))

(PROVE JACM-24
       (EQUAL (CDRN C (APPEND A B)) (APPEND (CDRN C A) (CDRN (CDRN A C) B))))

(PROVE JACM-25
       (EQUAL (CDRN (APPEND B C) A) (CDRN C (CDRN B A))))

(PROVE JACM-26
       (EQUAL (EQUAL A B) (EQUAL B A)))

(PROVE JACM-27
       (IMPLIES (AND (EQUAL A B) (EQUAL B C)) (EQUAL A C)))

(PROVE JACM-28
       (IMPLIES (AND (BOOLEAN A) (AND (BOOLEAN B) (BOOLEAN C)))
         (EQUAL (EQUAL (EQUAL A B) C) (EQUAL A (EQUAL B C)))))

(PROVE JACM-29
       (EQUAL (ADD A B) (ADD B A)))

(PROVE JACM-30
       (EQUAL (ADD A (ADD B C)) (ADD (ADD A B) C)))

(PROVE JACM-31
       (EQUAL (MULT A B) (MULT B A)))

(PROVE JACM-32
       (EQUAL (MULT A (ADD B C)) (ADD (MULT A B) (MULT A C))))

(PROVE JACM-33
       (EQUAL (MULT A (MULT B C)) (MULT (MULT A B) C)))

; This is not proveable by PLTP(A) if we use our version of EVEN1, but is
; proveable with EVEN2.

(PROVE JACM-34
       (EVEN2 (DOUBLE A)))

(PROVE JACM-35
       (IMPLIES (NUMBERP A) (EQUAL (HALF (DOUBLE A)) A)))

; This is not proveable by PLTP(A) if we use our version of EVEN1, but is
; proveable with EVEN2.

(PROVE JACM-36
       (IMPLIES (AND (NUMBERP A) (EVEN2 A)) (EQUAL (DOUBLE (HALF A)) A)))

(PROVE JACM-37
       (EQUAL (DOUBLE A) (MULT 2 A)))

(PROVE JACM-38
       (EQUAL (DOUBLE A) (MULT A 2)))

(PROVE JACM-39
       (EQUAL (EVEN1 T A) (EVEN2 A)))

(PROVE JACM-40
       (GT (LENGTH (CONS A B)) (LENGTH B)))

(PROVE JACM-41
       (IMPLIES (AND (GT A B) (GT B C)) (GT A C)))

(PROVE JACM-42
       (IMPLIES (GT A B) (NOT (GT B A))))

(PROVE JACM-43
       (LTE A (APPEND B A)))

(PROVE JACM-44
       (OR (LTE A B) (LTE B A)))

(PROVE JACM-45
       (OR (GT A B) (OR (GT B A) (EQUAL (LENGTH A) (LENGTH B)))))

(PROVE JACM-46
       (EQUAL (MONOT2P A) (MONOT1 A)))

(PROVE JACM-47
       (ORDERED (SORT A)))

(PROVE JACM-48
       (IMPLIES (AND (MONOT1 A) (MEMBER B A)) (EQUAL (CAR A) B)))

(PROVE JACM-49
       (LTE (CDRN A B) B))

(PROVE JACM-50
       (EQUAL (MEMBER A (SORT B)) (MEMBER A B)))

(PROVE JACM-51
       (EQUAL (LENGTH A) (LENGTH (SORT A))))

(PROVE JACM-52
       (EQUAL (COUNT A B) (COUNT A (SORT B))))

(PROVE JACM-53
       (IMPLIES (ORDERED A) (EQUAL A (SORT A))))

(PROVE JACM-54
       (IMPLIES (ORDERED (APPEND A B)) (ORDERED A)))

(PROVE JACM-55
       (IMPLIES (ORDERED (APPEND A B)) (ORDERED B)))

(PROVE JACM-56
       (EQUAL (EQUAL (SORT A) A) (ORDERED A)))

(PROVE JACM-57
       (LTE (HALF A) A))

(PROVE JACM-58
       (EQUAL (COPY A) A))

(PROVE JACM-59
       (EQUAL (EQUALP A B) (EQUAL A B)))

(PROVE JACM-60
       (EQUAL (SUBST A A B) B))

(PROVE JACM-61
       (IMPLIES (MEMBER A B) (OCCUR A B)))

(PROVE JACM-62
       (IMPLIES (NOT (OCCUR A B)) (EQUAL (SUBST C A B) B)))

(PROVE JACM-63
       (EQUAL (EQUALP A B) (EQUALP B A)))

(PROVE JACM-64
       (IMPLIES (AND (EQUAL A B) (EQUALP B C)) (EQUALP A C)))

(PROVE JACM-65
       (EQUAL (SWAPTREE (SWAPTREE A)) A))

(PROVE JACM-66
       (EQUAL (FLATTEN (SWAPTREE A)) (REVERSE (FLATTEN A))))

(PROVE JACM-67
       (EQUAL (LENGTH (FLATTEN A)) (TIPCOUNT A)))

