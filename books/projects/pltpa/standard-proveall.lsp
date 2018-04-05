; Copyright (C) 2018, J Strother Moore
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Listing-I: [/ DEFS] and [THEOREMS]

; Section: [/ DEFS]

; [/ DEFS] TRACK 36 CREATED 10.59 18 1973
; [21.23 14 SEPT 1973];

; However, we have had to reorder the sequence because of PLTP(A)'s insistence
; that the body of a definition be a term at the time it is introduced.  When a
; definition from [/ DEFS] is omitted below it is because that symbol is a
; primitive of PLTP(A) and is defined in the BOOT-STRAP process; we leave the
; note ``introduced in BOOT-STRAP'' on each such occasion.  When a definition
; has had to be moved up in the sequence to allow the introduction of the
; ``next'' definition, we write ``out of order'' at its new, earlier location
; and ``moved up'' at its original location in [/ DEFS].  These notes are
; intended to make it easier for the reader to confirm that this really does
; contain all and only the definitions in [/ DEFS].

; We also added two ``declaration'' commands to introduce undefined functions
; used in PLTP definitions.  PLTP(A) insists that every function used have a
; previously fixed arity.

; More importantly, on 14 occasions we have changed the theorems listed below
; from those listed in [THEOREMS].  All are marked with comments including the
; word ``Discrepancy''.  Twelve of the changes consist merely of adding NUMBERP
; hypotheses on variables that PLTP considered ``numeric''; PLTP(A) does not
; support this notion.  The other two discrepancies are theorems that are
; omitted entirely from this sequence because (as discussed in
; standard-proveall-failures.lisp) PLTP(A) cannot prove them and neither, I
; believe, could PLTP.

(BOOT-STRAP)

; This causes us to print IF as COND as we did in 14 September, 1973.  It also
; untranslates numeric constants, e.g., (cons nil (cons nil nil)), to their
; counterparts, e.g., 2, so output more closely resembles the 1973 conventions.

(SET-FEATURE :ALL :PLTP-NOTATION)

; Discrepancy: These two DCLs are not in the JACM paper because PLTP did not
; require undefined functions to have known arities.

(DCL
 (APPLY (X Y)))

(DCL
 (APPLY2 (X Y Z)))

; ADD1 introduced by BOOT-STRAP

; LTE out of order

(DEFINE
  (LTE (LAMBDA (X Y) (COND X (COND Y (LTE (SUB1 X) (SUB1 Y)) NIL) T))))

(DEFINE
  (ADDTOLIS
   (LAMBDA (X Y)
           (COND Y
                 (COND (LTE X (CAR Y)) (CONS X Y) (CONS (CAR Y) (ADDTOLIS X (CDR Y))))
                 (CONS X NIL)))))


; AND introduced by BOOT-STRAP

(DEFINE
  (APPEND (LAMBDA (X Y) (COND X (CONS (CAR X) (APPEND (CDR X) Y)) Y))))

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

(DEFINE
  (BINADD
   (LAMBDA
    (X Y)
    (COND
     X
     (COND Y
           (COND (CAR X)
                 (COND (CAR Y)
                       (CONS 0 (BINADD (CONS 1 NIL) (BINADD (CDR X) (CDR Y))))
                       (CONS 1 (BINADD (CDR X) (CDR Y))))
                 (CONS (CAR Y) (BINADD (CDR X) (CDR Y))))
           X)
     Y))))

(DEFINE
  (BINARYOF
   (LAMBDA (X) (COND X (BINADD (CONS 1 NIL) (BINARYOF (CDR X))) NIL))))

; BOOLEAN introduced by BOOT-STRAP

(DEFINE
  (CDRN (LAMBDA (X Y) (COND Y (COND X (CDRN (SUB1 X) (CDR Y)) Y) NIL))))

(DEFINE
  (CONSNODE (LAMBDA (X Y) (CONS NIL (CONS X Y)))))

; CONSTTRUE introduced by BOOT-STRAP

(DEFINE
  (COPY (LAMBDA (X) (COND X (CONS (COPY (CAR X)) (COPY (CDR X))) NIL))))

(DEFINE
  (COUNT
   (LAMBDA (X Y)
           (COND Y
                 (COND (EQUAL X (CAR Y)) (ADD1 (COUNT X (CDR Y))) (COUNT X (CDR Y)))
                 0))))


(DEFINE
  (DOUBLE (LAMBDA (X) (COND X (ADD1 (ADD1 (DOUBLE (SUB1 X)))) 0))))

(DEFINE
  (ELEMENT
   (LAMBDA (X Y) (COND Y (COND X (ELEMENT (SUB1 X) (CDR Y)) (CAR Y)) NIL))))

(DEFINE
  (EQUALP
   (LAMBDA (X Y)
           (COND
            X
            (COND Y (COND (EQUALP (CAR X) (CAR Y)) (EQUALP (CDR X) (CDR Y)) NIL) NIL)
            (COND Y NIL T)))))

(DEFINE
  (EVEN1 (LAMBDA (X) (COND X (NOT (EVEN1 (SUB1 X))) T))))

(DEFINE
  (EVEN2 (LAMBDA (X) (COND X (COND (SUB1 X) (EVEN2 (SUB1 (SUB1 X))) NIL) T))))

; NODE out of order

(DEFINE
  (NODE (LAMBDA (X) (COND X (COND (CAR X) NIL (COND (CDR X) T NIL)) NIL))))

(DEFINE
  (FLATTEN
   (LAMBDA (X)
           (COND (NODE X)
                 (APPEND (FLATTEN (CAR (CDR X))) (FLATTEN (CDR (CDR X))))
                 (CONS X NIL)))))

(DEFINE
  (GT (LAMBDA (X Y) (COND X (COND Y (GT (SUB1 X) (SUB1 Y)) T) NIL))))

(DEFINE
  (HALF
   (LAMBDA (X) (COND X (COND (SUB1 X) (ADD1 (HALF (SUB1 (SUB1 X)))) 0) 0))))

; IMPLIES introduced by BOOT-STRAP

; MEMBER out of order

(DEFINE
  (MEMBER
   (LAMBDA (X Y) (COND Y (COND (EQUAL X (CAR Y)) T (MEMBER X (CDR Y))) NIL))))

(DEFINE
  (INTERSEC
   (LAMBDA (X Y)
           (COND X
                 (COND (MEMBER (CAR X) Y)
                       (CONS (CAR X) (INTERSEC (CDR X) Y))
                       (INTERSEC (CDR X) Y))
                 NIL))))

(DEFINE
  (ISBINARY
   (LAMBDA
    (X)
    (COND
     X
     (COND (OR (EQUAL (CAR X) NIL) (EQUAL (CAR X) T)) (ISBINARY (CDR X)) NIL)
     T))))

(DEFINE
  (LAST (LAMBDA (X) (COND X (COND (CDR X) (LAST (CDR X)) (CAR X)) NIL))))

(DEFINE
  (LENGTH (LAMBDA (X) (COND X (ADD1 (LENGTH (CDR X))) 0))))

(DEFINE
  (LINEAR
   (LAMBDA (X)
           (COND X
                 (COND (CAR X)
                       (CONS NIL (DOUBLE (LINEAR (CDR X))))
                       (DOUBLE (LINEAR (CDR X))))
                 NIL))))

(DEFINE
  (LIT (LAMBDA (X Y Z) (COND X (APPLY2 Z (CAR X) (LIT (CDR X) Y Z)) Y))))

; LTE moved up

(DEFINE
  (LT (LAMBDA (X Y) (COND (LTE X Y) (NOT (EQUAL X Y)) NIL))))

(DEFINE
  (MAPLIST
   (LAMBDA (X Y) (COND X (CONS (APPLY Y (CAR X)) (MAPLIST (CDR X) Y)) NIL))))

; MEMBER moved up

(DEFINE
  (MONOT1
   (LAMBDA
    (X)
    (COND
     X
     (COND (CDR X) (COND (EQUAL (CAR X) (CAR (CDR X))) (MONOT1 (CDR X)) NIL) T)
     T))))

(DEFINE
  (MONOT2
   (LAMBDA (X Y) (COND Y (COND (EQUAL X (CAR Y)) (MONOT2 X (CDR Y)) NIL) T))))

(DEFINE
  (MONOT2P (LAMBDA (X) (COND X (MONOT2 (CAR X) (CDR X)) T))))

; NODE moved up

; NOT introduced by BOOT-STRAP

(DEFINE
  (OCCUR
   (LAMBDA (X Y)
           (COND (EQUAL X Y)
                 T
                 (COND Y (COND (OCCUR X (CAR Y)) T (OCCUR X (CDR Y))) NIL)))))

; OR introduced by BOOT-STRAP

(DEFINE
  (ORDERED
   (LAMBDA (X)
           (COND X
                 (COND (CDR X) (COND (LTE (CAR X) (CAR (CDR X))) (ORDERED (CDR X)) NIL) T)
                 T))))

(DEFINE
  (PAIRLIST
   (LAMBDA (X Y)
           (COND X
                 (COND Y
                       (CONS (CONS (CAR X) (CAR Y)) (PAIRLIST (CDR X) (CDR Y)))
                       (CONS (CONS (CAR X) NIL) (PAIRLIST (CDR X) NIL)))
                 NIL))))

(DEFINE
  (PLUS (LAMBDA (X Y) (COND X (ADD1 (PLUS (SUB1 X) Y)) Y))))

(DEFINE
  (REVERSE
   (LAMBDA (X) (COND X (APPEND (REVERSE (CDR X)) (CONS (CAR X) NIL)) NIL))))

(DEFINE
  (REVN (LAMBDA (X Y) (COND X (REVERSE (REVN (CDR X) Y)) Y))))

(DEFINE
  (SORT (LAMBDA (X) (COND X (ADDTOLIS (CAR X) (SORT (CDR X))) NIL))))

; SUB1 introduced by BOOT-STRAP

(DEFINE
  (SUBSET
   (LAMBDA (X Y) (COND X (COND (MEMBER (CAR X) Y) (SUBSET (CDR X) Y) NIL) T))))

(DEFINE
  (SUBST
   (LAMBDA
    (X Y Z)
    (COND (EQUAL Y Z) X
          (COND Z (CONS (SUBST X Y (CAR Z)) (SUBST X Y (CDR Z))) NIL)))))

(DEFINE
  (SWAPTREE
   (LAMBDA (X)
           (COND (NODE X)
                 (CONSNODE (SWAPTREE (CDR (CDR X))) (SWAPTREE (CAR (CDR X))))
                 X))))

(DEFINE
  (TET
   (LAMBDA
    (X Y)
    (COND
     Y
     (COND (EQUAL (CAR Y) X) (CONS (CAR Y) (TET X (CDR Y))) (TET X (CDR Y)))
     NIL))))

(DEFINE
  (TGT
   (LAMBDA
    (X Y)
    (COND
     Y
     (COND (NOT (LTE (CAR Y) X)) (CONS (CAR Y) (TGT X (CDR Y))) (TGT X (CDR Y)))
     NIL))))

(DEFINE
  (TIMES (LAMBDA (X Y) (COND X (PLUS Y (TIMES (SUB1 X) Y)) 0))))

(DEFINE
  (EXP (LAMBDA (X Y) (COND Y (TIMES X (EXP X (SUB1 Y))) 1))))

(DEFINE
  (TIPCOUNT
   (LAMBDA (X)
           (COND (NODE X)
                 (PLUS (TIPCOUNT (CAR (CDR X))) (TIPCOUNT (CDR (CDR X))))
                 1))))

(DEFINE
  (TLT
   (LAMBDA
    (X Y)
    (COND Y
          (COND (LT (CAR Y) X) (CONS (CAR Y) (TLT X (CDR Y))) (TLT X (CDR Y)))
          NIL))))

(DEFINE
  (TRIPAPP
   (LAMBDA (X Y Z)
           (COND X
                 (CONS (CAR X) (TRIPAPP (CDR X) Y Z))
                 (COND Y (CONS (CAR Y) (TRIPAPP X (CDR Y) Z)) Z)))))

(DEFINE
  (UNION
   (LAMBDA (X Y)
           (COND X
                 (COND (MEMBER (CAR X) Y)
                       (UNION (CDR X) Y)
                       (CONS (CAR X) (UNION (CDR X) Y)))
                 Y))))

(DEFINE
  (XOR (LAMBDA (X Y) (COND X (COND Y NIL T) (COND Y T NIL)))))

; -----------------------------------------------------------------
; Section: [THEOREMS] 

; [THEOREMS] TRACK 36 CREATED 17.57 2 9 1973
; [ 21.23 14 SEPT 1973];

; COMMENT 'THEOREMS INVOLVING APPEND, LENGTH AND REVERSE`;

(PROVE
 (T 1 1)
 (EQUAL (APPEND A (APPEND B C)) (APPEND (APPEND A B) C)))

(PROVE
 (T 1 2)
 (IMPLIES (EQUAL (APPEND A B) (APPEND A C)) (EQUAL B C)))

(PROVE
 (T 1 3)
 (EQUAL (LENGTH (APPEND A B)) (LENGTH (APPEND B A))))

(PROVE
 (T 1 4)
 (EQUAL (REVERSE (APPEND A B)) (APPEND (REVERSE B) (REVERSE A))))

(PROVE
 (T 1 5)
 (EQUAL (LENGTH (REVERSE A)) (LENGTH A)))

(PROVE
 (T 1 6)
 (EQUAL (REVERSE (REVERSE A)) A))

(PROVE
 (T 1 7)
 (IMPLIES A (EQUAL (LAST (REVERSE A)) (CAR A))))

(PROVE
 (T 1 8 * UNPROVEN)
 (IMPLIES (EVEN2 N) (EQUAL A (REVN N A))))

; COMMENT 'THEOREMS INVOLVING MEMBER`;

(PROVE
 (T 2 1)
 (IMPLIES (MEMBER A B) (MEMBER A (APPEND B C))))

(PROVE
 (T 2 2)
 (IMPLIES (MEMBER A B) (MEMBER A (APPEND C B))))

(PROVE
 (T 2 3)
 (IMPLIES (AND (NOT (EQUAL A (CAR B))) (MEMBER A B)) (MEMBER A (CDR B))))

(PROVE
 (T 2 4)
 (IMPLIES (OR (MEMBER A B) (MEMBER A C)) (MEMBER A (APPEND B C))))

(PROVE
 (T 2 5)
 (IMPLIES (AND (MEMBER A B) (MEMBER A C)) (MEMBER A (INTERSEC B C))))

(PROVE
 (T 2 6)
 (IMPLIES (OR (MEMBER A B) (MEMBER A C)) (MEMBER A (UNION B C))))

(PROVE
 (T 2 7)
 (IMPLIES (SUBSET A B) (EQUAL (UNION A B) B)))

(PROVE
 (T 2 8)
 (IMPLIES (SUBSET A B) (EQUAL (INTERSEC A B) A)))

(PROVE
 (T 2 9)
 (EQUAL (MEMBER A B) (NOT (EQUAL (ASSOC A (PAIRLIST B C)) NIL))))

; COMMENT 'THEOREMS INVOLVING MAPLIST`;

(PROVE
 (T 3 1)
 (EQUAL (MAPLIST (APPEND A B) C) (APPEND (MAPLIST A C) (MAPLIST B C))))

(PROVE
 (T 3 2)
 (EQUAL (LENGTH (MAPLIST A B)) (LENGTH A)))

(PROVE
 (T 3 3)
 (EQUAL (REVERSE (MAPLIST A B)) (MAPLIST (REVERSE A) B)))

; COMMENT 'THEOREMS INVOLVING MISC LISP FUNCTIONS`;

(PROVE
 (T 4 1)
 (EQUAL (LIT (APPEND A B) C D) (LIT A (LIT B C D) D)))

(PROVE
 (T 4 2)
 (IMPLIES (AND (BOOLEAN A) (BOOLEAN B))
          (EQUAL (AND (IMPLIES A B) (IMPLIES B A)) (EQUAL A B))))

(PROVE
 (T 4 3)
 (EQUAL (ELEMENT B A) (ELEMENT (APPEND C B) (APPEND C A))))

(PROVE
 (T 4 4)
 (IMPLIES (ELEMENT B A) (MEMBER (ELEMENT B A) A)))

(PROVE
 (T 4 5)
 (EQUAL (CDRN C (APPEND A B)) (APPEND (CDRN C A) (CDRN (CDRN A C) B))))

(PROVE
 (T 4 6)
 (EQUAL (CDRN (APPEND B C) A) (CDRN C (CDRN B A))))

(PROVE
 (T 4 7)
 (EQUAL (EQUAL A B) (EQUAL B A)))

(PROVE
 (T 4 8)
 (IMPLIES (AND (EQUAL A B) (EQUAL B C)) (EQUAL A C)))

(PROVE
 (T 4 9)
 (IMPLIES (AND (BOOLEAN A) (AND (BOOLEAN B) (BOOLEAN C)))
          (EQUAL (EQUAL A (EQUAL B C)) (EQUAL (EQUAL A B) C))))

; COMMENT 'THEOREMS INVOLVING ARITHMETIC`;

(PROVE
 (T 5 1)
 (implies (and (numberp n) ; Discrepancy:  Added explicit hyps
               (numberp m))
          (EQUAL (PLUS N M) (PLUS M N))))

(PROVE
 (T 5 2)
 (implies (and (numberp n) ; Discrepancy:  Added explicit hyps
               (and (numberp m)
                    (numberp k)))
          (EQUAL (PLUS N (PLUS M K)) (PLUS (PLUS N M) K))))

(PROVE
 (T 5 5/2) ; = (T 5 2.5)
 (implies (and (numberp k) ; Discrepancy:  Added explicit hyps
               (and (numberp l)
                    (numberp n)))
          (EQUAL (PLUS (PLUS K L) N) (PLUS (PLUS L N) K))))

(PROVE
 (T 5 3)
 (implies (and (numberp n) ; Discrepancy:  Added explicit hyps
               (numberp m))
          (EQUAL (TIMES N M) (TIMES M N))))


(PROVE
 (T 5 4)
 (implies (and (numberp n) ; Discrepancy:  Added explicit hyps
               (and (numberp m)
                    (numberp k)))
          (EQUAL (TIMES N (PLUS M K)) (PLUS (TIMES N M) (TIMES N K)))))

(PROVE
 (T 5 5)
 (implies (and (numberp n) ; Discrepancy:  Added explicit hyps
               (and (numberp m)
                    (numberp k)))
          (EQUAL (TIMES N (TIMES M K)) (TIMES (TIMES N M) K))))

(PROVE
 (T 5 6)
 (implies (numberp n) ; Discrepancy:  Added explicit hyp
          (EVEN1 (DOUBLE N))))

(PROVE
 (T 5 7)
 (implies (numberp n) ; Discrepancy:  Added explicit hyp
          (EQUAL (HALF (DOUBLE N)) N)))

(PROVE
 (T 5 3)
 (implies (numberp n) ; Discrepancy:  Added explicit hyp
          (IMPLIES (EVEN1 N) (EQUAL (DOUBLE (HALF N)) N))))

(PROVE
 (T 5 9)
 (implies (numberp n) ; Discrepancy:  Added explicit hyp
          (EQUAL (DOUBLE N) (TIMES 2 N))))

(PROVE
 (T 5 10)
 (implies (numberp n) ; Discrepancy:  Added explicit hyp
          (EQUAL (DOUBLE N) (TIMES N 2))))

(PROVE
 (T 5 11)
 (implies (numberp n) ; Discrepancy:  Added explicit hyp
          (EQUAL (EVEN1 N) (EVEN2 N))))

; COMMENT 'THEOREMS INVOLVING ORDERING RELATIONS`;

(PROVE
 (T 6 1)
 (GT (LENGTH (CONS A B)) (LENGTH B)))

(PROVE
 (T 6 2)
 (IMPLIES (AND (GT A B) (GT B C)) (GT A C)))

(PROVE
 (T 6 3)
 (IMPLIES (GT A B) (NOT (GT B A))))

(PROVE
 (T 6 4)
 (LTE A (APPEND B A)))

(PROVE
 (T 6 5)
 (OR (LTE A B) (LTE B A)))

(PROVE
 (T 6 6)
 (OR (GT A B) (OR (GT B A) (EQUAL (LENGTH A) (LENGTH B)))))

(PROVE
 (T 6 7)
 (EQUAL (MONOT2P A) (MONOT1 A)))

(PROVE
 (T 6 8)
 (ORDERED (SORT A)))

(PROVE
 (T 6 9)
 (IMPLIES (AND (MONOT1 A) (MEMBER B A)) (EQUAL (CAR A) B)))

(PROVE
 (T 6 10)
 (LTE (CDRN A B) B))

(PROVE
 (T 6 11 *)
 (EQUAL (MEMBER A (SORT B)) (MEMBER A B)))

(PROVE
 (T 6 12)
 (EQUAL (LENGTH A) (LENGTH (SORT A))))

(PROVE
 (T 6 13 *)
 (EQUAL (COUNT A B) (COUNT A (SORT B))))

(PROVE
 (T 6 14)
 (IMPLIES (ORDERED A) (EQUAL A (SORT A))))

(PROVE
 (T 6 15)
 (IMPLIES (ORDERED (APPEND A B)) (ORDERED A)))

(PROVE
 (T 6 16)
 (IMPLIES (ORDERED (APPEND A B)) (ORDERED B)))

(PROVE
 (T 6 17 *)
 (EQUAL (EQUAL (SORT A) A) (ORDERED A)))

(PROVE
 (T 6 18)
 (LTE (HALF A) A))

(PROVE
 (T 6 19)
 (IMPLIES (AND (ORDERED A) (AND (ORDERED B) (LTE (LAST A) (CAR B))))
          (ORDERED (APPEND A B))))

; COMMENT 'THEOREMS INVOLVING TREE STRUCTURED LISTS`;

(PROVE
 (T 7 1)
 (EQUAL (COPY A) A))

(PROVE
 (T 7 2)
 (EQUAL (EQUALP A B) (EQUAL A B)))

(PROVE
 (T 7 3)
 (EQUAL (SUBST A A B) B))

(PROVE
 (T 7 4)
 (IMPLIES (MEMBER A B) (OCCUR A B)))

(PROVE
 (T 7 5)
 (IMPLIES (NOT (OCCUR A B)) (EQUAL (SUBST C A B) B)))

(PROVE
 (T 7 6)
 (EQUAL (EQUALP A B) (EQUALP B A)))

(PROVE
 (T 7 7)
 (IMPLIES (AND (EQUALP A B) (EQUALP B C)) (EQUALP A C)))

(PROVE
 (T 7 8)
 (EQUAL (SWAPTREE (SWAPTREE A)) A))

(PROVE
 (T 7 9)
 (EQUAL (FLATTEN (SWAPTREE A)) (REVERSE (FLATTEN A))))

(PROVE
 (T 7 10)
 (EQUAL (LENGTH (FLATTEN A)) (TIPCOUNT A)))

; COMMENT 'THEOREMS ABOUT BINARY ARITHMETIC`;

; Discrepancy: This formula has been deleted from the standard proveall.
; I believe it was never proved by PLTP and it cannot be proved by PLTP(A).
; See standard-proveall-failures.lisp for a discussion.

; (PROVE
;  (T 8 1 *)
;  (EQUAL (BINARYOF (PLUS N M)) (BINADD (BINARYOF N) (BINARYOF M))))

(PROVE
 (T 8 2)
 (implies (numberp n)
          (EQUAL (LINEAR (BINARYOF N)) N)))

; Discrepancy: This formula has been deleted from the standard proveall.
; I believe it was never proved by PLTP and it cannot be proved by PLTP(A).
; See standard-proveall-failures.lisp for a discussion.

; (PROVE
;  (T 8 3)
;  (EQUAL (LINEAR (CDR (BINARYOF N))) (HALF N)))

