; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book is based on books/demos/defabsstobj-example-1.lisp, which has
; the following header.

; Copyright (C) 2012, Regents of the University of Texas
; Written by Matt Kaufmann, July, 2012 (updated Nov. and Dec., 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See impl-top.lisp for explanation, and see gen-support.lisp for an analogous
; book to support a generic stobj that is also based on
; books/demos/defabsstobj-example-1.lisp.

(in-package "ACL2")

(include-book "gen-support")

(DEFTHM CREATE-ST2{CORRESPONDENCE}
  (ST$CORR (CREATE-ST$C) (CREATE-ST$A))
  :RULE-CLASSES NIL)

(DEFTHM CREATE-ST2{PRESERVED}
  (ST$AP (CREATE-ST$A))
  :RULE-CLASSES NIL)

(DEFTHM LOOKUP2{CORRESPONDENCE}
  (IMPLIES (AND (ST$CORR ST$C ST2)
                (INTEGERP I)
                (<= 0 I)
                (<= I 49)
                (ST$AP ST2))
           (EQUAL (MEM$CI I ST$C)
                  (LOOKUP$A I ST2)))
  :hints (("Goal" :use ((:instance lookup{correspondence} (st st2)))))
  :RULE-CLASSES NIL)

(DEFTHM LOOKUP2{GUARD-THM}
  (IMPLIES (AND (ST$CORR ST$C ST2)
                (INTEGERP I)
                (<= 0 I)
                (<= I 49)
                (ST$AP ST2))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (MEM$C-LENGTH ST$C))))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE2{CORRESPONDENCE}
  (IMPLIES (AND (ST$CORR ST$C ST2)
                (INTEGERP I)
                (<= 0 I)
                (<= I 49)
                (INTEGERP V)
                (<= 0 V)
                (ST$AP ST2)
                (MEM$C-ENTRYP V))
           (ST$CORR (UPDATE-MEM$CI I V ST$C)
                    (UPDATE$A I V ST2)))
  :hints (("Goal" :use ((:instance update{correspondence} (st st2)))))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE2{GUARD-THM}
  (IMPLIES (AND (ST$CORR ST$C ST2)
                (INTEGERP I)
                (<= 0 I)
                (<= I 49)
                (INTEGERP V)
                (<= 0 V)
                (ST$AP ST2)
                (MEM$C-ENTRYP V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (MEM$C-LENGTH ST$C))
                (INTEGERP V)
                (<= 0 V)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE2{PRESERVED}
  (IMPLIES (AND (INTEGERP I)
                (<= 0 I)
                (<= I 49)
                (INTEGERP V)
                (<= 0 V)
                (ST$AP ST2)
                (MEM$C-ENTRYP V))
           (ST$AP (UPDATE$A I V ST2)))
  :RULE-CLASSES NIL)

(DEFTHM MISC2{CORRESPONDENCE}
  (IMPLIES (AND (ST$CORR ST$C ST2) (ST$AP ST2))
           (EQUAL (MISC$C+ ST$C) (MISC$A ST2)))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-MISC2{CORRESPONDENCE}
  (IMPLIES (AND (ST$CORR ST$C ST2) (ST$AP ST2))
           (ST$CORR (UPDATE-MISC$C V ST$C)
                    (UPDATE-MISC$A V ST2)))
  :hints (("Goal" :use ((:instance update-misc{correspondence} (st st2)))))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-MISC2{PRESERVED}
  (IMPLIES (ST$AP ST2)
           (ST$AP (UPDATE-MISC$A V ST2)))
  :RULE-CLASSES NIL)

(defabsstobj st2
  :foundation st$c
  :recognizer (st2p :logic st$ap :exec st$cp)
  :creator (create-st2 :logic create-st$a :exec create-st$c)
  :corr-fn st$corr
  :exports ((lookup2 :logic lookup$a :exec mem$ci)
            (update2 :logic update$a :exec update-mem$ci)
            (misc2 :logic misc$a :exec misc$c+)
            (update-misc2 :logic update-misc$a :exec update-misc$c))
  :attachable t)

(encapsulate
  ()
   
  (local (include-book "std/testing/must-fail" :dir :system))

  (local
   (must-fail ; Misc2 causes an error since its :exec is misc$c+, as with gen.
    (value-triple (misc2 st2)))))
