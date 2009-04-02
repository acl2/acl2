(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "defs-out")

(LOCAL (INCLUDE-BOOK "lemmas-in"))

(LOCAL (INCLUDE-BOOK "defs-eq"))

(LOCAL (IN-THEORY (THEORY '%-REMOVAL-THEORY)))

(DEFTHM LEMMA-1
        (IMPLIES (TRUE-LISTP X)
                 (EQUAL (G2 X Y) NIL))
        :HINTS (("Goal" :USE %LEMMA-1)))

