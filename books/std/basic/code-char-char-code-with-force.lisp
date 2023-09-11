; Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This little book contains versions before September 4, 2023 of two defaxiom
; events from ACL2 source file axioms.lisp.  The current versions in
; axioms.lisp were created by eliminating forcing from the hypotheses.  Books
; that certified with ACL2 before that change but not after that change can
; probably be made to certify by (locally) including this book.

(in-package "ACL2")

(defthm code-char-char-code-is-identity-forced
  (implies (force (characterp c))
           (equal (code-char (char-code c)) c)))

(defthm char-code-code-char-is-identity-forced
  (implies (and (force (integerp n))
                (force (<= 0 n))
                (force (< n 256)))
           (equal (char-code (code-char n)) n)))
