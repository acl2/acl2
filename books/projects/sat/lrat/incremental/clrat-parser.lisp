; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Reader for compressed LRAT ("clrat") files

; The description of the binary format is in the DRAT-trim public
; repository. You can get it at:

; git clone https://github.com/marijnheule/drat-trim.git

; The description is in the README.md file.  It is also here:
; https://github.com/marijnheule/drat-trim

; Work was originally started by Nathan Wetzler, but has been modified
; extensively by Warren Hunt and Matt Kaufmannn so as to produce a
; faster, lrat proof checker.

; We read two files: a formula file and a proof file.  A proof step in
; the proof file is either a deletion step

;  d i1 ... ik 0

; or else an addition step

;  j l1 l2 ... lk 0 d1 d2 ... dm -e1 f11 ... f1{m_1} -e2 f21 ... f2{m_2} ... 0

; where:

; - j is the index of a clause C = {l1, l2, ..., lk} to be added redundantly;
; - d1 ... dm are indices of unit clauses for RUP from the negation of C;
; - e1 < e2 < ... are indices of existing (non-deleted) clauses; and
; - ei is a RAT clause Ci, and fi1 ... fi{m_i} are indices of unit clauses for
;   RUP from the union of the negation of C with the negation of Ci \ {-l1}.

; Note that each index j must exceed all preceding clause indices.

; See the function LRAT-GUARD (below) for a description of our
; string/file reading invariant.

; See the function CHECK-LRAT-LINE-TO-LF (below) for a description of
; our coding approach.

; (in-package "ACL2")
(in-package "LRAT")

(include-book "std/util/bstar" :dir :system)
(include-book "limits")

; (include-book "misc/disassemble" :dir :system)


; Some miscellaneous definitions.

(defmacro with-arithmetic-help-5 (&rest forms)
  `(encapsulate
    ()
    (local (include-book "arithmetic-5/top" :dir :system))
    (set-default-hints #!acl2'((nonlinearp-default-hint
                                stable-under-simplificationp
                                hist
                                pspv)))
    ,@forms))


; Reverse function

(defun my-rev1 (x a)
  (declare (xargs :guard (true-listp a)))
  (if (atom x)
      a
    (my-rev1 (cdr x) (cons (car x) a))))

(defthm true-listp-my-rev1
  (implies (true-listp a)
           (true-listp (my-rev1 x a))))

(defthm nat-listp-my-rev1
  (implies (and (nat-listp x)
                (nat-listp a))
           (nat-listp (my-rev1 x a))))

(defthm integer-listp-my-rev1
  (implies (and (integer-listp x)
                (integer-listp a))
           (integer-listp (my-rev1 x a))))

(defthm alistp-my-rev1
  (implies (and (alistp x)
                (alistp a))
           (alistp (my-rev1 x a))))

(defthm character-listp-my-rev1
  (implies (and (character-listp x)
                (character-listp a))
           (character-listp (my-rev1 x a))))

(in-theory (disable my-rev1))


(defun my-rev (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (my-rev1 x nil)))

(defthm true-listp-my-rev
  (true-listp (my-rev x)))

(defthm nat-listp-my-rev
  (implies (nat-listp x)
           (nat-listp (my-rev x))))

(defthm integer-listp-my-rev
  (implies (integer-listp x)
           (integer-listp (my-rev x))))

(defthm alistp-my-rev
  (implies (alistp x)
           (alistp (my-rev x))))

(defthm character-listp-my-rev
  (implies (character-listp x)
           (character-listp (my-rev x))))

(in-theory (disable my-rev))


(defun my-app (x y)
  (declare (xargs :guard t))
  (if (atom x)
      y
    (cons (car x)
          (my-app (cdr x) y))))

(defthm true-listp-my-app
  (implies (true-listp y)
           (true-listp (my-app x y))))

(defthm integer-listp-app
  (implies (and (integer-listp x)
                (integer-listp y))
           (integer-listp (my-app x y))))

(in-theory (disable my-app))


(with-arithmetic-help-5
 (defthm logand-less-than-or-equal
   (implies (natp x)
            (and (<= (logand x y) x)
                 (<= (logand y x) x)))
   :hints (("Goal" :cases ((equal x 0))))
   :rule-classes :linear))

(with-arithmetic-help-5
 (defthm logand-greater-or-equal-to-zero
   (implies (or (natp x) (natp y))
            (and (integerp (logand x y))
                 (<= 0 (logand x y))
                 ;; (integerp (logand y x))
                 ;; (<= 0 (logand y x))
                 ))
   :hints (("Goal" :cases ((equal x 0))))
   :rule-classes :type-prescription))

; ASH rules

(with-arithmetic-help-5
 (defthm ash-negative-shift-makes-input-smaller
   (implies (and (integerp x)
                 (< 0 x)
                 (integerp shift)
                 (< shift 0))
            (< (ash x shift) x))
   :rule-classes :linear))

(with-arithmetic-help-5
 (defthm helper
   (implies (< 127 nat)
            (< (ash nat -7)
               nat))
   :rule-classes (:rewrite :linear)))

(with-arithmetic-help-5
 (defthm positivep-ash
   (implies (<= 0 x)
            (<= 0 (ash x n)))
   :rule-classes :type-prescription))

(in-theory (disable ash))

(with-arithmetic-help-5
 (defthm nat-to-clrat-num-helper
   (implies (and (integerp nat) ; needed for ACL2(r) proof
                 (< 127 nat))
            (< (integer-abs (ash nat -7))
               (acl2-count nat)))))

(defun list-of-integer-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (integer-listp (car x))
         (list-of-integer-listp (cdr x)))))


(defun-inline char-to-nat (ch)

; Convert character decimal digit to natural number.  If CH is '0' to
; '9', return corresponding natural number; otherwise NIL

  (declare (xargs :guard (characterp ch)))
  (let ((code (u59 (char-code ch))))
    (and (>= code 48)
         (<= code 57)
         (- code 48))))

(defthm natp-or-null-char-to-nat
  (or (natp (char-to-nat ch))
      (null (char-to-nat ch)))
  :rule-classes :type-prescription)

(defthm natp-char-to-nat
  (implies (char-to-nat ch)
           (natp (char-to-nat ch))))

(defthm char-to-nat-is-less-than-10
  (implies (char-to-nat ch)
           (< (char-to-nat ch) 10))
  :rule-classes :linear)

(in-theory (disable char-to-nat))


; Our CLRAT reader processes the contents of a file and makes it ready
; for our SAT-checking algorithm..  This proof processing is done
; incrementally.  We process a SAT-proof file by reading some of it,
; processing what we read, and then, reading some more of the file and
; follow that with more processing, and so on.  We repeat this process
; until an entire file has been processed.


(defun lrat-guard (str len pos)

; Guard for string processing functions.  The requirement that LEN is
; less than 2^56 ensures that keeping track of our position can be
; done with FIXNUMs.  The diagram below is meant to represent a string.

; POS is a natural number <= LEN.
; LEN is the length of STR.
; "_ _ _ _ _ _ _ _ _ _ _ _ _ ... _ _ _ _" is some string STR.
;            ^                           ^
;           POS                          LEN

; Functions that accept a STR, POS, and LEN, and return a position,
; POS, are proven to return a position that is in bounds.

  (declare (xargs :guard t))
  (and (stringp str)
       (natp len)
       (natp pos)
       (equal len (length str))
       (<= pos len)
       (< len *2^56*)))


(defun check-lrat-line-to-lf (str len pos)  ; This function unused.

; Check STR up to a #\LineFeed for allowable characters; this is a
; general syntatic check that a file only contains characters that can
; be converted into a proof.  This function shows our idiomatic
; approach to functions that are guarded by our recognizer LRAT-GUARD
; (defined just above).  We we reach the end, we return LEN.  We also
; return LEN when we recognize an error condition.

; We use a certain idiomatic style here, which we follow in later
; functions.

  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))
  ;; Declare LEN and POS to be 56-bit natural (fixnum) numbers.
  (let* ((len (u56 len))
         (pos (u56 pos)))

    ;; LEN is returned whenever we reach `the end'.
    (if (mbe :logic (zp (- len pos))
             :exec  (>= pos len))
        len ; At end

      (let ((ch  (char str pos)))
        (if (eql ch #\Newline)
            pos ; At end of line, return POS.

          (if (not (or (eql ch #\Space)
                       (eql ch #\Tab)
                       (eql ch #\-)
                       (eql ch #\d) ; Part of deletion command
                       (char-to-nat ch)))

              (prog2$
               (er hard?
                   "check-lrat-line-to-lf:  Check byte at position ~x0.~%"
                   pos)
               len) ; If unrecognized character, report at end

            (let ((pos+1 (u59 (1+ pos))))
              (check-lrat-line-to-lf str len pos+1))))))))


(defun find-next-space (str len pos)

; Starting at POS, find next space character.

  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))
  (b* ((pos (u56 pos))
       (len (u56 len))
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
            len) ; File end
       (ch (char str pos))
       ((if (eql ch #\Space)) pos)
       (pos+1 (u56 (1+ pos))))
    (find-next-space str len pos+1)))

(defthm natp-find-next-space
  (implies (and (natp len) (natp pos))
           (natp (find-next-space str len pos)))
  :rule-classes :type-prescription)

(defthm bound-find-next-space
  (implies (and (natp len) (natp pos) (<= pos len))
           (and (<= pos (find-next-space str len pos))
                (<= (find-next-space str len pos) len)))
  :rule-classes (:rewrite :linear))

(in-theory (disable find-next-space))


(defun find-lf (str len pos)

; Find next #\Newline character

  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos)))
           (type string str))
  (let ((len (u56 len))
        (pos (u56 pos)))
    (if (mbe :logic (zp (- len pos))
             :exec  (>= pos len))
        len
      (let ((ch (char str pos)))
        (if (eql ch #\Newline)
            pos
          (let ((pos+1 (u59 (1+ pos))))
            (find-lf str len pos+1)))))))

(defthm integerp-find-lf
  (implies (and (natp pos) (natp len))
           (integerp (find-lf str len pos)))
  :rule-classes :type-prescription)

(defthm natp-find-lf
  (implies (and (natp pos) (<= pos len))
           (and (<= 0 (find-lf str len pos))
                (<= (find-lf str len pos) len)))
  :rule-classes :linear)

(defthm pos-<=-find-lf
  (implies (<= pos len)
           (<= pos (find-lf str len pos)))
  :rule-classes (:linear :rewrite))

(in-theory (disable find-lf))


(defun lrat-pos-skip-spaces (str len pos)

; Skip space characters, leave POS at first non-space character

  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))
  (b* ((len (u56 len))
       (pos (u56 pos))
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        len)
       (ch (char str pos))
       ((when (not (eql ch #\Space))) pos)
       (pos+1 (u56 (1+ pos))))
    (lrat-pos-skip-spaces str len pos+1)))

(defthm natp-lrat-pos-skip-spaces
  (implies (and (natp len) (natp pos))
           (natp (lrat-pos-skip-spaces str len pos)))
  :rule-classes :type-prescription)

(defthm pos-fact-lrat-pos-skip-spaces
  (implies (and (natp len) (natp pos) (<= pos len)) ; (lrat-guard str len pos)
           (and (<= pos (lrat-pos-skip-spaces str len pos))
                (<= (lrat-pos-skip-spaces str len pos) len)))
  :hints
  (("Goal" :induct (lrat-pos-skip-spaces str len pos)))
  :rule-classes (:rewrite :linear))

(in-theory (disable lrat-pos-skip-spaces))


(with-arithmetic-help-5
 (defun lrat-nat1 (str len pos n)

; Natural number reader.  Can read (approximately) 18-decimal-digit
; numbers; otherwise, it will fail.  Returns natural number (fixnum).

   (declare (xargs :guard (and (lrat-guard str len pos)
                               (natp n)
                               (< n *2^60*))
                   :measure (nfix (- len pos))))
   (let* ((len (u56 len))
          (pos (u56 pos))
          (n   (u60 n)))
     (if (mbe :logic (zp (- len pos))
              :exec  (>= pos len))
         0 ; File end

       (let* ((ch (char str pos))
              (digit (char-to-nat ch)))

         (if (null digit)
             n ; At end of base-10 numerals, return answer

           (if (not (< n *2^56*))
               (prog2$ (er hard? 'lrat-nat1
                           "lrat-nat1:  Number too large; position: ~x0.~%"
                           pos)
                       0)
             (let* ((digit (u04 digit))
                    (n   (u56 n))
                    (2n  (u57 (+ n n)))
                    (8n  (u59 (mbe :logic (* 8 n) :exec (ash n 3))))
                    (10n (u60 (+ 8n 2n)))

                    ;; (10n (u60 (* n 10))) creates a big-num call
                    ;; And this code generated for 10n is
                    ;; unnecessarily large

                    ;; I find this strange -- that adding something
                    ;; (anything positive) to a u60 is still thought
                    ;; to be a u60.  Possibly, it is known that 10n
                    ;; leaves 6n left of a u60, where n is 2*56*.

                    (10n+digit (u60 (+ digit 10n)))
                    (pos+1 (u59 (1+ pos))))
               (lrat-nat1 str len pos+1 10n+digit)))))))))

(defthm natp-lrat-nat1
  (implies (natp n)
           (natp (lrat-nat1 str len pos n)))
  :hints
  (("Goal"
    :in-theory (disable length)
    :induct (lrat-nat1 str len pos n)))
  :rule-classes :type-prescription)

(defthm bound-lrat-nat1
   (implies (and (natp n) (< n *2^60*))
            (and (<= 0 (lrat-nat1 str len pos n))
                 (< (lrat-nat1 str len pos n) *2^60*)))
   :hints
   (("Goal"
     :in-theory (disable length)
     :induct (lrat-nat1 str len pos n)))
   :rule-classes :linear)

(in-theory (disable lrat-nat1))


(defun lrat-nat (str len pos)

; Read natural number starting at POS

  (declare (xargs :guard (lrat-guard str len pos)))
  (b* ((pos (u56 pos))
       (len (u56 len))
       ((unless (< pos len)) 0)
       (ch (char str pos))
       (val (char-to-nat ch))
       ((unless val) 0)
       ((if (= val 0)) 0))
    (lrat-nat1 str len pos 0)))

(defthm natp-lrat-nat
  (natp (lrat-nat str len pos))
  :rule-classes :type-prescription)

(defthm bound-lrat-nat
   (and (<= 0 (lrat-nat str len pos))
        (< (lrat-nat str len pos) *2^60*))
  :rule-classes :linear)

(in-theory (disable lrat-nat))


(defun lrat-int (str len pos)

; Read integer starting at POS

  (declare (xargs :guard (lrat-guard str len pos)))
  (b* ((pos (u56 pos))
       (len (u56 len))
       ((unless (< pos len)) 0)
       (ch  (char str pos))
       ((if (not (eql ch #\-)))
        (lrat-nat str len pos))
       (pos+1 (u56 (1+ pos)))
       ((unless (< pos+1 len)) 0))
    (- (lrat-nat str len pos+1))))

(defthm integerp-lrat-int
  (integerp (lrat-int str len pos))
  :rule-classes :type-prescription)

(defthm bound-lrat-int
   (and (< (- *2^60*) (lrat-int str len pos))
        (< (lrat-int str len pos) *2^60*))
  :rule-classes :linear)

(in-theory (disable lrat-int))


(defun lrat-flg-int (str len pos)

; Read an integer and return (mv <end-of-integer-pos> <integer>)

  (declare (xargs :guard (lrat-guard str len pos)))
  (b* ((pos (u56 pos))
       (len (u56 len))
       (space-pos (u56 (find-next-space str len pos)))
       ((unless (< pos space-pos)) (mv nil 0))
       (lrat-int (s61 (lrat-int str len pos))))
    (mv space-pos lrat-int)))

(defthm natp-pos-lrat-flg-int
  (implies (and (natp pos) (natp len)
                (car (lrat-flg-int str len pos)))
           (natp (car (lrat-flg-int str len pos))))
  :hints
  (("Goal"
    :in-theory (disable length))))

(defthm bound-lrat-flg-int
  (implies (and (natp pos) (natp len) (<= pos len)
                (car (lrat-flg-int str len pos)))
           (and (<= 0 (car (lrat-flg-int str len pos)))
                (<= (car (lrat-flg-int str len pos)) len)))
  :hints
  (("Goal"
    :in-theory (disable length)))
  :rule-classes :linear)

(defthm pos-has-increased-lrat-flg-int-1
  (implies (and (natp pos) (natp len)
                (<= pos pos1)
                (car (lrat-flg-int str len pos1)))
           (< pos (car (lrat-flg-int str len pos1))))
  :rule-classes :linear)

(defthm car-lrat-flag-int-less-than-len
  (implies (and (lrat-guard str len pos)
                (or (car (lrat-flg-int str len pos))
                    (integerp (lrat-flg-int str len pos))))
           (<= (car (lrat-flg-int str len pos)) len))
  :rule-classes :linear)

(defthm mv-nth-1-natp-lrat-flg-int
  (implies (car (lrat-flg-int str len pos))
           (integerp (mv-nth 1 (lrat-flg-int str len pos))))
  :rule-classes (:rewrite :type-prescription))

(encapsulate
  ()
  (local
   (defthm one-time-math-fact
     ;; Note, this is also true without the INTEGERP hypotheses
     (implies (and (integerp i)
                   (integerp n))
              (iff (< (- i) (- n))
                   (< n i)))
     ;; By using IFF (instead of EQUAL), linear arithmetic is given
     ;; the chance to work -- which it does; otherwise, it fails.
     :rule-classes ((:rewrite :corollary
                              (implies (and (integerp i)
                                            (integerp n))
                                       (equal (< (- i) (- n))
                                              (< n i)))))))

  (defthm mv-nth1-lrat-flg-int-abs-less-than-*2^60*
    (implies (car (lrat-flg-int str len pos))
             (and (< (- *2^60*) (mv-nth 1 (lrat-flg-int str len pos)))
                  (< (mv-nth 1 (lrat-flg-int str len pos)) *2^60*)))
    :hints
    (("Goal" :do-not-induct t))))

(in-theory (disable lrat-flg-int))


(defun lrat-flg-nat-list-until-0 (str len pos lst)

; Read list of natural numbers until a stand-alone "0" is found.
; Return (mv <pos-after-0> <nat-list>)

  (declare (xargs :guard (and (lrat-guard str len pos)
                              (nat-listp lst))
                  :measure (nfix (- len pos))))
  (b* ((pos (u56 pos))
       (len (u56 len))
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        (mv len nil))

       ;; Skip spaces
       (pos-after-spaces (u56 (lrat-pos-skip-spaces str len pos)))
       ((unless (< pos-after-spaces len)) (mv len nil))

       ;; Read natural number
       (nat-read (u60 (lrat-nat str len pos-after-spaces)))

       ;; If zero, stop
       ((if (= nat-read 0)) (mv (1+ pos-after-spaces) (my-rev lst)))

       ;; Locate space after number
       (pos-after-nat (find-next-space str len pos-after-spaces))

       ;; For measure
       ((unless (< pos pos-after-nat)) (mv len lst)))

    (lrat-flg-nat-list-until-0 str len pos-after-nat (cons nat-read lst))))

(defthm natp-lrat-flg-nat-list-until-0
  (implies (and (natp len) (natp pos))
           (natp (car (lrat-flg-nat-list-until-0 str len pos lst))))
  :rule-classes :type-prescription)

(defthm bound-lrat-flg-nat-list-until-0
  (implies (and (natp len) (natp pos) (<= pos len))
           (and (<= pos (car (lrat-flg-nat-list-until-0 str len pos lst)))
                (<= (car (lrat-flg-nat-list-until-0 str len pos lst)) len)))
  :rule-classes :linear)

(defthm nat-listp-lrat-flg-nat-list-until-0
  (implies (nat-listp lst)
           (nat-listp (mv-nth 1 (lrat-flg-nat-list-until-0 str len pos lst)))))

(in-theory (disable lrat-flg-nat-list-until-0))


(defun lrat-flg-int-list-until-0 (str len pos lst)

; Read list of INTEGERs until "0" found.
; Return (mv <pos-after-0> <int-list>);  When Error or End, then (= pos len)

  (declare (xargs :guard (and (lrat-guard str len pos)
                              (integer-listp lst))
                  :measure (nfix (- len pos))))
  (b* ((pos (u56 pos))
       (len (u56 len))
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        (mv len nil))

       ;; Skip spaces
       (pos-after-spaces (u56 (lrat-pos-skip-spaces str len pos)))
       ((unless (< pos-after-spaces len)) (mv len nil))

       ;; Read integer
       (int-read (s61 (lrat-int str len pos-after-spaces)))

       ;; If zero, stop
       ((if (= int-read 0)) (mv (1+ pos-after-spaces) (my-rev lst)))

       ;; Locate space after number
       (pos-after-int (find-next-space str len pos-after-spaces))

       ;; For measure; !!! This is an error return.
       ((unless (< pos pos-after-int)) (mv len lst)))

    (lrat-flg-int-list-until-0 str len pos-after-int (cons int-read lst))))

(defthm natp-lrat-flg-int-list-until-0
  (implies (and (natp len) (natp pos))
           (natp (car (lrat-flg-int-list-until-0 str len pos lst))))
  :rule-classes :type-prescription)

(defthm bound-lrat-flg-int-list-until-0
  (implies (and (natp len) (natp pos) (<= pos len))
           (and (<= pos (car (lrat-flg-int-list-until-0 str len pos lst)))
                (<= (car (lrat-flg-int-list-until-0 str len pos lst)) len)))
  :rule-classes :linear)

(defthm integer-listp-lrat-flg-int-list-until-0
  (implies (integer-listp lst)
           (integer-listp (mv-nth 1 (lrat-flg-int-list-until-0 str len pos lst)))))

(in-theory (disable lrat-flg-int-list-until-0))



(defun lrat-flg-nat-list-until-0-or-- (str len pos lst)

; Read list of NATs until "0" or "-" found
; Return (mv pos-after-0 nat-list); Finished when (= pos len)

  (declare (xargs :guard (and (lrat-guard str len pos)
                              (nat-listp lst))
                  :measure (nfix (- len pos))))
  (b* ((pos (u56 pos))
       (len (u56 len))
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        (mv len nil))

       ;; Skip spaces
       (pos-after-spaces (u56 (lrat-pos-skip-spaces str len pos)))
       ((unless (< pos-after-spaces len)) (mv pos lst))

       ;; If "-", then advance POS and return list of naturals
       (ch (char str pos-after-spaces))
       ((if (eql ch #\-)) (mv (1+ pos-after-spaces) (my-rev lst)))

       ;; Read natural number
       (nat-read (u60 (lrat-nat str len pos-after-spaces)))

       ;; If zero, stop, and return list of naturals
       ((if (= nat-read 0)) (mv pos-after-spaces (my-rev lst)))

       ;; Locate space after number
       (pos-after-nat (find-next-space str len pos-after-spaces))

       ;; For measure
       ((unless (< pos pos-after-nat)) (mv len lst)))

    (lrat-flg-nat-list-until-0-or-- str len pos-after-nat (cons nat-read lst))))

(defthm natp-lrat-flg-nat-list-until-0-or--
  (implies (and (natp len) (natp pos))
           (natp (car (lrat-flg-nat-list-until-0-or-- str len pos lst))))
  :rule-classes :type-prescription)

(defthm bound-lrat-flg-nat-list-until-0-or--
  (implies (and (natp len) (natp pos) (<= pos len))
           (and (<= pos (car (lrat-flg-nat-list-until-0-or-- str len pos lst)))
                (<= (car (lrat-flg-nat-list-until-0-or-- str len pos lst)) len)))
  :rule-classes :linear)

(defthm nat-listp-lrat-flg-nat-list-until-0-or--
  (implies (nat-listp lst)
           (nat-listp (mv-nth 1 (lrat-flg-nat-list-until-0-or-- str len pos lst)))))

(in-theory (disable lrat-flg-nat-list-until-0-or--))


(defun lrat-flg-nat-rev-list-of-lists-until-0-or-- (str len pos lst)

; Read sequence of integer lists separated with "-" (which makes it
; look like a negative number)

; Returns (mv pos list-of-nat-list)

  (declare (xargs :guard (and (lrat-guard str len pos)
                              (list-of-integer-listp lst))
                  :measure (nfix (- len pos))))
  (b* ((pos (u56 pos))
       (len (u56 len))
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        (mv len nil))

       ;; At #\0 char?
       (ch (char str pos))
       ((if (eql ch #\0)) (mv (1+ pos) lst))

       ;; Gather next list of natural numbers until "-" or 0 (at end of line)
       ((mv pos-after-int-list int-list)
        (lrat-flg-nat-list-until-0-or-- str len pos nil))

       ;; End-of-File?
       (pos-after-int-list (u56 pos-after-int-list))
       ((unless (< pos pos-after-int-list)) (mv len nil)))

      (lrat-flg-nat-rev-list-of-lists-until-0-or--
       str len pos-after-int-list (cons int-list lst))))

(defthm natp-lrat-flg-nat-rev-list-of-lists-until-0-or--
  (implies
   (and (natp len) (natp pos))
   (natp (car (lrat-flg-nat-rev-list-of-lists-until-0-or-- str len pos lst))))
  :rule-classes :type-prescription)

(defthm bound-lrat-flg-nat-rev-list-of-lists-until-0-or--
  (implies
   (and (natp len) (natp pos) (<= pos len))
   (and (<= pos (car (lrat-flg-nat-rev-list-of-lists-until-0-or-- str len pos lst)))
        (<= (car (lrat-flg-nat-rev-list-of-lists-until-0-or-- str len pos lst)) len)))
  :rule-classes :linear)

(defthm list-integer-listp-lrat-flg-nat-rev-list-of-lists-until-0-or--
  (implies (list-of-integer-listp lst)
           (list-of-integer-listp
            (mv-nth 1 (lrat-flg-nat-rev-list-of-lists-until-0-or-- str len pos lst)))))

(in-theory (disable lrat-flg-nat-rev-list-of-lists-until-0-or--))



(defun lrat-line-mv (str len pos)
  (declare (xargs :guard (lrat-guard str len pos)))

; Expects POS at beginning of line
; Leaves  POS at #\Newline or :eof
; Reads the next line or returns NIL.

  (b* ((pos (u56 pos))
       (len (u56 len))

       ;; Read proof step
       (proof-step (lrat-nat str len pos))
       (pos-after-proof-step (u56 (find-next-space str len pos)))
       ((unless (< pos-after-proof-step len)) (mv len nil))

       ;; Check for exactly one space character
       (ch (char str pos-after-proof-step))
       ((unless (eql ch #\Space)) (mv len nil))
       (pos-after-proof-step+1 (u56 (1+ pos-after-proof-step)))

       ;; Deletion command if ch is #\d
       ((unless (< pos-after-proof-step+1 len)) (mv len nil))
       (ch (char str pos-after-proof-step+1)))

    (if (eql ch #\d)

        ;; proof-step d <nat>* 0
        ;; Deletion:  (cons T <nat>*)
        (b* ((pos-after-proof-step+2 (u56 (1+ pos-after-proof-step+1)))
             ((unless (< pos-after-proof-step+2 len)) (mv len nil))

             ;; Check for space
             (ch (char str pos-after-proof-step+2))
             ((unless (eql ch #\Space)) (mv len nil))

             ;; Read list of naturals until 0
             ((mv pos-after-nat-list nat-list)
              (lrat-flg-nat-list-until-0 str len pos-after-proof-step+2 nil))

             ;; POS-AFTER-NAT-LIST should now be pointing at #\Newline

             ((unless (< pos pos-after-nat-list)) (mv len nat-list))
             ((unless (< pos-after-nat-list len)) (mv len nat-list)))

          (mv pos-after-nat-list (cons t nat-list)))

      ;; proof-step int* 0 <nats-until-0-or-first-neg-number> <negative-int nat*|0>*
      ;; Addition:  (list proof-step <list-of-ints> (rev <list-of-ints>))

      (b* (((mv pos-after-int-list-1 int-list-1)
            (lrat-flg-int-list-until-0 str len pos-after-proof-step+1 nil))
           ((unless (< pos-after-int-list-1 len)) (mv len (cons proof-step int-list-1)))

           ((mv pos-after-int-list-2 int-list-2)
            (lrat-flg-nat-list-until-0-or-- str len pos-after-int-list-1 nil))
           ((unless (< pos-after-int-list-2 len)) (mv len int-list-2))

           ((mv pos-after-int-list-3 int-list-3)
            (lrat-flg-nat-rev-list-of-lists-until-0-or--
             str len pos-after-int-list-2 nil))

           ;; POS-AFTER-INT-LIST-3 should now be pointing at #\Newline

           ((unless (< pos pos-after-int-list-3)) (mv len int-list-3))
           ((unless (< pos-after-int-list-3 len)) (mv len int-list-3))

           ;; Put the answer together
           (ans (cons (cons proof-step int-list-1)
                      (cons int-list-2 int-list-3))))

        (mv pos-after-int-list-3 ans)))))

(defthm natp-lrat-line-mv
  (implies (and (natp len) (natp pos))
           (natp (car (lrat-line-mv str len pos))))
  :rule-classes :type-prescription)

(defthm bound-1-lrat-line-mv
  (implies (and (natp len) (natp pos) (< pos len))
           (and (< pos (car (lrat-line-mv str len pos)))
                (<= (car (lrat-line-mv str len pos)) len)))
  :rule-classes :linear)

(defthm bound-2-lrat-line-mv
  (implies (and (natp len) (natp pos) (<= pos len))
           (and (<= pos (car (lrat-line-mv str len pos)))
                (<= (car (lrat-line-mv str len pos)) len)))
  :rule-classes :linear)

(in-theory (disable lrat-line-mv))


(defun lrat-str-mv (str len pos rev-lines)
  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))

  (b* ((pos (u56 pos))
       (len (u56 len))
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        (mv len rev-lines))

       ;; Process line
       ((mv pos-after-line line) (lrat-line-mv str len pos))
       (more-rev-lines (cons line rev-lines))

       ;; Advance pointer
       ((unless (< pos-after-line len)) (mv len more-rev-lines))
       (pos-after-line+1 (u56 (1+ pos-after-line)))

       ;; Check that POS(ition) advanced -- for measure
       ((unless (< pos pos-after-line+1)) (mv len rev-lines)))

    (lrat-str-mv str len pos-after-line+1 more-rev-lines)))


(defun lrat-str (str len pos rev-lines)
  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))

  (b* ((pos (u56 pos))
       (len (u56 len))
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        rev-lines)

       ;; Process line
       ((mv pos-after-line line) (lrat-line-mv str len pos))
       (more-rev-lines (cons line rev-lines))

       ;; Advance pointer
       ((unless (< pos-after-line len)) more-rev-lines)
       (pos-after-line+1 (u56 (1+ pos-after-line)))

       ;; Check that POS(ition) advanced -- for measure
       ((unless (< pos pos-after-line+1)) rev-lines))

    (lrat-str str len pos-after-line+1 more-rev-lines)))


(defun pos-at-eol (str len pos)

; Find position at end of line.

  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos)))
           (type string str))
  (let ((len (u56 len))
        (pos (u56 pos)))
    (if (mbe :logic (zp (- len pos))
             :exec  (>= pos len))
        len
      (if (eql (char str pos) #\Newline)
          pos
        (pos-at-eol str len (u56 (1+ pos)))))))

(defthm natp-pos-at-eol
  (implies (and (natp pos) (natp len))
           (natp (pos-at-eol str len pos)))
  :hints
  (("Goal" :induct (pos-at-eol str len pos)))
  :rule-classes :type-prescription)

(defthm bound-pos-at-eol
  (implies (lrat-guard str len pos)
           (and (<= pos (pos-at-eol str len pos))
                (<= (pos-at-eol str len pos) len)))
  :hints
  (("Goal"
    :induct (pos-at-eol str len pos)
    :in-theory (disable not length)))
  :rule-classes :linear)

(in-theory (disable pos-at-eol))


(defun pos-at-next-digit-or-minus-char (str len pos)

; Find position of next integer -- skipping blank and comment lines.
; Return LEN if none.  LEN is often return when we discover an error.
; Assuming the LEN is (length STR), (char STR LEN) will not pass a
; guard check.

  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))
  (let ((len (u56 len))
        (pos (u56 pos)))
    (if (mbe :logic (zp (- len pos))
             :exec  (>= pos len))
        len
      (let ((ch (char str pos)))

        ;; !!! Investigate removing this test...
        (if (or (eql ch #\c)  ; CNF-style comments
                (eql ch #\C))

            ;; Skip comment lines...
            (let ((pos-at-eol (pos-at-eol str len pos)))
              (if (< pos (u56 pos-at-eol))
                  (pos-at-next-digit-or-minus-char str len pos-at-eol)
                len))

          (let* ((digit? (char-to-nat ch))
                 (minus-ch (eql ch #\-)))
            (if (or digit? minus-ch)
                pos
              (pos-at-next-digit-or-minus-char str len (u56 (1+ pos))))))))))

(defthm natp-pos-at-next-digit-or-minus-char
  (implies (and (natp pos) (natp len))
           (natp (pos-at-next-digit-or-minus-char str len pos)))
  :hints
  (("Goal" :induct (pos-at-next-digit-or-minus-char str len pos)))
  :rule-classes :type-prescription)

(defthm bound-pos-at-next-digit-or-minus-char
  (implies (lrat-guard str len pos)
           (and (<= pos (pos-at-next-digit-or-minus-char str len pos))
                (<= (pos-at-next-digit-or-minus-char str len pos) len)))
  :hints
  (("Goal"
    :induct (pos-at-next-digit-or-minus-char str len pos)
    :in-theory (disable not length)))
  :rule-classes :linear)

(in-theory (disable pos-at-next-digit-or-minus-char))


(defun lrat-read-file (file-name state)

; Returns a formula data structure, i.e., a list of (index . clause) pairs.
; See formula-p in list-based/lrat-checker.lisp.  Note that the formula is
; _not_ a fast-alist.

  (declare (xargs :guard (stringp file-name)
                  :guard-hints
                  (("Goal" :in-theory (disable acl2::read-file-into-string2)))
                  :stobjs (state)))
  (b* ((str (read-file-into-string file-name))
       ((unless (stringp str))
        (prog2$ (er hard? 'lrat-read-file
                    "lrat-read-file: (read-file-into-string ~x0 .~%" file-name)
                nil))
       (len (length str))
       ((unless (< len *2^56*))
        (prog2$ (er hard? 'lrat-read-file
                    "lrat-read-file:  file ~x0 is too long.~%" file-name)
                nil))
       ;; Skip forward until the beginning of an integer
       (start (pos-at-next-digit-or-minus-char str len 0))
       ((unless (lrat-guard str len start))
        (prog2$ (er hard? 'cnf-read-file
                    "lrat-read-file:  LRAT-GUARD fails.~%")
                nil))
       (rev-lines (lrat-str str len start nil)))
    rev-lines))


(defun cnf-str (str len pos line-num rev-lines)

; Read a string containing a CNF formula, returns a list of
; adddition/deletion commands

; !!! For GCL, check whether a DECLARATION is required for U56, etc.
; !!! Have a look at: ../books/projects/sat/dimacs-reader/reader.lisp
; !!! Write formal spec and make it available on the Web (after
; !!! 4/10/17).

  (declare (xargs :guard (and (lrat-guard str len pos)
                              (natp line-num))
                  :measure (nfix (- len pos))))
  (b* ((len (u56 len))
       (pos (u56 pos))

       ;; End of file?
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        (mv len rev-lines))

       ;; Read list of integers until 0
       ((mv pos-after-int-list int-list)
        (lrat-flg-int-list-until-0 str len pos nil))

       ;; If nothing read or at EOF, return what there is
       ((unless (and (< pos pos-after-int-list)
                     (< pos-after-int-list len)))
        (mv len rev-lines))

       ;; Find the next digit, possibly skipping blank lines
       (pos-at-next-digit-or-minus-char
        (pos-at-next-digit-or-minus-char str len pos-after-int-list))
       ((unless (< pos-after-int-list
                   pos-at-next-digit-or-minus-char))
        (mv len rev-lines))

       ;; Collect this line, and continue...
       (line (cons line-num int-list)))
    (cnf-str str len pos-at-next-digit-or-minus-char (1+ line-num)
             (cons line rev-lines))))

(defthm natp-cnf-str
  (implies (and (natp len) (natp pos))
           (natp (car (cnf-str str len pos line-num rev-lines))))
  :rule-classes :type-prescription)

(defthm bound-cnf-str
  (implies (and (natp len) (natp pos) (<= pos len))
           (and (<= pos (car (cnf-str str len pos line-num rev-lines)))
                (<= (car (cnf-str str len pos line-num rev-lines)) len)))
  :hints
  (("Goal"
    :induct (cnf-str str len pos line-num rev-lines)
    :in-theory (disable not length)))
  :rule-classes :linear)

(in-theory (disable cnf-str))


(defun cnf-read-file (file-name state)

; Returns a formula data structure, i.e., a list of (index . clause) pairs.
; See formula-p in list-based/lrat-checker.lisp.  Note that the formula is
; _not_ a fast-alist.

  (declare (xargs :guard (stringp file-name)
                  :guard-hints
                  (("Goal" :in-theory (disable acl2::read-file-into-string2)))
                  :stobjs (state)))
  (b* ((str (read-file-into-string file-name))
       ((unless (stringp str))
        (prog2$ (er hard? 'cnf-read-file
                    "Unable to read file ~x0." file-name)
                nil))
       (len (length str))
       ((unless (< len *2^56*))
        (prog2$ (er hard? 'cnf-read-file
                    "File ~x0 has length ~x1, which exceeds the maximum of ~
                     2^56-1 (~x2)."
                    file-name len (1- *2^56*))
                nil))
       ;; Skip forward until the beginning of an integer
       (start (pos-at-next-digit-or-minus-char str len 0))
       ((unless (lrat-guard str len start))
        (prog2$ (er hard? 'cnf-read-file
                    "Possible implementation error: LRAT-GUARD failed.~%")
                nil))
       ((mv & rev-lines)
         (cnf-str str len start 1 nil)))
    rev-lines))


; CLRAT Parser

; We now turn our attention to reading Compressed LRAT (CLRAT) files.
; CLRAT files are binary files and must be processed character by
; character.  CLRAT files are broken into lines by reading until one 0
; is found (when reading a deletion command) or until a second 0 is
; found (when reading an addition command).


(defun pos-after-clrat-nums (str len pos)

; Return POS after reading compressed numbers.  The last byte of a
; command is 0; thus we find a byte containing 0 -- and then, we
; finally return the POSition just after the zero byte.

  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))
  ;; Declare LEN and POS to be56-bit natural (fixnum) numbers.
  (b*  ((pos (u56 pos))
        (len (u56 len))

        ;; If at end of string, then stop
        ((if (mbe :logic (zp (- len pos))
                  :exec  (>= pos len)))
         len) ; Report at end of STR.

        (ch (char str pos))
        (byte (u08 (char-code ch)))
        (zero (= byte 0))
        (pos+1 (u56 (1+ pos)))
        ((if zero) pos+1))
     (pos-after-clrat-nums str len pos+1)))

(defthm natp-pos-after-clrat-nums
  (implies (and (natp len) (natp pos))
           (natp (pos-after-clrat-nums str len pos)))
  :rule-classes :type-prescription)

(defthm bound-pos-after-clrat-nums
  (implies (and (natp len) (natp pos) (<= pos len))
           (and (<= pos (pos-after-clrat-nums str len pos))
                (<= (pos-after-clrat-nums str len pos) len)))
  :rule-classes :linear)

(in-theory (disable pos-after-clrat-nums))


(with-arithmetic-help-5
 (defun clrat-nat (str len pos n shift)

; Read compressed natural number from string; return number read.

   (declare (xargs :guard (and (lrat-guard str len pos)
                               (natp n)
                               (< n *2^60*)
                               (natp shift)
                               (< shift 53))
                   :measure (nfix (- len pos))))
   ;; Expecting little-endian numbers
   (b* ((pos (u56 pos))
        (len (u56 len))
        (n   (u60 n))

        ;; Maximum clause number permitted
        ((unless (< n *2^52*)) 0)
        (n (u52 n))

        ;; End of string?  Terminate read
        ((if (mbe :logic (zp (- len pos))
                  :exec  (>= pos len))) n) ; At end of str

        (ch (char str pos))
        (byte (u08 (char-code ch)))

        (7-bit-num (u07 (logand byte 127)))
        ;; MATT, math issue
        (placed-7-bit-num (u60 (n60 (ash 7-bit-num shift))))

        ;; End of natural number?
        (n (u60 (n60 (+ placed-7-bit-num n)))) ;; MATT, math issue
        (more (= (logand byte 128) 128))
        ((unless more) n)

        (pos+1 (u56 (1+ pos)))
        (next-shift (+ shift 7))

        ;; If number collect so far is too big, stop read
        ((if (not (< next-shift 53))) n))
     (clrat-nat str len pos+1 n (+ shift 7)))))

(defthm natp-clrat-nat
  (implies (natp n)
           (natp (clrat-nat str len pos n shift)))
  :rule-classes :type-prescription)

(defthm bound-clrat-nat
  (implies (and (natp n)
                (< n *2^60*)
                (< shift 53))
           (and (<= 0 (clrat-nat str len pos n shift))
                (< (clrat-nat str len pos n shift) *2^60*)))
  :rule-classes :linear)

(in-theory (disable clrat-nat))


(defun clrat-int (str len pos)

; Read compressed integer from STR starting at position POS.  Return
; integer read.

  (declare (xargs :guard (lrat-guard str len pos)))
  (b* ((pos (u56 pos))
       (len (u56 len))

       ;; If already at end, return 0.
       ((unless (< pos len)) 0)
       (ch (char str pos))
       (byte (u08 (char-code ch)))

       ((if (= byte 0)) 0)  ; MATT:  Check not needed; guard proof easier
       (sign (= (logand byte 1) 1))
       (more (= (logand byte 128) 128))
       (6-bit-num (u06 (logand (ash byte -1) 63)))

       ((unless (mbt (<= 6-bit-num 63))) 0) ; MATT:  Another guard issue
       ((unless more) (s07 (if sign (- 6-bit-num) 6-bit-num)))

       ;; Prematurely at end?
       (pos+1 (u56 (1+ pos)))
       ((unless (< pos+1 len)) 0)

       (all-of-nat (u60 (clrat-nat str len pos+1 6-bit-num 6))))
    (s61 (if sign (- all-of-nat) all-of-nat))))

(defthm integerp-clrat-int
  (integerp (clrat-int str len pos))
  :rule-classes :type-prescription)

(defthm bound-clrat-int
  (and (<= (- *2^60*) (clrat-int str len pos))
       (< (clrat-int str len pos) *2^60*))
  :rule-classes :linear)

(in-theory (disable clrat-int))


(defun clrat-zero (str len pos)

; Find next zero (starting at POS) in STR, where STR contains
; compressed list of numbers.  Return position of that next zero.

  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))
  (b* ((pos (u56 pos))
       (len (u56 len))

       ;; At End of STR?  If so, return position at end of STR.
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        len)

       (ch (char str pos))
       (byte (u08 (char-code ch)))
       (zero (= byte 0))
       ((if zero) pos)
       (pos+1 (u56 (1+ pos))))
    (clrat-zero str len pos+1)))

(defthm natp-clrat-zero
  (implies (and (natp len) (natp pos))
           (natp (clrat-zero str len pos)))
  :rule-classes :type-prescription)

(defthm bound-clrat-zero
  (implies (and (natp pos) (< pos len))
           (and (<= pos (clrat-zero str len pos))
                (<= (clrat-zero str len pos) len)))
  :rule-classes :linear)

(in-theory (disable clrat-zero))


(defun-inline clrat-zero+1 (str len pos)
  (declare (xargs :guard (lrat-guard str len pos)))
  (b* ((clrat-zero (clrat-zero str len pos))
       ((unless (< clrat-zero len)) len))
    (1+ clrat-zero)))

(defthm natp-clrat-zero+1
  (implies (and (natp len) (natp pos))
           (natp (clrat-zero+1 str len pos)))
  :rule-classes :type-prescription)

(defthm bound-clrat-zero+1
  (implies (and (natp pos) (natp len) (< pos len))
           (and (< pos (clrat-zero+1 str len pos))
                (<= (clrat-zero+1 str len pos) len)))
  :rule-classes :linear)

(in-theory (disable clrat-zero+1))


(defun clrat-int-end+1 (str len pos)

; Return the position in STR just after the end of a compressed integer.

  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))
  (b* ((pos (u56 pos))
       (len (u56 len))

       ;; At end of STR?  If so, return end position
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        len) ; At end of str

       (ch (char str pos))
       (byte (u08 (char-code ch)))
       (more (<= 128 byte))
       (pos+1 (u56 (1+ pos)))

       ;; If POS points to last byte of compressed number, quit
       ((if (not more)) pos+1))
    (clrat-int-end+1 str len pos+1)))

(defthm natp-clrat-int-end+1
  (implies (and (natp len) (natp pos))
           (natp (clrat-int-end+1 str len pos)))
  :rule-classes :type-prescription)

(defthm bound-clrat-int-end+1
  (implies (< pos len)
           (and (< pos (clrat-int-end+1 str len pos))
                (<= (clrat-int-end+1 str len pos) len)))
  :rule-classes :linear)

(in-theory (disable clrat-int-end+1))


(with-arithmetic-help-5
 (defun clrat-ints (str len pos ints)

; Read list of compressed integers from STR, until a 0 is discovered

   (declare (xargs :guard (lrat-guard str len pos)
                   :measure (nfix (- len pos))))
   (b* ((pos (u56 pos))
        (len (u56 len))

        ;; If at end of string, quit
        ((if (mbe :logic (zp (- len pos))
                  :exec  (>= pos len)))
         nil)

        (ch (char str pos))
        (byte (u08 (char-code ch)))

        ;; If zero discovered, return list of integers
        ((if (= byte 0)) (my-rev ints))

        (int (s61 (clrat-int str len pos)))
        (pos-nx-int (clrat-int-end+1 str len pos))

        ;; MATT -- A strange requirement
        ((unless (mbt (< pos pos-nx-int))) nil))

     (clrat-ints str len pos-nx-int (cons int ints)))))

(defthm integer-listp-clrat-ints
  (implies (integer-listp ints)
           (integer-listp (clrat-ints str len pos ints))))

(in-theory (disable clrat-ints))


(defun cut-at-first-negative-integer (lst)

; Collect natural numbers from integer list until first negative
; number encountered.

  (declare (xargs :guard (integer-listp lst)))
  (if (atom lst)
      nil
    (let ((int (car lst)))
      (if (< int 0)
          nil
        (cons int
              (cut-at-first-negative-integer (cdr lst)))))))

(defthm nat-listp-cut-at-first-negative-integer
  (implies (integer-listp lst)
           (nat-listp (cut-at-first-negative-integer lst))))

(in-theory (disable cut-at-first-negative-integer))


(defun delete-until-first-negative-integer (lst)

; Eliminate natural numbers in LST until first negative number; return
; remainder of LST (including negative number discovered).

  (declare (xargs :guard (integer-listp lst)))
  (if (atom lst)
      nil
    (let ((int (car lst)))
      (if (< int 0)
          lst
        (delete-until-first-negative-integer (cdr lst))))))

(defthm integer-listp-delete-until-first-negative-integer
  (implies (integer-listp x)
           (integer-listp (delete-until-first-negative-integer x))))

(defthm acl2-count-delete-until-first-negative-integer
  (<= (acl2-count (delete-until-first-negative-integer lst))
      (acl2-count lst))
  :rule-classes :linear)

(in-theory (disable delete-until-first-negative-integer))


(defun break-into-lists-at-negative-integers (lst rat-list)

; When "standing" at negative integer (in LST); negate first integer
; and collect up to next negative integer or to end of LST.  Finally,
; return result being collected in RAT-LIST.

  (declare (xargs :guard (and (integer-listp lst)
                              (list-of-integer-listp rat-list))))
  (declare (xargs :guard (integer-listp lst)))
  (if (atom lst)
      rat-list
    (b* ((rest-of-rat (cut-at-first-negative-integer (cdr lst)))
         (rat-clause (cons (- (car lst)) rest-of-rat))
         (rest-of-rats (delete-until-first-negative-integer (cdr lst))))
      (break-into-lists-at-negative-integers rest-of-rats (cons rat-clause rat-list)))))


(defun clrat-read-a-line (str len pos)

; Read addition command.  Returns (MV <new-pos> <command>) where
; <new-pos> is the position in the string after this <command>.

  (declare (xargs :guard (lrat-guard str len pos)))
  (b* ((pos (u56 pos))
       (len (u56 len))

       ;; Read until first zero
       (line-clause-ints (clrat-ints str len pos nil))
       (pos-after-first-zero (pos-after-clrat-nums str len pos))

       ;; If first zero isn't discovered before end of string
       ((unless (< pos-after-first-zero len)) (mv len nil))

       ;; Read until second zero
       (rup-rat-ints (clrat-ints str len pos-after-first-zero nil))
       (pos-after-second-zero (pos-after-clrat-nums str len pos-after-first-zero))

       ;; If second zero isn't discovered before end of string
       ((unless (<= pos-after-second-zero len)) (mv len nil))

       ;;If nothing read, then short-circuit end
       ((unless (consp line-clause-ints)) (mv len nil))

       ;; Cut second part of line
       (rup (cut-at-first-negative-integer rup-rat-ints))
       (rat-list (delete-until-first-negative-integer rup-rat-ints))

       ;; Reverse RAT clauses
       (rev-rat-lists (break-into-lists-at-negative-integers rat-list nil)))

    (mv pos-after-second-zero
        ;; Create return result
        (cons line-clause-ints
              (cons rup rev-rat-lists)))))

(defthm natp-car-clrat-read-a-line
  (implies (and (natp len) (natp pos))
           (natp (car (clrat-read-a-line str len pos))))
  :rule-classes :type-prescription)

(defthm bound-car-clrat-read-a-line
  (implies (and (natp len) (natp pos) (<= pos len))
           (and (<= pos (car (clrat-read-a-line str len pos)))
                (<= (car (clrat-read-a-line str len pos)) len)))
  :rule-classes :linear)

(in-theory (disable clrat-read-a-line))


(defun clrat-line-mv (str len pos)

; Read either an addition or a deletion line of a LRAT proof.  Returns
; (MV <new-pos> <command>) where <new-pos> is the position in the
; string after the addition/deletion <command>.

  (declare (xargs :guard (lrat-guard str len pos)))
  (b* ((pos (u56 pos))
       (len (u56 len))

       ;; Read character
       ((unless (< pos len)) (mv len nil))
       (ch (char str pos))

       ;; Bump read position
       (pos+1 (u56 (1+ pos)))
       ((unless (< pos+1 len)) (mv len nil)))

    (if (eql ch #\d) ; Deletion or Addition line

        ;; proof-step d <nat>* 0
        (b* ((dlst (clrat-ints str len pos+1 nil))
             (pos-after-dlst (u56 (clrat-zero+1 str len pos+1))))
          (mv pos-after-dlst (cons t dlst)))

      ;; proof-step a <nat>* 0 nat* {-int nat*}*
      (clrat-read-a-line str len pos+1))))

(defthm natp-car-clrat-line-mv
  (implies (and (natp len) (natp pos))
           (natp (car (clrat-line-mv str len pos))))
  :rule-classes :type-prescription)

(defthm bound-car-clrat-line-mv
  (implies (and (natp len) (natp pos) (<= pos len))
           (and (<= pos (car (clrat-line-mv str len pos)))
                (<= (car (clrat-line-mv str len pos)) len)))
  :rule-classes :linear)

(in-theory (disable clrat-line-mv))


(defun skip-clrat-command (str len pos)
  (declare (xargs :guard (lrat-guard str len pos)))
  (b* ((pos (u56 pos))
       (len (u56 len))

       ;; Read character
       ((unless (< pos len)) len)
       (ch (char str pos))

       ;; Bump read position
       (pos+1 (u56 (1+ pos)))
       ((unless (< pos+1 len)) len)

       ;; Position after first zero
       (pos-after-zero (clrat-zero+1 str len pos+1))
       ((unless (< pos-after-zero len)) len))

    (if (eql ch #\d) ; Deletion or Addition line
        pos-after-zero
      (clrat-zero+1 str len pos-after-zero))))

(defthm natp-skip-clrat-command
  (implies (and (natp pos) (natp len))
           (natp (skip-clrat-command str len pos)))
  :rule-classes :type-prescription)

(defthm bound-skip-clrat-command
  (implies (and (natp pos) (natp len) (<= pos len))
           (and (<= pos (skip-clrat-command str len pos))
                (<= (skip-clrat-command str len pos) len)))
  :rule-classes :linear)

(in-theory (disable skip-clrat-command))


(defun skip-clrat-commands (str len pos)
  (declare (xargs :guard (lrat-guard str len pos)
                   :measure (nfix (- len pos))))
   (b* ((pos (u56 pos))
        (len (u56 len))

        ;; If at end of string, quit
        ((if (mbe :logic (zp (- len pos))
                  :exec  (>= pos len)))
         len)

        (next-cmd-pos (skip-clrat-command str len pos))
        ((unless (< next-cmd-pos len)) pos)

        ;; If SKIP-CLRAT-COMMAND finishes at end -- not supposed to, then stop
        ((unless (< pos next-cmd-pos)) len))
    (skip-clrat-commands str len next-cmd-pos)))

(defthm natp-skip-clrat-commands
  (implies (and (natp pos) (natp len))
           (natp (skip-clrat-commands str len pos)))
  :rule-classes :type-prescription)

(defthm bound-skip-clrat-commands
  (implies (and (natp pos) (natp len) (<= pos len))
           (and (<= pos (skip-clrat-commands str len pos))
                (<= (skip-clrat-commands str len pos) len)))
  :rule-classes :linear)

(in-theory (disable skip-clrat-commands))



(defun clrat-read-some-lines
    (str       ; STRing to be read
     len       ; LENgth of STRing
     pos       ; POSition where processing STRing
     commands) ; Commands collected for processing

; Finally returns:
;    suffix    ; STRing remainder, if any; cut might be between commands
;  commands    ; Addition and Deletion commands

  (declare (xargs :guard (and (lrat-guard str len pos)
                              (true-listp commands))
                  :measure (nfix (- len pos))))
  (b* ((pos (u56 pos))
       (len (u56 len))

       ;; End of STRing?  If so, return what commands we have
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        (mv "" (my-rev commands)))

       ;; Insufficient characters for command?  Return STRing fragment
       ;; and commands.
       (ch (char str pos))
       (next-zero (clrat-zero str len pos))
       (insufficient (if (eql ch #\d)
                         (>= next-zero len)
                       (or (>= (1+ next-zero) len)
                           (>= (clrat-zero str len (1+ next-zero)) len))))
       ((if insufficient)
        (mv (subseq str pos len) (my-rev commands)))

       ;; Read a line, either an addition or deletion command
       ((mv new-pos command)
        (clrat-line-mv str len pos))

       ;; No progress?  Error!  Return what we have.
       (new-pos (u56 new-pos))
       ((unless (< pos new-pos)) (mv "" (my-rev commands))))

    (clrat-read-some-lines str len new-pos
                           (cons command commands))))

(defthm true-listp-clrat-read-some-lines
  (implies (true-listp commands)
           (true-listp (mv-nth 1 (clrat-read-some-lines str len pos commands)))))

(in-theory (disable clrat-read-some-lines))


(defun matts-incremental-proof-command-checker (commands)
  (declare (xargs :guard (true-listp commands)))
  (if (atom commands)
      T
    (and t ; (proof-command-ok (car commands))
         (matts-incremental-proof-command-checker (cdr commands)))))

(in-theory (disable matts-incremental-proof-command-checker))


(defmacro clrat-read-next-er (str &rest args)
  `(mv (er hard? 'clrat-read-next
           ,str
           ,@args)
       ""
       position))

(defun clrat-read-next-1 (filename    ; Filename
                          position    ; Position in file
                          read-amount ; Amount to read from file
                          suffix      ; Left over from previous chunck
                          file-length ; Length of filename contents
                          state)

; First read the contents of filename starting from position,
; returning a string of length read-amount (or less if end-of-file is
; reached).  Return (mv proof suffix), where proof is a list of
; add-step records parsed from that string and suffix is the final
; portion of that string that is unused in that parse.  However, in
; the case of error return (mv nil nil) instead.

  (declare (xargs :guard (and (stringp filename)
                              (natp position)
                              (< position *2^56*)
                              (posp read-amount)
                              (stringp suffix)
                              (natp file-length))
                  :stobjs (state)
                  :guard-hints
                  (("Goal" :in-theory (disable acl2::read-file-into-string2)))))
  (b* (((unless (mbt (and (stringp filename)
                          (natp position)
                          (< position *2^56*)
                          (posp read-amount)
                          (stringp suffix)
                          (natp file-length))))
        ;; Guard finesse
        (clrat-read-next-er "Illegal arguments.~%"))

       (input-chars (read-file-into-string
                     filename
                     :start position
                     :bytes read-amount))

       ((unless input-chars) ; !! Don't we know it's a string?
        (clrat-read-next-er "Input file problem.~%"))

       ((unless (stringp input-chars)) ; !! Don't we know it's a string?
        (clrat-read-next-er "Input from file not a string.~%"))

       (new-position (+ position read-amount))
       (final
        (and (= new-position file-length)

             ;; Then close the stream:

             (read-file-into-string
              filename
              :start file-length
              :bytes 1)))

       ((if (and final (not (equal final ""))))
        (clrat-read-next-er "Implementation error: expected final read to ~
                             yield \"\".~%"))

       (str (if (equal suffix "") ; optimization
                input-chars
              (string-append suffix input-chars)))
       (len (length str))

       ((unless (< len *2^56*)) ; !! presumably we know len <= read-amount
        (clrat-read-next-er "String too long to process."))

       ;; If both SUFFIX and INPUT-CHARS empty, then finished:

       ((if (= len 0))
        (mv nil "" position))
       ((mv suffix commands)
        (clrat-read-some-lines str len 0 nil))

       ((unless (stringp suffix))
        (clrat-read-next-er "Bad suffix returned from CLRAT-READ-SOME-LINES"))
       ((unless (< (+ position read-amount) *2^56*))
        (clrat-read-next-er "Proof file too big")))

    (mv commands suffix new-position)))


(defun clrat-read-next (filename    ; Filename
                        position    ; Position in file
                        read-amount ; Amount to read from file
                        suffix      ; Left over from previous chunck
                        file-length ; Length of filename contents
                        state)
  (declare (xargs :guard (and (stringp filename)
                              (natp position)
                              (< position *2^56*)
                              (posp read-amount)
                              (stringp suffix)
                              (natp file-length))
                  :measure (nfix (- file-length position))
                  :hints ; not necessary but greatly reduces processing time
                  (("Goal" :in-theory (disable acl2::read-file-into-string2)))
                  :guard-hints ; also unnecessary, but also greatly reduces time
                  (("Goal" :in-theory
                    (disable open-input-channel
                             open-input-channels
                             acl2::read-file-into-string2)))
                  :stobjs (state)))
  (mv-let (proof new-suffix new-posn)
    (clrat-read-next-1 filename position read-amount suffix file-length state)
    (cond
     ((or proof
          (equal new-suffix "")
          (not (mbt (natp file-length))))
      (mv proof new-suffix new-posn))
     (t (cond
         ((>= new-posn *2^56*) ; extremely unlikely
          (mv proof new-suffix new-posn))
         ((>= new-posn file-length) ; Don't recur; we need to terminate!
          (clrat-read-next-1 filename new-posn read-amount new-suffix file-length
                             state))
         (t
          (clrat-read-next filename new-posn read-amount new-suffix file-length
                           state)))))))

; The rest of this file defines function CLRAT-READ-FILE, which can be
; used to read the entire file into an alleged proof before it is checked.

(defun clrat-read-all-lines-rev (str len pos lines state)

; Read each "line" in a CLRAT-style file.  Returns a reversed list of
; addition and deletion commands.

  (declare (xargs :guard (lrat-guard str len pos)
                  :guard-hints
                  (("Goal" :in-theory (disable length)))
                  :stobjs (state)
                  :measure (nfix (- len pos))))
  (b* ((pos (u56 pos))
       (len (u56 len))

       ;; End of file?  If so, return collected lines
       ((if (mbe :logic (zp (- len pos))
                 :exec  (>= pos len)))
        (mv lines state))

       ;; Read a line, either an addition or deletion instruction
       ((mv new-pos line)
        (clrat-line-mv str len pos))

       ;; Progress?  If not, return what we have
       (new-pos (u56 new-pos))
       ((unless (< pos new-pos))
        (mv lines state)))

    (clrat-read-all-lines-rev str len new-pos (cons line lines) state)))


(defun clrat-read-all-lines (str len pos state)

; Just reverses the lines...

  (declare (xargs :guard (lrat-guard str len pos)
                  :stobjs (state)))
  (b* (((mv lines-rev state)
        (clrat-read-all-lines-rev str len pos nil state)))
    (mv (my-rev lines-rev) state)))


(defun clrat-read-file (file-name state)

; Reads a Compressed-LRAT file nameed FILE-NAME.  Returns a formula
; data structure, i.e., a list of (index . clause) pairs.  See
; formula-p in list-based/lrat-checker.lisp.  Note that the formula is
; _not_ a fast-alist.

  (declare (xargs :guard (stringp file-name)
                  :guard-hints
                  (("Goal" :in-theory (disable acl2::read-file-into-string2)))
                  :stobjs (state)))
  (b* ((str (read-file-into-string file-name))
       ((unless (stringp str))
        (mv (er hard? 'clrat-read-file
                    "clrat-read-file: (read-file-into-string ~x0 .~%" file-name)
            state))
       (len (length str))
       ((unless (< len *2^56*))
        (mv (er hard? 'clrat-read-file
                "clrat-read-file:  file ~x0 is too long.~%" file-name)
            state))
       (start 0)
       ((unless (lrat-guard str len start))
        (mv (er hard? 'clrat-read-file
                "clrat-read-file:  LRAT-GUARD fails.~%")
            state))
       (pos start))
    (clrat-read-all-lines str len pos state)))



; For debugging:

(defrec add-step
  ((index . clause)
   .
   (rup-indices . drat-hints))
  t)

(defun show-proof (proof acc)
  (cond ((endp proof) (reverse acc))
        (t (show-proof
            (cdr proof)
            (let ((step (if (eq (caar proof) t)
                            (list :delete (cdar proof))
                          (let* ((x (car proof))
                                 (index (access add-step x :index))
                                 (clause (access add-step x :clause))
                                 (rup-indices (access add-step x :rup-indices))
                                 (drat-hints (access add-step x :drat-hints)))
                            (list :index index
                                  :clause clause
                                  :rup-indices rup-indices
                                  :drat-hints drat-hints)))))
              (cons step acc))))))


; No need to reason about these printing and debugging functions...

(program)
(set-state-ok t)

(defun print-integers (lst end chan state)

; Lst is a list of integers.  Print each element of the list to the given
; channel, followig each with a space.  If end is not nil, then print it with
; princ$ too.

  (cond ((endp lst)
         (if end
             (princ$ end chan state)
           state))
        (t (pprogn (princ$ (car lst) chan state)
                   (princ$ #\Space chan state)
                   (print-integers (cdr lst) end chan state)))))

(defun print-drat-hints (drat-hints chan state)
  (cond ((endp drat-hints) state)
        (t (pprogn (princ$ (- (caar drat-hints)) chan state)
                   (princ$ #\Space chan state)
                   (print-integers (cdar drat-hints) nil chan state)
                   (print-drat-hints (cdr drat-hints) chan state)))))


(defun clrat-to-lrat-add-step (add-step chan state)

; Finally, we produce a converter from clrat to lrat, which can be useful for
; viewing clrat files.  For this first cut we read the entire file, but it
; should be easy to deal with chunks if need be.

;  j l1 l2 ... lk 0 d1 d2 ... dm -e1 f11 ... f1{m_1} -e2 f21 ... f2{m_2} ... 0

  (let ((index (access add-step add-step :index))
        (clause (access add-step add-step :clause))
        (rup-indices (access add-step add-step :rup-indices))
        (drat-hints (access add-step add-step :drat-hints)))
    (pprogn (princ$ index chan state)
            (princ$ #\Space chan state)
            (print-integers clause 0 chan state)
            (princ$ #\Space chan state)
            (print-integers rup-indices nil chan state)
            (print-drat-hints (reverse drat-hints) chan state)
            (princ$ 0 chan state)
            (newline chan state))))

(defun clrat-to-lrat-rec (lines last-index chan state)
  (cond ((endp lines) state)
        (t (pprogn (if (eq (caar lines) t) ; deletion
                       (pprogn (princ$ last-index chan state)
                               (princ$ #\Space chan state)
                               (princ$ #\d chan state)
                               (princ$ #\Space chan state)
                               (print-integers (cdar lines) 0 chan state)
                               (newline chan state))
                     (clrat-to-lrat-add-step (car lines) chan state))
                   (clrat-to-lrat-rec (cdr lines)
                                      (access add-step (car lines) :index)
                                      chan
                                      state)))))

(defun clrat-to-lrat (clrat-in-file lrat-out-file state)

; Clrat-in-file is a .clrat input file.  We print out a corresponding .lrat
; file, either to lrat-out-file if that is a string, else to (standard-co
; state).

  (mv-let (lines state)
    (clrat-read-file clrat-in-file state) ; returns a proofp
    (let ((last-index (or (and (consp lines)
                               (eq (car (car lines)) t) ; deletion
                               (consp (cdr lines))
                               (not (eq (car (cadr lines)) t))
                               (1- (access add-step (cadr lines) :index)))
                          0)))
      (pprogn
       (cond ((not (stringp lrat-out-file))
              (clrat-to-lrat-rec lines last-index (standard-co state) state))
             (t (mv-let
                  (chan state)
                  (open-output-channel lrat-out-file :character state)
                  (pprogn (clrat-to-lrat-rec lines last-index chan state)
                          (close-output-channel chan state)))))
       (value :invisible)))))
