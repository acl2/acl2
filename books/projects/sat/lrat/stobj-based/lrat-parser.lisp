; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file was originally created by Nathan Wetzler, but now is being
; modified by Warren Hunt and Matt Kaufmannn so as to produce a faster,
; lrat proof checker.

; We read two files: a formula file and a proof file.  A proof step in the
; proof file is either a deletion step

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

(in-package "LRAT")

(include-book "std/util/bstar" :dir :system)
(include-book "limits")
(include-book "lrat-checker")
; (include-book "misc/disassemble" :dir :system)

; (ld "lrat-parser-char-by-char.lisp" :ld-pre-eval-print t)


; Some miscellaneous definitions.

(defmacro ! (x y)
  (declare (xargs :guard (symbolp x)))
  `(assign ,x ,y))

(defmacro !! (variable new-value)
  ;; Assign without printing the result.
  (declare (xargs :guard t))
  `(mv-let
    (erp result state)
    (assign ,variable ,new-value)
    (declare (ignore result))
    (value (if erp 'Error! ',variable))))

(set-state-ok t)


; Some helper events...

(defun firstn (n x)
  (declare (xargs :guard (natp n)))
  (if (atom x)
      nil
    (if (mbe :logic (zp n) :exec (<= n 0))
        nil
      (cons (car x)
            (firstn (1- n) (cdr x))))))

(defthm integer-listp-firstn
  (implies (integer-listp l)
           (integer-listp (firstn n l))))

(defthm integer-listp-nth-cdr
  (implies (integer-listp l)
           (integer-listp (nthcdr s l))))


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

(in-theory (disable my-rev))


(defun-inline char-to-nat (ch)
  (declare (xargs :guard (characterp ch)))

; Returns the integer from 0 to 9 if one corresponds to ch, else nil.

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

(defun lrat-guard (str len pos)
  (declare (xargs :guard t))
  (and (stringp str)
       (natp pos)
       (natp len)
       (equal len (length str))
       (< pos len)
       ;;     *2^56*
       (< len 72057594037927936)))

(defun lrat-flg-nat1 (str len pos n) ; Returns (mv pos-or-nil nat)
  (declare (xargs :guard (and (lrat-guard str len pos)
                              (natp n)
                              (< n *2^56*))
                  :measure (nfix (- len pos))))
  (let* ((len (u56 len))
         (pos (u56 pos))
         (n   (u56 n))
         (ch  (char str pos))
         (digit (char-to-nat ch)))
    (if (null digit)
        (mv pos n)
      (let ((pos+1 (u59 (1+ pos))))
        (if (mbe :logic (zp (- len pos+1))
                 :exec  (>= pos+1 len))
            (mv nil 0)
          (if (not (< n 4503599627370496)) ; *2^52*
              (mv nil 0)
            (let* ((10n+digit (u56 (+ (u04 digit) (u56 (* n 10))))))
              (lrat-flg-nat1 str len pos+1 10n+digit))))))))

(defthm integerp-lrat-flg-nat1
  (implies (and (natp pos)
                (car (lrat-flg-nat1 str len pos n)))
           (integerp (car (lrat-flg-nat1 str len pos n))))
  :hints
  (("Goal"
    :in-theory (disable length)
    :induct (lrat-flg-nat1 str len pos n))))

(defthm natp-lrat-flg-nat1
  (implies (and (natp pos)
                (car (lrat-flg-nat1 str len pos n)))
           (<= 0 (car (lrat-flg-nat1 str len pos n))))
  :hints
  (("Goal"
    :in-theory (disable length)
    :induct (lrat-flg-nat1 str len pos n)))
  :rule-classes :linear)

(defthm pos-has-increased-lrat-flg-nat1
  (implies (and (char-to-nat (char str pos))
                (car (lrat-flg-nat1 str len pos n)))
           (< pos (car (lrat-flg-nat1 str len pos n)))))

(defthm pos-has-increased-lrat-flg-nat1-1
  (implies (and (char-to-nat (char str pos1))
                (natp pos)
                (<= pos pos1)
                (car (lrat-flg-nat1 str len pos1 n)))
           (< pos (car (lrat-flg-nat1 str len pos1 n)))))

(defthm car-lrat-flag-nat1-less-than-len
  (implies (and (lrat-guard str len pos)
                 (car (lrat-flg-nat1 str len pos n)))
           (< (car (lrat-flg-nat1 str len pos n)) len))
  :hints
  (("Goal"
    :in-theory (disable length)
    :induct (lrat-flg-nat1 str len pos n))))

(encapsulate
  ()
  (local
   (defthm mv-nth-1-natp-lrat-flg-nat1
     (implies (and (natp n)
                   (car (lrat-flg-nat1 str len pos n)))
              (natp (mv-nth 1 (lrat-flg-nat1 str len pos n))))))

  (defthm integerp-mv-nth-1-natp-lrat-flg-nat1
    (implies (and (natp n)
                  (car (lrat-flg-nat1 str len pos n)))
             (integerp (mv-nth 1 (lrat-flg-nat1 str len pos n)))))

  (defthm ge-0-mv-nth-1-natp-lrat-flg-nat1
    (implies (and (natp n)
                  (car (lrat-flg-nat1 str len pos n)))
             (<= 0 (mv-nth 1 (lrat-flg-nat1 str len pos n))))))

(defthm mv-nth1-lrat-flg-nat1-less-than-*2^56*
  (implies (and (natp n)
                (< n *2^56*)
                (car (lrat-flg-nat1 str len pos n)))
           (< (mv-nth 1 (lrat-flg-nat1 str len pos n)) *2^56*))
  :hints
  (("Goal"
    :in-theory (disable length)
    :induct (lrat-flg-nat1 str len pos n))))

(in-theory (disable lrat-flg-nat1))


(defun lrat-flg-nat (str len pos) ; Returns (mv pos-or-nil nat)
  (declare (xargs :guard (lrat-guard str len pos)))

; Requires that at least one decimal digit is found; reads until non nat digit.
; Returns (mv POS N), POS points just after NAT, N is the natural number read.

  (b* ((ch (char str pos))
       ((unless (char-to-nat ch)) (mv nil 0)))
    (lrat-flg-nat1 str len pos 0)))

(defthm integerp-lrat-flg-nat
  (implies (and (natp pos)
                (car (lrat-flg-nat str len pos)))
           (integerp (car (lrat-flg-nat str len pos))))
  :hints
  (("Goal"
    :in-theory (disable length))))

(defthm natp-lrat-flg-nat
  (implies (and (natp pos)
                (car (lrat-flg-nat str len pos)))
           (<= 0 (car (lrat-flg-nat str len pos))))
  :hints
  (("Goal"
    :in-theory (disable length)))
  :rule-classes :linear)

(defthm pos-has-increased-lrat-flg-nat
  (implies (car (lrat-flg-nat str len pos))
           (< pos (car (lrat-flg-nat str len pos)))))

(defthm pos-has-increased-lrat-flg-nat-1
  (implies (and (natp pos)
                (<= pos pos1)
                (car (lrat-flg-nat str len pos1)))
           (< pos (car (lrat-flg-nat str len pos1)))))

(defthm car-lrat-flag-nat-less-than-len
  (implies (and (lrat-guard str len pos)
                (car (lrat-flg-nat str len pos)))
           (< (car (lrat-flg-nat str len pos)) len)))

(encapsulate
  ()
  (local
   (defthm mv-nth-1-natp-lrat-flg-nat
     (implies (car (lrat-flg-nat str len pos))
              (natp (mv-nth 1 (lrat-flg-nat str len pos))))))

  (defthm integerp-mv-nth-1-lrat-flg-nat
    (implies (car (lrat-flg-nat str len pos))
             (integerp (mv-nth 1 (lrat-flg-nat str len pos))))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (disable mv-nth lrat-flg-nat)
             :use ((:instance mv-nth-1-natp-lrat-flg-nat
                              (str str) (len len) (pos pos))))))

  (defthm ge-0-mv-nth-1-lrat-flg-nat
    (implies (car (lrat-flg-nat str len pos))
             (<= 0 (mv-nth 1 (lrat-flg-nat str len pos))))
    :rule-classes :linear
    :hints (("Goal" :in-theory (disable mv-nth lrat-flg-nat)
             :use ((:instance mv-nth-1-natp-lrat-flg-nat
                              (str str) (len len) (pos pos)))))))

(defthm mv-nth1-lrat-flg-nat-less-than-*2^56*
  (implies (car (lrat-flg-nat str len pos))
           (< (mv-nth 1 (lrat-flg-nat str len pos))
              *2^56*)))

(in-theory (disable lrat-flg-nat))


(defun lrat-flg-int (str len pos) ; Returns (mv pos-or-nil int)
  (declare (xargs :guard (lrat-guard str len pos)))
  (b* ((ch (char str pos)))
    (if (eql ch #\-)
        (b* ((pos   (u56     pos))
             (len   (u56     len))
             (pos+1 (u59 (1+ pos)))
             ((unless (< pos+1 len)) (mv nil 0))
             ((mv pos-after-nat num) (lrat-flg-nat str len pos+1))
             ((unless pos-after-nat) (mv nil 0))
             ;; ((unless (< pos pos-after-nat)) (mv nil 0))
             (num (u56 num))
             )
          (mv pos-after-nat (- num)))
      (lrat-flg-nat str len pos))))

(defthm integerp-lrat-flg-int
  (implies (and (natp pos)
                (car (lrat-flg-nat str len pos)))
           (integerp (car (lrat-flg-nat str len pos))))
  :hints
  (("Goal"
    :in-theory (disable length))))

(defthm natp-lrat-flg-int
  (implies (and (natp pos)
                (car (lrat-flg-int str len pos)))
           (<= 0 (car (lrat-flg-int str len pos))))
  :hints
  (("Goal"
    :in-theory (disable length)))
  :rule-classes :linear)

(defthm pos-has-increased-lrat-flg-int-1
  (implies (and (natp pos)
                (<= pos pos1)
                (car (lrat-flg-int str len pos1)))
           (< pos (car (lrat-flg-int str len pos1)))))

(defthm car-lrat-flag-int-less-than-len
  (implies (and (lrat-guard str len pos)
                (or (car (lrat-flg-int str len pos))
                    (integerp (lrat-flg-int str len pos))))
           (< (car (lrat-flg-int str len pos)) len)))

(defthm mv-nth-1-natp-lrat-flg-int
  (implies (car (lrat-flg-int str len pos))
           (integerp (mv-nth 1 (lrat-flg-int str len pos))))
  :rule-classes (:rewrite :type-prescription))

(encapsulate
  ()
  (local
   (defthm ONE-TIME-MATH-FACT
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

  (defthm mv-nth1-lrat-flg-int-abs-less-than-*2^56*
    (implies (car (lrat-flg-int str len pos))
             (and (< (- *2^56*) (mv-nth 1 (lrat-flg-int str len pos)))
                  (< (mv-nth 1 (lrat-flg-int str len pos)) *2^56*)))
    :hints
    (("Goal" :do-not-induct t))))

(in-theory (disable lrat-flg-int))


(defun lrat-flg-pos-skip-spaces (str len pos) ; Returns pos
  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))

; Skip space characters, leave POS at first non-space character

  (b* ((ch (char str pos))
       ((when (not (eql ch #\Space))) pos)
       (len (u56 len))
       (pos (u56 pos))
       (pos+1 (u56 (1+ pos))))
    (if (mbe :logic (zp (- len pos+1))
             :exec  (>= pos+1 len))
        pos
      (lrat-flg-pos-skip-spaces str len pos+1))))

(encapsulate
  ()
  (local
   (defthm natp-lrat-flg-pos-skip-spaces
     (implies (natp pos)
              (natp (lrat-flg-pos-skip-spaces str len pos)))))

  (defthm integerp-lrat-flg-pos-skip-spaces
    (implies (integerp pos) ; (natp pos)
             (integerp (lrat-flg-pos-skip-spaces str len pos)))
    :rule-classes :type-prescription)

  (defthm ge-0-lrat-flg-pos-skip-spaces
    (implies (natp pos)
             (<= 0 (lrat-flg-pos-skip-spaces str len pos)))
    :rule-classes (:rewrite :linear)))

(defthm pos-fact-lrat-flg-pos-skip-spaces
  (<= pos (lrat-flg-pos-skip-spaces str len pos))
  :rule-classes (:rewrite :linear))

(defthm lrat-flg-pos-skip-spaces-<-length-str
  (implies (lrat-guard str len pos)
           (< (lrat-flg-pos-skip-spaces str len pos)
              len))
  :hints
  (("Goal"
    :in-theory (enable nth)
    :induct (lrat-flg-pos-skip-spaces len pos n))))

(defthm lrat-flg-pos-skip-spaces-<-*2^56*
  (implies (and (equal limit *2^56*)
                (lrat-guard str len pos))
           (< (lrat-flg-pos-skip-spaces str len pos) limit))
  :hints
  (("Goal"
    :in-theory (enable nth)
    :induct (lrat-flg-pos-skip-spaces len pos n))))

(in-theory (disable lrat-flg-pos-skip-spaces))


; NAT reader

(defun lrat-flg-nat-list-until-0 (str len pos lst cnt) ; Returns (mv pos-or-nil nat-list)
  (declare (xargs :guard (and (lrat-guard str len pos)
                              (true-listp lst)
                              (natp cnt)
                              (<= cnt len))
                  :guard-hints
                  (("Goal"
                    :in-theory (disable length car-lrat-flag-nat-less-than-len)
                    :use
                    ((:instance car-lrat-flag-nat-less-than-len
                                (str str)
                                (len (length str))
                                (pos (lrat-flg-pos-skip-spaces str (length str) pos)))
                                     )))
                  :measure (acl2-count cnt)))

; Read list of nats until "0" found; return list

  (b* ((pos (u59 pos))
       (pos-after-spaces (lrat-flg-pos-skip-spaces str len pos))
       ((unless (integerp pos-after-spaces)) (mv nil nil))
       (pos-after-spaces (u56 pos-after-spaces))

       ((mv pos-after-nat nat-read) (lrat-flg-nat str len pos-after-spaces))
       ((unless (integerp pos-after-nat)) (mv nil nil))

       (pos-after-nat (u59 pos-after-nat))
       (nat-read (u56 nat-read))

       ((if (= nat-read 0)) (mv pos-after-nat (my-rev lst)))

       ((unless (< pos pos-after-nat)) (mv nil nil))
       (len (u59 len))
       (cnt (u59 cnt))
       (cnt-1 (1- cnt)))

    (if (mbe :logic (zp cnt) :exec (<= cnt 0))
        (mv nil nil) ; Use information about POS-AFTER-NAT to remove CNT.
      (lrat-flg-nat-list-until-0
       str len pos-after-nat (cons nat-read lst) cnt-1))))


(defthm integerp-lrat-flg-nat-list-until-0
  (implies (and (natp pos)
                (car (lrat-flg-nat-list-until-0 str len pos lst cnt)))
           (integerp (car (lrat-flg-nat-list-until-0 str len pos lst cnt))))
  :hints
  (("Goal"
    :in-theory (disable length))))

(defthm natp-lrat-flg-nat-list-until-0
  (implies (and (natp pos)
                (car (lrat-flg-nat-list-until-0 str len pos lst cnt)))
           (<= 0 (car (lrat-flg-nat-list-until-0 str len pos lst cnt))))
  :hints
  (("Goal"
    :in-theory (disable length)))
  :rule-classes :linear)

(defthm pos-has-increased-lrat-flg-nat-list-until-0
  (implies (and (natp pos)
                (<= pos pos1)
                (car (lrat-flg-nat-list-until-0 str len pos1 lst cnt)))
           (< pos (car (lrat-flg-nat-list-until-0 str len pos1 lst cnt)))))

#||
(defthm car-lrat-flag-nat-list-until-0-less-than-len
  ;; May need to augment the definition
  (implies (and (lrat-guard str len pos)
                (car (lrat-flg-nat-list-until-0 str len pos lst cnt)))
           (< (car (lrat-flg-nat-list-until-0 str len pos lst cnt)) len)))
||#

(defthm nat-listp-lrat-flg-nat-list-until-0
  (implies (nat-listp lst)
           (nat-listp (mv-nth 1 (lrat-flg-nat-list-until-0 str len pos lst cnt)))))

(in-theory (disable lrat-flg-nat-list-until-0))


; INTEGER reader

(defun lrat-flg-int-list-until-0 (str len pos lst cnt) ; Returns (mv pos-or-nil int-list)
  (declare (xargs :guard (and (lrat-guard str len pos)
                              (true-listp lst)
                              (natp cnt)
                              (<= cnt len))
                  :guard-hints
                  (("Goal"
                    :in-theory (disable length car-lrat-flag-int-less-than-len)
                    :use
                    ((:instance car-lrat-flag-int-less-than-len
                                (str str)
                                (len (length str))
                                (pos (lrat-flg-pos-skip-spaces str (length str) pos)))
                     (:instance mv-nth1-lrat-flg-int-abs-less-than-*2^56*
                                (str str)
                                (len (length str))
                                (pos (lrat-flg-pos-skip-spaces str (length str) pos))))))
                  :measure (acl2-count cnt)))

; Read list of ints until "0" found; return list

  (b* ((pos (u59 pos))
       (pos-after-spaces (lrat-flg-pos-skip-spaces str len pos))
       ((unless (integerp pos-after-spaces)) (mv nil nil))
       (pos-after-spaces (u56 pos-after-spaces))

       ((mv pos-after-int int-read) (lrat-flg-int str len pos-after-spaces))
       ((unless (integerp pos-after-int)) (mv nil nil))

       (pos-after-int (u59 pos-after-int))
       (int-read (s57 int-read))

       ((if (= int-read 0)) (mv pos-after-int (my-rev lst)))

       (len (u59 len))
       (cnt (u59 cnt))
       (cnt-1 (1- cnt)))

    (if (mbe :logic (zp cnt) :exec (<= cnt 0))
        (mv nil nil) ; Use information about POS-AFTER-INT to remove CNT.
      (lrat-flg-int-list-until-0
       str len pos-after-int (cons int-read lst) cnt-1))))

(defthm integerp-lrat-flg-int-list-until-0
  (implies (and (natp pos)
                (car (lrat-flg-int-list-until-0 str len pos lst cnt)))
           (integerp (car (lrat-flg-int-list-until-0 str len pos lst cnt))))
  :hints
  (("Goal"
    :in-theory (disable length))))

(defthm natp-lrat-flg-int-list-until-0
  (implies (and (natp pos)
                (car (lrat-flg-int-list-until-0 str len pos lst cnt)))
           (<= 0 (car (lrat-flg-int-list-until-0 str len pos lst cnt))))
  :hints
  (("Goal"
    :in-theory (disable length)))
  :rule-classes :linear)

#||
(defthm pos-has-increased-lrat-flg-int-list-until-0
  (implies (and (natp pos)
                (<= pos pos1)
                (car (lrat-flg-int-list-until-0 str len pos1 lst cnt)))
           (< pos (car (lrat-flg-int-list-until-0 str len pos1 lst cnt)))))

(defaxiom car-lrat-flag-int-list-until-0-less-than-len
  ;; May need to augment the definition
  (implies (and (lrat-guard str len pos)
                (car (lrat-flg-int-list-until-0 str len pos lst cnt)))
           (< (car (lrat-flg-int-list-until-0 str len pos lst cnt)) len)))
||#

(defthm int-listp-lrat-flg-int-list-until-0
  (implies (integer-listp lst)
           (integer-listp (mv-nth 1 (lrat-flg-int-list-until-0 str len pos lst cnt)))))


; INTEGER list reader until 0 or "-" reader

(defun lrat-flg-int-list-until-0-or-- (str len pos lst cnt) ; Returns (mv pos-or-nil int-list)
  (declare (xargs :guard (and (lrat-guard str len pos)
                              (true-listp lst)
                              (natp cnt)
                              (<= cnt len))
                  :guard-hints
                  (("Goal"
                    :in-theory (disable length car-lrat-flag-int-less-than-len)
                    :use
                    ((:instance car-lrat-flag-int-less-than-len
                                (str str)
                                (len (length str))
                                (pos (lrat-flg-pos-skip-spaces str (length str) pos)))
                     (:instance mv-nth1-lrat-flg-int-abs-less-than-*2^56*
                                (str str)
                                (len (length str))
                                (pos (lrat-flg-pos-skip-spaces str (length str) pos))))))
                  :measure (acl2-count cnt)))

; Read list of ints until "-" or "0" found; return list

  (b* ((pos (u59 pos))
       (pos-after-spaces (lrat-flg-pos-skip-spaces str len pos))
       ((unless (integerp pos-after-spaces)) (mv nil nil))
       (pos-after-spaces (u56 pos-after-spaces))

       ;; Exit if "-" character discovered, leave POS just after "-" character
       (ch (char str pos-after-spaces))

       ((if (eql #\- ch))
        (b* ((pos-after-spaces+1 (1+ (u56 pos-after-spaces))))
             (if (not (and (< pos pos-after-spaces+1)
                           (< pos-after-spaces+1 len)))
                 (mv pos nil)
               (mv pos-after-spaces+1 (my-rev lst)))))

       ((mv pos-after-int int-read) (lrat-flg-int str len pos-after-spaces))
       ((unless (integerp pos-after-int)) (mv nil nil))

       (len (u59 len))
       ((unless (< pos-after-int len)) (mv nil nil))

       (pos-after-int (u59 pos-after-int))
       (int-read (s57 int-read))

       ;; Exit when 0 read
       ((if (= int-read 0)) (mv pos-after-int (my-rev lst)))

       (cnt (u59 cnt))
       (cnt-1 (1- cnt)))

    (if (mbe :logic (zp cnt) :exec (<= cnt 0))
        (mv nil nil) ; Use information about POS-AFTER-INT to remove CNT.
      (lrat-flg-int-list-until-0-or--
       str len pos-after-int (cons int-read lst) cnt-1))))


(defthm integerp-lrat-flg-int-list-until-0-or--
  (implies (and (natp pos)
                (car (lrat-flg-int-list-until-0-or-- str len pos lst cnt)))
           (integerp (car (lrat-flg-int-list-until-0-or-- str len pos lst cnt))))
  :hints
  (("Goal"
    :in-theory (disable length))))

(defthm natp-lrat-flg-int-list-until-0-or--
  (implies (and (natp pos)
                (car (lrat-flg-int-list-until-0-or-- str len pos lst cnt)))
           (<= 0 (car (lrat-flg-int-list-until-0-or-- str len pos lst cnt))))
  :hints
  (("Goal"
    :in-theory (disable length)))
  :rule-classes :linear)

#||
(defthm pos-has-increased-lrat-flg-int-list-until-0-or--
  (implies (and (natp pos)
                (<= pos pos1)
                (car (lrat-flg-int-list-until-0-or-- str len pos1 lst cnt)))
           (< pos (car (lrat-flg-int-list-until-0-or-- str len pos1 lst cnt)))))

||#

(defthm car-lrat-flag-int-list-until-0-or---less-than-len
  (implies (and (lrat-guard str len pos)
                (car (lrat-flg-int-list-until-0-or-- str len pos lst cnt)))
           (< (car (lrat-flg-int-list-until-0-or-- str len pos lst cnt)) len))
  :hints
  (("Goal"
    :in-theory (disable length))
   ("Subgoal *1/3"
    :in-theory (disable car-lrat-flag-int-less-than-len)
    :use
    ((:instance
      car-lrat-flag-int-less-than-len
      (str str)
      (len (length str))
      (pos (lrat-flg-pos-skip-spaces str (length str) pos)))))))

(defthm int-listp-lrat-flg-int-list-until-0-or--
  (implies (integer-listp lst)
           (integer-listp (mv-nth 1 (lrat-flg-int-list-until-0-or-- str len pos lst cnt)))))

(in-theory (disable lrat-flg-int-list-until-0-or--))


(defun lrat-flg-int-rev-list-of-lists-until-0-or-- (str len pos lst cnt)

; Returns (mv pos-or-nil list-of-int-list)

  (declare (xargs :guard (and (lrat-guard str len pos)
                              (true-listp lst)
                              (natp cnt)
                              (<= cnt len))
                  :measure (acl2-count cnt)))
  (b* ((ch (char str pos))
       ((if (eql #\Newline ch)) (mv pos lst))
       ((mv pos-after-int-list int-list)
        (lrat-flg-int-list-until-0-or-- str len pos nil len))

       ((unless (and (integerp pos-after-int-list)
                     (< pos-after-int-list 72057594037927936)))
        (mv nil nil))

       (pos (u59 pos))
       (pos-after-int-list (u59 pos-after-int-list))
       ((unless (< pos pos-after-int-list)) (mv nil nil))

       (cnt (u59 cnt))
       (cnt-1 (s60 (1- cnt))))

    (if (mbe :logic (zp cnt) :exec (<= cnt 0))
        (mv nil nil) ; Use information about POS-AFTER-INT to remove CNT.
      (lrat-flg-int-rev-list-of-lists-until-0-or--
       str len pos-after-int-list (cons int-list lst) cnt-1))))


(defun lrat-line-mv (str len pos)
  (declare (xargs :guard (lrat-guard str len pos)
                  :guard-hints
                  (("Goal"
                    :in-theory (disable length)))))

; Expects POS at beginning of line
; Leaves  POS at \#Newline or :eof
; Reads next line or returns NIL.

  (b* ((pos (u59 pos))
       ((mv pos-after-line-number proof-step)
        (lrat-flg-nat str len pos))
       ;; Good line number?
       (in-bounds (and (integerp pos-after-line-number)
                       (< pos-after-line-number 72057594037927936)))
       ((unless in-bounds) (mv nil nil))
       (pos-after-line-number (u59 pos-after-line-number))

       (ch (char str pos-after-line-number))
       ((unless (eql ch #\Space)) (mv nil nil))

       ;; Step over space
       (pos-after-line-number+1 (u59 (1+ pos-after-line-number)))
       (len (u59 len))
       ((unless (< pos-after-line-number+1 len)) (mv nil nil))

       (ch (char str pos-after-line-number+1)))

    (if (eql ch #\d)

        ;; proof-step d <nat>* 0
        ;; Deletion:  (cons T <nat>*)
        (b* ((pos-after-line-number+2 (1+ pos-after-line-number+1))
             ((unless (< pos-after-line-number+2 len)) (mv nil nil))
             (ch (char str pos-after-line-number+2))
             ((unless (eql ch #\Space)) (mv nil nil))

             ;; Step over space
             (pos-after-line-number+3 (1+ pos-after-line-number+2))
             ((unless (< pos-after-line-number+3 len)) (mv nil nil))

             ((mv pos-after-nat-list nat-list)
              (lrat-flg-nat-list-until-0 str len pos-after-line-number+3 nil len))
             ((unless pos-after-nat-list) (mv nil nil))
             )
          (mv pos-after-nat-list (cons t nat-list)))

      ;; proof-step int* 0 <nats-until-0-or-first-neg-number> <negative-int nat*|0>*
      ;; Addition:  (list proof-step <list-of-ints> (rev <list-of-ints>))

      (b* (((mv pos-after-int-list-1 int-list-1)
            (lrat-flg-int-list-until-0 str len pos-after-line-number+1 nil len))
           ((unless (and (integerp pos-after-int-list-1)
                         (< pos-after-int-list-1 len)))
            (mv nil nil))

           ((mv pos-after-int-list-2 int-list-2)
            (lrat-flg-int-list-until-0-or--
             str len pos-after-int-list-1 nil len))
           ((unless pos-after-int-list-2)
            (mv nil nil))

           ((mv pos-after-int-list-3 int-list-3)
            (lrat-flg-int-rev-list-of-lists-until-0-or--
             str len pos-after-int-list-2 nil len))
           ((unless pos-after-int-list-3)
            (mv nil nil))

           ;; Put the answer together
           (ans (cons (cons proof-step int-list-1)
                      (cons int-list-2 int-list-3))))

        (mv pos-after-int-list-3 ans)))))

(in-theory (disable lrat-line-mv))


(defun lrat-str (str len pos cnt rev-lines)
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (natp len)
                              (equal len (length str))
                              (<= pos len)
                              (< len 72057594037927936)
                              (natp cnt))
                  :measure (acl2-count cnt)))

  (if (>= pos len)
      nil
    (b* (((mv pos-after-line line) (lrat-line-mv str len pos))
         ((unless (natp pos-after-line)) nil)
         ;; ((unless (< pos pos-after-line)) nil) ; when measure with pos
         ((unless (< pos-after-line len)) nil)
         ;; pos-after-line points to #\Newline or :EOF
         (ch (char str pos-after-line))
         ((unless (eql ch #\Newline)) nil)
         (pos-after-line+1 (1+ pos-after-line))

         ;; End of file
         ((unless (< pos-after-line+1 len)) (cons line rev-lines))
         ((if (mbe :logic (zp cnt) :exec (<= cnt 0)))
          nil))
      (lrat-str str len pos-after-line+1 (1- cnt) (cons line rev-lines)))))

(in-theory (disable lrat-str))

(defun lrat-read-file (file-name state)
  (declare (xargs :guard (stringp file-name)
                  :guard-hints (("Goal"
                                 :in-theory (disable open-input-channel)))
                  :stobjs state))
  (b* (; ((unless (state-p1 state)) nil)
       (str (read-file-into-string file-name))
       (len (length str))
       ((unless (lrat-guard str len 0)) NIL)
       (ans (my-rev (lrat-str str len 0 len nil))))
    ans))


(defun pos-to-eol+1 (str len pos)
  (declare (xargs :guard (lrat-guard str len pos)
                  :measure (nfix (- len pos))))
  (b* ((ch (char str pos))
       ((unless (< pos 72057594037927936)) len)

       (pos+1 (1+ (u56 pos)))
       ((if (eql ch #\Newline)) pos+1)

       (len (u56 len))
       ((if (mbe :logic (zp (- len pos+1))
                 :exec  (>= pos+1 len)))
        len))
    (pos-to-eol+1 str len pos+1)))

(defthm natp-pos-to-eol+1
  (implies (and (natp pos)
                (natp len))
           (<= 0 (pos-to-eol+1 str len pos))))

(defthm pos-to-eol+1-is-limited
  (implies (lrat-guard str len pos)
           (< (pos-to-eol+1 str len pos) 72057594037927936))
  :hints
  (("Goal"
    :induct (pos-to-eol+1 str len pos))))

(defun cnf-str (str len pos cnt line-num rev-lines file-name)
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (natp len)
                              (equal len (length str))
                              (< pos len)
                              (< len 72057594037927936)
                              (natp cnt)
                              (< cnt len)
                              (natp line-num))
                  :guard-hints
                  (("Goal"
                    :in-theory (disable length)))
                  :measure (acl2-count cnt)
                  )
           (ignorable rev-lines))
  (b* (((when (eql (char str pos) #\c))
        (er hard? 'parse-cnf-file
            "Line ~x0 of file ~x1 starts with character `c', perhaps ~
             indicating a DIMACS comment; but such lines are not supported by ~
             this checker."
            line-num
            file-name))
       ((mv pos-after-line int-list)
        (lrat-flg-int-list-until-0 str len pos nil cnt))
       ((when (null int-list))
        (er hard? 'parse-cnf-file
            "Line ~x0 of file ~x1 contains no data."
            line-num
            file-name))
       ((unless (integerp pos-after-line)) nil)
       ((unless (< pos-after-line len)) nil)

       (int-list (cons line-num int-list))  ; Include line number

       (pos-at-eol+1 (pos-to-eol+1 str len pos-after-line))

       ((unless (integerp pos-at-eol+1)) nil)
       ;; check for last entry
       ((if (= pos-at-eol+1 len)) (cons int-list rev-lines))
       ((unless (< pos-at-eol+1 len)) nil)

       ((if (mbe :logic (zp cnt) :exec (<= cnt 0)))
        nil))
    (cnf-str str len pos-at-eol+1 (1- (u59 cnt)) (1+ line-num)
             (cons int-list rev-lines)
             file-name)))

(in-theory (disable cnf-str))

(defun cnf-read-file (file-name state)
  (declare (xargs :guard (stringp file-name)
                  :guard-hints
                  (("Goal" :in-theory (disable read-file-into-string)))
                  :verify-guards nil
                  :stobjs state))
  (b* (; ((unless (state-p1 state)) nil)
       (str (read-file-into-string file-name))
       (len (length str))
       ((unless (lrat-guard str len 0)) NIL)
       (pos (pos-to-eol+1 str len 0))
       (ans (cnf-str str len pos (1- len) 1 nil file-name)))
    ans))

(defun parse-lrat-file (filename state)
  (value (lrat-read-file filename state)))

(defun parse-cnf-file (filename state)
  (value (cnf-read-file filename state)))


; Keep rest of this file from the original...

(defun verify-lrat-proof-fn (cnf-file lrat-file incomplete-okp state)
  (b* (((er formula) (time$ (parse-cnf-file cnf-file state)))
       ((er proof) (time$ (parse-lrat-file lrat-file state))))
    (value (time$ (valid-proofp$-top formula proof incomplete-okp)))))

(defmacro verify-lrat-proof (cnf-file lrat-file
                                      &optional (incomplete-okp 'nil))
  `(verify-lrat-proof-fn ,cnf-file ,lrat-file ,incomplete-okp state))

; Example:
; (verify-lrat-proof "tests/example-4-vars.cnf" "tests/example-4-vars.lrat")

; Some debugging tools.

(defun show-proof-entry (entry)
  (cond ((proof-entry-deletion-p entry)
         (cons 'deletion (cdr entry)))
        (t (list :index (access add-step entry :index)
                 :clause (access add-step entry :clause)
                 :rup-indices (access add-step entry :rup-indices)
                 :drat-hints (access add-step entry :drat-hints)))))

(defun show-lrat-proof (proof acc)
  (cond ((endp proof) (reverse acc))
        (t (show-lrat-proof (cdr proof)
                            (cons (show-proof-entry (car proof)) acc)))))

(defun show-lrat-parse (lrat-file state)
  (er-let* ((proof (parse-lrat-file lrat-file state)))
    (value (show-lrat-proof proof nil))))

(defun show-drat-hints-raw (drat-hints acc)
  (cond ((endp drat-hints) acc)
        (t (show-drat-hints-raw (cdr drat-hints)
                                (cons (- (caar drat-hints))
                                      (append (cdar drat-hints) acc))))))

(defun show-proof-entry-raw (index entry)
  (cond ((proof-entry-deletion-p entry)
         (list* index 'd (cdr entry)))
        (t (cons (access add-step entry :index)
                 (append (access add-step entry :clause)
                         (cons 0
                               (append (access add-step entry :rup-indices)
                                       (show-drat-hints-raw
                                        (access add-step entry :drat-hints)
                                        nil))))))))

(defun show-lrat-proof-raw (index proof acc)
  (cond ((endp proof) (reverse acc))
        (t (let ((entry-raw (show-proof-entry-raw index (car proof))))
             (show-lrat-proof-raw (car entry-raw)
                                  (cdr proof)
                                  (cons entry-raw acc))))))

(program)

(defun show-lrat-parse-raw (lrat-file state)
  (er-let* ((proof (parse-lrat-file lrat-file state)))
    (pprogn (acl2::print-on-separate-lines
             (show-lrat-proof-raw nil proof nil)
             nil *standard-co* state)
            (value :invisible))))

; Test driver

(defun lrat-test-fn (doublets dir okp chan state)
  (cond
   ((endp doublets)
    (pprogn (fms "OVERALL RESULT: ~s0~|~%"
                 (list (cons #\0 (if okp "success" "FAILURE")))
                 chan state nil)
            (value okp)))
   (t (let* ((d (car doublets))
             (cnf (concatenate 'string dir (car d)))
             (lrat (concatenate 'string dir (cadr d)))
             (incomplete-okp (caddr d)))
        (pprogn
         (fms "Starting ~x0.~|"
              (list (cons #\0 `(verify-lrat-proof ,cnf ,lrat ,@(cddr d))))
              chan state nil)
         (er-let* ((val (verify-lrat-proof cnf lrat incomplete-okp)))
           (pprogn
            (princ$ "Result: " chan state)
            (princ$ (if val "success" "FAILURE") chan state)
            (newline chan state)
            (lrat-test-fn (cdr doublets) dir (and val okp) chan state))))))))

(defmacro lrat-test (doublets &optional (dir '""))

; This should be run in the tests/ directory, or else in the directory dir
; relative to the current directory (e.g., "../tests" or "../tests/").

  (declare (xargs :guard (stringp dir))) ; partial guard
  (let ((dir (if (and (not (equal dir ""))
                      (not (eql (char dir (1- (length dir)))
                                #\/)))
                 (concatenate 'string dir "/")
               dir)))
    `(lrat-test-fn ',doublets ',dir t (standard-co state) state)))
