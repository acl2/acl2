; ACL2 String Library
; Copyright (C) 2009 Centaur Technology
; Contact: jared@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "STR")
(include-book "digitp")
(include-book "tools/mv-nth" :dir :system)
(include-book "tools/bstar" :dir :system)
(local (include-book "arithmetic"))
(local (include-book "char-support"))



(defund parse-nat-from-charlist (x val len)

; Tries to extract a natural number from the beginning of the character list x.
; VAL is an accumulator for the value of the digits we have read so far, and
; LEN is an accumulator for the number of digits we have read.  We return (MV
; VAL LEN REST), where REST is the non-numeric portion of the character list.

  (declare (type integer val)
           (type integer len)
           (xargs :guard (and (character-listp x)
                              (natp val)
                              (natp len))
                  :verify-guards nil))

  (mbe :logic
       (cond ((atom x)
              (mv (nfix val) (nfix len) nil))
             ((digitp (car x))
              (let ((digit-val (digit-val (car x))))
                (parse-nat-from-charlist (cdr x)

; A silly idea I have would be to instead multiply each character by 16, which
; would mean that the operation could be done via ash and logior.  I think the
; values produced by such a scheme would be ordered in the same way that the
; values here are ordered.  And, rudimentary speed test suggests it could be as 
; much as 50% faster.  The proof seems difficult, so for now I don't have the
; patience to attempt it.

                                         (+ digit-val (* 10 (nfix val)))
                                         (+ 1 (nfix len)))))
             (t
              (mv (nfix val) (nfix len) x)))
       :exec 
       (cond ((atom x)
              (mv val len nil))
             (t
              (let ((code (the (unsigned-byte 8) (char-code (the character (car x))))))
                (declare (type (unsigned-byte 8) code))
                (if (and (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code))
                         (<= (the (unsigned-byte 8) code) (the (unsigned-byte 8) 57)))
                    (let ((digit-val (the (unsigned-byte 8)
                                       (- (the (unsigned-byte 8) code)
                                          (the (unsigned-byte 8) 48)))))
                      (parse-nat-from-charlist
                       (cdr x)
                       (the integer (+ (the (unsigned-byte 8) digit-val)
                                       (the integer (* 10 (the integer val)))))
                       (the integer (+ 1 (the integer len)))))
                  (mv val len x)))))))

(verify-guards parse-nat-from-charlist
               :hints(("Goal" :in-theory (enable parse-nat-from-charlist
                                                 digitp
                                                 digit-val
                                                 char-fix))))

(encapsulate
 ()
 (local (defund leading-digits-value (x val)
          (declare (xargs :verify-guards nil))
          (if (consp x)
              (if (digitp (car x))
                  (leading-digits-value (cdr x)
                                        (+ (digit-val (car x)) (* 10 (nfix val))))
                (nfix val))
            (nfix val))))

 (local (defthm lemma-1
          (equal (mv-nth 0 (parse-nat-from-charlist x val len))
                 (leading-digits-value x val))
          :hints(("Goal" :in-theory (enable parse-nat-from-charlist
                                            leading-digits-value)))))

 (local (defthm lemma-2
          (equal (leading-digits-value x val)
                 (digit-list-value1 (take-leading-digits x) val))
          :hints(("Goal" :in-theory (e/d (leading-digits-value
                                          digit-list-value1
                                          take-leading-digits)
                                         (digit-list-value1-removal))))))

 (defthm val-of-parse-nat-from-charlist
   (equal (mv-nth 0 (parse-nat-from-charlist x val len))
          (+ (digit-list-value (take-leading-digits x))
             (* (nfix val) (expt 10 (len (take-leading-digits x))))))))


(encapsulate
 ()
 (local (defund count-leading-digits1 (x len)
          (declare (xargs :verify-guards nil))
          (if (consp x)
              (if (digitp (car x))
                  (count-leading-digits1 (cdr x) (+ 1 (nfix len)))
                (nfix len))
            (nfix len))))

 (local (defthm lemma-1
          (equal (mv-nth 1 (parse-nat-from-charlist x val len))
                 (count-leading-digits1 x len))
          :hints(("Goal" :in-theory (enable parse-nat-from-charlist 
                                            count-leading-digits1)))))

 (local (defthm lemma-2
          (equal (count-leading-digits1 x len)
                 (+ (nfix len)
                    (len (take-leading-digits x))))
          :hints(("Goal" :in-theory (enable count-leading-digits1
                                            take-leading-digits)))))

 (defthm len-of-parse-nat-from-charlist
   (equal (mv-nth 1 (parse-nat-from-charlist x val len))
          (+ (nfix len) (len (take-leading-digits x))))))
  


(defthm rest-of-parse-nat-from-charlist
  (equal (mv-nth 2 (parse-nat-from-charlist x val len))
         (skip-leading-digits x))
  :hints(("Goal" :in-theory (enable parse-nat-from-charlist
                                    skip-leading-digits))))



(defund charlistnat< (x y)

  ":Doc-Section Str
  Mixed alphanumeric character-list less-than test~/
  
  We order character lists in a case-sensitive way.  But unlike a regular character-code
  based ordering, we identify natural numbers which occur in a string, and group them 
  together to sort them as numbers. 

  That is, most string sorts, when given strings \"x0\" through \"x11\", will put them 
  into a peculiar order, \"x0\", \"x1\", \"x10\", \"x11\", \"x2\", \"x3\", ..., but in
  ~c[charlistnat<], the adjacent digits are grouped to produce the more human-friendly
  ordering, \"x0\", \"x1\", \"x2\", ..., \"x9\", \"x10\", \"x11\".

  We consider leading zeroes to be part of the number.  To sensibly handle such zeroes,
  think not of grouping adjacent digits only into a natural number, but into pairs of 
  value and length, which are to be sorted first by value and then by length.  Under 
  this approach, a string such as \"x0\" is considered to be less than \"x00\", etc.
  ~/
  ~l[strnat<], ~pl[icharlist<]"

  (declare (xargs :guard (and (character-listp x)
                              (character-listp y))
                  :measure (len x)))

  (cond ((atom y)
         nil)
        ((atom x) 
         t)
        ((and (digitp (car x))
              (digitp (car y)))
         (b* (((mv v1 l1 rest-x) (parse-nat-from-charlist x 0 0))
              ((mv v2 l2 rest-y) (parse-nat-from-charlist y 0 0)))

; The basic idea is to order numbers by their values, and then by their
; lengths.  This second part only is necessary to accomodate leading zeroes.

             (cond ((or (< v1 v2)
                        (and (= v1 v2)
                             (< l1 l2)))
                    t)
                   ((or (< v2 v1)
                        (and (= v1 v2)
                             (< l2 l1)))
                    nil)
                   (t
                    (charlistnat< rest-x rest-y)))))

        ((char< (car x) (car y))
         t)
        ((char< (car y) (car x))
         nil)
        (t 
         (charlistnat< (cdr x) (cdr y)))))

(defcong charlisteqv equal (charlistnat< x y) 1
  :hints(("Goal" :in-theory (enable charlistnat<))))

(defcong charlisteqv equal (charlistnat< x y) 2
  :hints(("Goal" :in-theory (enable charlistnat<))))

(defthm charlistnat<-irreflexive
  (not (charlistnat< x x))
  :hints(("Goal" :in-theory (enable charlistnat<))))

(defthm charlistnat<-antisymmetric
  (implies (charlistnat< x y)
           (not (charlistnat< y x)))
  :hints(("Goal" :in-theory (enable charlistnat<))))

(encapsulate
 ()
 (local (defthm char<-nonsense-1
          (implies (and (not (char< x z))
                        (char< x y))
                   (not (char< y z)))
          :hints(("Goal" :in-theory (enable char<)))))

 (local (defthm char<-nonsense-2
          (implies (and (char< a y)
                        (not (char< a z))
                        (digitp y)
                        (digitp z))
                   (digitp a))
          :hints(("Goal" :in-theory (enable char< digitp)))))

 (local (defthm char<-nonsense-3
          (implies (and (not (char< x a))
                        (char< y a)
                        (digitp x)
                        (digitp y))
                   (digitp a))
          :hints(("Goal" :in-theory (enable char< digitp)))))

 (local (defthm char<-nonsense-4
          (implies (and (digitp x)
                        (digitp z)
                        (char< x y)
                        (char< y z))
                   (digitp y))
          :hints(("Goal" :in-theory (enable digitp char<)))))

 (defthm charlistnat<-transitive
   (implies (and (charlistnat< x y)
                 (charlistnat< y z))
            (charlistnat< x z))
   :hints(("Goal" :in-theory (enable charlistnat<)))))



(local 
 (encapsulate
  ()

  ; A slightly tricky lemma about arithmetic.

  (local (defun expr (a x b n)
           (+ a (* x (expt b n)))))

  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

  (local (defthm mod-of-expr
           (implies (and (natp a1)
                         (natp x1)
                         (natp n)
                         (natp b)
                         (< a1 (expt b n))
                         (<= x1 b))
                    (equal (mod (expr a1 x1 b n)
                                (expt b n))
                           a1))))

  (local (defthm main-lemma
           (implies (and (natp a1)
                         (natp a2)
                         (natp x1)
                         (natp x2)
                         (natp n)
                         (natp b)
                         (< a1 (expt b n))
                         (< a2 (expt b n))
                         (<= x1 b)
                         (<= x2 b)
                         (not (equal a1 a2)))
                    (not (equal (expr a1 x1 b n)
                                (expr a2 x2 b n))))
           :hints(("Goal" :in-theory (disable expr mod-of-expr)
                   :use ((:instance mod-of-expr)
                         (:instance mod-of-expr (a1 a2) (x1 x2)))))))

  (defthmd arith-lemma-1
    (implies (and (natp a1)
                  (natp a2)
                  (natp x1)
                  (natp x2)
                  (natp n)
                  (natp b)
                  (< a1 (expt b n))
                  (< a2 (expt b n))
                  (<= x1 b)
                  (<= x2 b)
                  (not (equal a1 a2)))
             (not (equal (+ a1 (* x1 (expt b n)))
                         (+ a2 (* x2 (expt b n))))))
    :hints(("Goal" 
            :in-theory (enable expr)
            :use ((:instance main-lemma)))))))


(encapsulate
 ()

; The main proof of trichotomy
 
 (local (defthm lemma-1
          (IMPLIES (AND (NOT (EQUAL (DIGIT-LIST-VALUE X2)
                                    (DIGIT-LIST-VALUE Y2)))
                        (NOT (EQUAL X2 Y2))
                        (CHARACTERP X1)
                        (CHARACTERP Y1)
                        (CHARACTER-LISTP X2)
                        (CHARACTER-LISTP Y2)
                        (DIGITP X1)
                        (DIGITP Y1)
                        (DIGIT-LISTP X2)
                        (DIGIT-LISTP Y2)
                        (EQUAL (LEN X2) (LEN Y2)))
                   (NOT (EQUAL (+ (DIGIT-LIST-VALUE X2)
                                  (* (DIGIT-VAL X1) (EXPT 10 (LEN X2))))
                               (+ (DIGIT-LIST-VALUE Y2)
                                  (* (DIGIT-VAL Y1) (EXPT 10 (LEN X2)))))))
          :hints(("Goal"
                  :use ((:instance arith-lemma-1
                                   (a1 (digit-list-value x2))
                                   (a2 (digit-list-value y2))
                                   (x1 (digit-val x1))
                                   (x2 (digit-val y1))
                                   (b 10)
                                   (n (len x2))))))))

 (local (defun my-induction (x y)
          (if (and (consp x)
                   (consp y))
              (my-induction (cdr x) (cdr y))
            nil)))

 (local (defthm lemma-2
          (implies (and
                    (character-listp x)
                    (character-listp y)
                    (digit-listp x)
                    (digit-listp y)
                    (equal (len x) (len y)))
                   (equal (equal (digit-list-value x) 
                                 (digit-list-value y))
                          (equal x y)))
          :hints(("Goal" 
                  :induct (my-induction x y)
                  :in-theory (enable digit-listp
                                     digit-list-value)))))

 (local (defthm lemma-3
          (implies (and (equal (len (take-leading-digits y))
                               (len (take-leading-digits x)))
                        (equal (digit-list-value (take-leading-digits y))
                               (digit-list-value (take-leading-digits x)))
                        (charlisteqv (skip-leading-digits x)
                                     (skip-leading-digits y)))
                   (equal (charlisteqv x y)
                          t))
          :hints(("Goal" :in-theory (enable take-leading-digits
                                            skip-leading-digits
                                            charlisteqv
                                            digit-list-value)))))
  
 (defthm charlistnat<-trichotomy-weak
   (implies (and (not (charlistnat< x y))
                 (not (charlistnat< y x)))
            (equal (charlisteqv x y)
                   t))
   :hints(("Goal" :in-theory (enable charlistnat<)))))
         
(defthm charlistnat<-trichotomy-strong
  (equal (charlistnat< x y)
         (and (not (charlisteqv x y))
              (not (charlistnat< y x))))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))



(defund parse-nat-from-string (x val len n xl)

; This is like parse-nat-from-charlist.  X is a string instead of a character
; list, val and len are the accumulators as before, n is our current position
; in x, and xl is the pre-computed length of x.  We return (mv val len) where
; val and len are as before.  We don't return an updated index or anything, 
; since that's easy to compute via adding len to the current index.

  (declare (type string x)
           (type integer val)
           (type integer len)
           (type integer n)
           (type integer xl)
           (xargs :guard (and (stringp x)
                              (natp val)
                              (natp len)
                              (natp n)
                              (equal xl (length x))
                              (<= n xl))
                  :measure (nfix (- (nfix xl) (nfix n)))
                  :verify-guards nil))

  (mbe :logic
       (cond ((zp (- (nfix xl) (nfix n)))
              (mv (nfix val) (nfix len)))
             ((digitp (char x n))
              (let ((digit-val (digit-val (char x n))))
                (parse-nat-from-string x
                                       (+ digit-val (* 10 (nfix val)))
                                       (+ 1 (nfix len))
                                       (+ 1 (nfix n))
                                       (nfix xl))))
             (t
              (mv (nfix val) (nfix len))))
       :exec 
       (cond ((= (the integer n) (the integer xl))
              (mv val len))
             (t
              (let ((code (the (unsigned-byte 8) 
                            (char-code (the character (char (the string x) 
                                                            (the integer n)))))))
                (declare (type (unsigned-byte 8) code))
                (if (and (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code))
                         (<= (the (unsigned-byte 8) code) (the (unsigned-byte 8) 57)))
                    (let ((digit-val (the (unsigned-byte 8)
                                       (- (the (unsigned-byte 8) code)
                                          (the (unsigned-byte 8) 48)))))
                      (parse-nat-from-string
                       (the string x)
                       (the integer (+ (the (unsigned-byte 8) digit-val)
                                       (the integer (* 10 (the integer val)))))
                       (the integer (+ 1 (the integer len)))
                       (the integer (+ 1 (the integer n)))
                       (the integer xl)))
                  (mv val len)))))))

(verify-guards parse-nat-from-string
               :hints(("Goal" :in-theory (enable digitp digit-val))))

(defthm natp-of-val-of-parse-nat-from-string
  (and (integerp (mv-nth 0 (parse-nat-from-string x val len n xl)))
       (<= 0 (mv-nth 0 (parse-nat-from-string x val len n xl))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable parse-nat-from-string))))

(defthm natp-of-len-of-parse-nat-from-string
  (and (integerp (mv-nth 1 (parse-nat-from-string x val len n xl)))
       (<= 0 (mv-nth 1 (parse-nat-from-string x val len n xl))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable parse-nat-from-string))))

(defthm progress-of-parse-nat-from-string
  (implies (and (equal xl (length x))
                (or (< 0 (nfix len))
                      (digitp (char x (nfix n)))))
           (< 0 (mv-nth 1 (parse-nat-from-string x val len n xl))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" 
          :induct (parse-nat-from-string x val len n xl)
          :in-theory (enable parse-nat-from-string))))

(defthm val-of-parse-nat-from-string
  (implies (and (stringp x)
                (natp val)
                (natp len)
                (natp n)
                (equal xl (length x))
                (<= n xl))
           (equal (mv-nth 0 (parse-nat-from-string x val len n xl))
                  (mv-nth 0 (parse-nat-from-charlist (nthcdr n (coerce x 'list)) val len))))
  :hints(("Goal"
          :induct (parse-nat-from-string x val len n xl)
          :in-theory (e/d (parse-nat-from-string
                           parse-nat-from-charlist)
                          (val-of-parse-nat-from-charlist))
          :do-not '(generalize fertilize))))

(defthm len-of-parse-nat-from-string
  (implies (and (stringp x)
                (natp val)
                (natp len)
                (natp n)
                (equal xl (length x))
                (<= n xl))
           (equal (mv-nth 1 (parse-nat-from-string x val len n xl))
                  (mv-nth 1 (parse-nat-from-charlist (nthcdr n (coerce x 'list)) val len))))
  :hints(("Goal"
          :induct (parse-nat-from-string x val len n xl)
          :in-theory (e/d (parse-nat-from-string
                           parse-nat-from-charlist)
                          (len-of-parse-nat-from-charlist))
          :do-not '(generalize fertilize))))



(defund strnat<-aux (x y xn yn xl yl)

; This is like charlistnat< except for strings.  X and Y are the strings being
; compared, xn and yn are the current indexes we are comparing in x and y, and
; xl and yl are the lengths of x and y, respectively.

  (declare (type string x)
           (type string y)
           (type integer xn)
           (type integer yn)
           (type integer xl)
           (type integer yl)
           (xargs :guard (and (stringp x)
                              (stringp y)
                              (natp xn)
                              (natp yn)
                              (equal xl (length x))
                              (equal yl (length y))
                              (<= xn xl)
                              (<= yn yl))
                  :verify-guards nil
                  :measure 
                  (let* ((x  (if (stringp x) x ""))
                         (y  (if (stringp y) y ""))
                         (xn (nfix xn))
                         (yn (nfix yn))
                         (xl (length x))
                         (yl (length y)))
                    (nfix (+ (- yl yn) (- xl xn))))
                  :hints(("Goal" :in-theory (disable val-of-parse-nat-from-string
                                                     len-of-parse-nat-from-string))))
           (ignorable xl yl))
  (mbe :logic 
       (let* ((x  (if (stringp x) x ""))
              (y  (if (stringp y) y ""))
              (xn (nfix xn))
              (yn (nfix yn))
              (xl (length x))
              (yl (length y)))
         (cond ((zp (- yl yn))
                nil)
               ((zp (- xl xn))
                t)
               ((and (digitp (char x xn))
                     (digitp (char y yn)))
                (b* (((mv v1 l1)
                      (parse-nat-from-string x 0 0 xn xl))
                     ((mv v2 l2) 
                      (parse-nat-from-string y 0 0 yn yl)))
                    (cond ((or (< v1 v2)
                               (and (= v1 v2)
                                    (< l1 l2)))
                           t)
                          ((or (< v2 v1)
                               (and (= v1 v2)
                                    (< l2 l1)))
                           nil)
                          (t
                           (strnat<-aux x y (+ xn l1) (+ yn l2) xl yl)))))
               ((char< (char x xn) 
                       (char y yn))
                t)
               ((char< (char y yn)
                       (char x xn))
                nil)
               (t 
                (strnat<-aux x y (+ 1 xn) (+ 1 yn) xl yl))))
       :exec
       (cond ((= (the integer yn) (the integer yl))
              nil)
             ((= (the integer xn) (the integer xl))
              t)
             (t
              (let* ((char-x (the character (char (the string x) (the integer xn))))
                     (char-y (the character (char (the string y) (the integer yn))))
                     (code-x (the (unsigned-byte 8) (char-code (the character char-x))))
                     (code-y (the (unsigned-byte 8) (char-code (the character char-y)))))
                (declare (type character char-x)
                         (type character char-y)
                         (type (unsigned-byte 8) code-x)
                         (type (unsigned-byte 8) code-y))
                (cond 
                 ((and 
                   ;; (digitp (char x xn))
                   (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code-x))
                   (<= (the (unsigned-byte 8) code-x) (the (unsigned-byte 8) 57))
                   ;; (digitp (char y yn))
                   (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code-y))
                   (<= (the (unsigned-byte 8) code-y) (the (unsigned-byte 8) 57)))
                  (b* (((mv v1 l1)
                        (parse-nat-from-string (the string x)
                                               (the integer 0)
                                               (the integer 0)
                                               (the integer xn)
                                               (the integer xl)))
                       ((mv v2 l2) 
                        (parse-nat-from-string (the string y)
                                               (the integer 0)
                                               (the integer 0)
                                               (the integer yn)
                                               (the integer yl))))
                      (cond ((or (< (the integer v1) (the integer v2))
                                 (and (= (the integer v1) (the integer v2))
                                      (< (the integer l1) (the integer l2))))
                             t)
                            ((or (< (the integer v2) (the integer v1))
                                 (and (= (the integer v1) (the integer v2))
                                      (< (the integer l2) (the integer l1))))
                             nil)
                            (t
                             (strnat<-aux (the string x)
                                          (the string y)
                                          (the integer (+ (the integer xn) (the integer l1)))
                                          (the integer (+ (the integer yn) (the integer l2)))
                                          (the integer xl)
                                          (the integer yl))))))
                 ((< (the (unsigned-byte 8) code-x) (the (unsigned-byte 8) code-y))
                  t)
                 ((< (the (unsigned-byte 8) code-y) (the (unsigned-byte 8) code-x))
                  nil)
                 (t 
                  (strnat<-aux (the string x)
                               (the string y)
                               (the integer (+ (the integer 1) (the integer xn)))
                               (the integer (+ (the integer 1) (the integer yn)))
                               (the integer xl)
                               (the integer yl)))))))))

(verify-guards strnat<-aux
               :hints((and stable-under-simplificationp
                           '(:in-theory (enable digitp
                                                digit-val
                                                char-fix
                                                char<)))))

(encapsulate
 ()
 (local (defthm skip-leading-digits-to-nthcdr
          (implies (force (true-listp x))
                   (equal (skip-leading-digits x)
                          (nthcdr (len (take-leading-digits x)) x)))
          :hints(("Goal" :in-theory (enable skip-leading-digits take-leading-digits)))))

 (defthm strnat<-aux-correct
   (implies (and (stringp x)
                 (stringp y)
                 (natp xn)
                 (natp yn)
                 (equal xl (length x))
                 (equal yl (length y))
                 (<= xn xl)
                 (<= yn yl))
            (equal (strnat<-aux x y xn yn xl yl)
                   (charlistnat< (nthcdr xn (coerce x 'list))
                                 (nthcdr yn (coerce y 'list)))))
   :hints(("Goal" 
           :induct (strnat<-aux x y xn yn xl yl)
           :expand ((charlistnat< (nthcdr xn (coerce x 'list))
                                  (nthcdr yn (coerce y 'list))))
           :in-theory (e/d (strnat<-aux charlistnat<)
                           ())
           :do-not '(generalize fertilize)))))




(defund strnat< (x y)

  ":Doc-Section Str
  Mixed alphanumeric string less-than test~/

  This is like ~il[charlistnat<], but for strings.  It avoids coercing the 
  strings to character-lists, and is altogether pretty fast.~/
  " 

  (declare (type string x)
           (type string y))

  (mbe :logic
       (charlistnat< (coerce x 'list)
                     (coerce y 'list))

       :exec 
       (strnat<-aux (the string x)
                    (the string y)
                    (the integer 0)
                    (the integer 0)
                    (the integer (length (the string x)))
                    (the integer (length (the string y))))))

(defthm strnat<-irreflexive
  (not (strnat< x x))
  :hints(("Goal" :in-theory (enable strnat<))))

(defthm strnat<-antisymmetric
  (implies (strnat< x y)
           (not (strnat< y x)))
  :hints(("Goal" :in-theory (enable strnat<))))

(defthm strnat<-transitive
  (implies (and (strnat< x y)
                (strnat< y z))
           (strnat< x z))
  :hints(("Goal" :in-theory (enable strnat<))))

(defthm strnat<-transitive-alt
  (implies (and (strnat< y z)
                (strnat< x y))
           (strnat< x z))
  :hints(("Goal" :in-theory (enable strnat<))))



#||

;; Using STP.

(include-book ;; fool dependency scanner
 "top")

(defn symnat< (sym1 sym2)
  (STR::strnat< (safe-symbol-name sym1)
                (safe-symbol-name sym2)))

(defthm symnat<-transitive
  (implies (and (symnat< x y)
                (symnat< y z))
           (symnat< x z)))

(defsort :compare< symnat<
         :prefix symnat<)

:q

(defparameter *prefixes* (list "foo" "bar" "baz" "a" "b" "c"))

(defparameter *test-strings*
  (let ((plen (length *prefixes*)))
    (loop for i from 1 to 10000 collect
          (concatenate 'string 
                       (nth (mod i plen) *prefixes*)
                       "-"
                       (coerce (explode-atom i 10) 'string)
                       "-suff"))))

(defparameter *test-syms*
  (loop for str in *test-strings* collect (intern str "ACL2")))

(plev-max)
(take 30 *test-syms*)

(equal (symnat<-sort *test-syms*)
       (symsort *test-syms*))

;; 3.308 seconds, 198,769,472 bytes allocated
(progn 
  (ccl::gc)
  (time (loop for i fixnum from 1 to 100 do
              (symnat<-sort *test-syms*)))
  nil)

;; 85.062 seconds, 11,405,636,416 bytes allocated
(progn 
  (ccl::gc)
  (time (loop for i fixnum from 1 to 100 do
              (symsort *test-syms*)))
  nil)

||#
