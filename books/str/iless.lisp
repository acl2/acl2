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
(include-book "doc")
(include-book "ieqv")
(local (include-book "unicode/nthcdr" :dir :system))
(local (include-book "arithmetic"))


(local
 (defthm equal-of-char-code-and-char-code
   (implies (and (characterp x)
                 (characterp y))
            (equal (equal (char-code x) (char-code y))
                   (equal x y)))
   :hints(("Goal" :use acl2::equal-char-code))))

(local 
 (defthm equal-of-char-code-and-constant
   (implies (syntaxp (quotep c))
            (equal (equal (char-code x) c)
                   (if (characterp x)
                       (and (natp c)
                            (<= c 255)
                            (equal x (code-char c)))
                     (equal c 0))))))

(local
 (defthm code-char-when-not-natp
   (implies (not (natp x))
            (equal (code-char x)
                   (code-char 0)))
   :hints(("Goal" :use ((:instance acl2::completion-of-code-char))))))

(local
 (defthm equal-of-char-code-of-plus
   (implies (and (syntaxp (quotep a))
                 (syntaxp (quotep const))
                 (characterp a)
                 (natp y)
                 (natp const)
                 (<= (+ const y) 255))
            (equal (equal a (code-char (+ const y)))
                   (equal y (- (char-code a) const))))))

(local 
 (encapsulate
  ()
  (local (defund exhaustive-test (n)
           (and (let ((x (code-char n)))
                  (equal (char-downcase x)
                         (if (and (<= (char-code #\A) (char-code x))
                                  (<= (char-code x) (char-code #\Z)))
                             (code-char (+ (char-code x) 32))
                           x)))
                (or (zp n)
                    (exhaustive-test (- n 1))))))

  (local (defthm lemma1
           (implies (and (natp n)
                         (<= n 255))
                    (equal (char-code (code-char n)) 
                           n))))

  (local (defthm lemma2
           (implies (and (natp n)
                         (natp m)
                         (exhaustive-test n)
                         (= x (code-char m))
                         (<= m n)
                         (<= n 255))
                    (equal (char-downcase x)
                           (if (and (<= (char-code #\A) (char-code x))
                                    (<= (char-code x) (char-code #\Z)))
                               (code-char (+ (char-code x) 32))
                             x)))
           :hints(("Goal" 
                   :induct (exhaustive-test n)
                   :in-theory (enable exhaustive-test)))))

  (local (defthm lemma3
           (implies (characterp x)
                    (equal (char-downcase x)
                           (if (and (<= (char-code #\A) (char-code x))
                                    (<= (char-code x) (char-code #\Z)))
                               (code-char (+ (char-code x) 32))
                             x)))
           :hints(("Goal"
                   :in-theory (disable lemma2)
                   :use ((:instance lemma2 
                                    (n 255)
                                    (m (char-code x))))))))

  (local (defthm lemma4
           (implies (not (characterp x))
                    (equal (char-downcase x)
                           (code-char 0)))
           :hints(("Goal" :in-theory (enable char-downcase)))))
                       
  (defthm char-downcase-redefinition
    (equal (char-downcase x)
           (if (characterp x)
               (if (and (<= (char-code #\A) (char-code x))
                        (<= (char-code x) (char-code #\Z)))
                   (code-char (+ (char-code x) 32))
                 x)
             (code-char 0)))
    :rule-classes :definition)))


(local 
 (encapsulate
  ()
  (local (defund exhaustive-test1 (x y)
           (and (equal (equal (code-char x) (code-char y))
                       (equal x y))
                (or (zp y)
                    (exhaustive-test1 x (- y 1))))))

  (local (defund exhaustive-test2 (x y)
           (and (exhaustive-test1 x y)
                (or (zp x)
                    (exhaustive-test2 (- x 1) y)))))

  (local (defthm lemma1
           (implies (and (exhaustive-test1 x y)
                         (natp x)
                         (natp y)
                         (natp m)
                         (<= m y)
                         (<= x 255)
                         (<= y 255))
                    (equal (equal (code-char x) (code-char m))
                           (equal x m)))
           :hints(("Goal" :in-theory (enable exhaustive-test1)))))

  (local (defthm lemma2
           (implies (and (exhaustive-test2 x y)
                         (natp x)
                         (natp y)
                         (<= x 255)
                         (<= y 255)
                         (natp n)
                         (natp m)
                         (<= n x)
                         (<= m y))
                    (equal (equal (code-char n) (code-char m))
                           (equal n m)))
           :hints(("Goal" 
                   :in-theory (enable exhaustive-test2)
                   :induct (exhaustive-test2 x y))
                  ("Subgoal *1/1" 
                   :in-theory (disable lemma1)
                   :use ((:instance lemma1
                                    (x 0)
                                    (m m)
                                    (y y)))))))

  (defthm equal-of-code-chars
    (implies (and (natp n)
                  (natp m)
                  (<= n 255)
                  (<= m 255))
             (equal (equal (code-char n) (code-char m))
                    (equal n m)))
    :hints(("Goal" 
            :in-theory (disable lemma2)
            :use ((:instance lemma2
                             (x 255)
                             (y 255)
                             (n n)
                             (m m))))))))


(local 
 (encapsulate
  ()
  (local (defund exhaustive-test (n)
           (and (let ((x (code-char n)))
                  (implies (and (<= 65 (char-code x))
                                (<= (char-code x) 90))
                           (and (standard-char-p x)
                                (standard-char-p (code-char (+ (char-code x) 32))))))
                (or (zp n)
                    (exhaustive-test (- n 1))))))

  (local (defthm lemma
           (implies (and (natp n)
                         (natp m)
                         (exhaustive-test n)
                         (= x (code-char m))
                         (<= m n)
                         (<= n 255))
                    (implies (and (<= 65 (char-code x))
                                  (<= (char-code x) 90))
                             (and (standard-char-p x)
                                  (standard-char-p (code-char (+ (char-code x) 32))))))
           :hints(("goal" 
                   :induct (exhaustive-test n)
                   :in-theory (enable exhaustive-test)))))

  (defthm standard-char-p-when-upper-case
    (implies (and (<= 65 (char-code x))
                  (<= (char-code x) 90))
             (standard-char-p x))
    :hints(("Goal" 
            :in-theory (disable lemma)
            :use ((:instance lemma 
                             (n 255)
                             (m (char-code x)))))))

  (defthm standard-char-p-of-char-downcase
    (implies (and (<= 65 (char-code x))
                  (<= (char-code x) 90))
             (standard-char-p (code-char (+ 32 (char-code x)))))
    :hints(("goal" 
            :in-theory (disable lemma)
            :use ((:instance lemma 
                             (n 255)
                             (m (char-code x)))))))))


 
(defund ichar< (x y)

  ":Doc-Section Str
  Case-insensitive character less-than test~/

  Our approach is basically to downcase upper-case letters.  Something subtle
  about this is that, in the ASCII character ordering, the upper-case
  characters do not immediately preceede the lower-case ones.  That is,
  upper-case Z is at 90, but lower-case a does not start until 97.  So, in our
  approach, the 6 intervening characters (the square brackets, backslash, hat,
  underscore, and backtick) are considered \"smaller\" than letters, even though
  in regular ASCII ordering they are \"larger\" than the upper-case letters.
  ~/
 
  ~l[istr<] and ~pl[icharlist<]"

  (declare (type character x)
           (type character y))

  (mbe :logic
       (let* ((xc (if (characterp x) 
                      (char-code x)
                    0))
              (yc (if (characterp y)
                      (char-code y)
                    0))
              (xc-fix (if (and (<= (char-code #\A) xc) (<= xc (char-code #\Z)))
                          (+ xc 32)
                        xc))
              (yc-fix (if (and (<= (char-code #\A) yc) (<= yc (char-code #\Z)))
                          (+ yc 32)
                        yc)))
         (< xc-fix yc-fix))
       
       :exec
       (let* ((xc     (the (unsigned-byte 8) (char-code (the character x))))
              (yc     (the (unsigned-byte 8) (char-code (the character y))))
              (xc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) xc))
                               (<= (the (unsigned-byte 8) xc) (the (unsigned-byte 8) 90)))
                          (the (unsigned-byte 8) (+ (the (unsigned-byte 8) xc) 32))
                        (the (unsigned-byte 8) xc)))
              (yc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) yc))
                               (<= (the (unsigned-byte 8) yc) (the (unsigned-byte 8) 90)))
                          (the (unsigned-byte 8) (+ (the (unsigned-byte 8) yc) 32))
                        (the (unsigned-byte 8) yc))))
         (< (the (unsigned-byte 8) xc-fix)
            (the (unsigned-byte 8) yc-fix)))))
              
(defthm ichar<-irreflexive
  (not (ichar< x x))
  :hints(("Goal" :in-theory (enable ichar<))))

(defthm ichar<-antisymmetric
  (implies (ichar< x y)
           (not (ichar< y x)))
  :hints(("Goal" :in-theory (enable ichar<))))

(defthm ichar<-transitive
  (implies (and (ichar< x y)
                (ichar< y z))
           (ichar< x z))
  :hints(("Goal" :in-theory (enable ichar<))))

(defthm ichar<-transitive-two
  (implies (and (ichar< y z)
                (ichar< x y))
           (ichar< x z))
  :hints(("Goal" :in-theory (enable ichar<))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (<= 65 (char-code x))
                        (<= (char-code x) 90)
                        (equal (char-code y) (+ 32 (char-code x))))
                   (standard-char-p y))
          :hints(("Goal"
                  :in-theory (disable standard-char-p-of-char-downcase)
                  :use ((:instance standard-char-p-of-char-downcase))))))

 (defthm ichar<-trichotomy-weak
   (implies (and (not (ichar< x y))
                 (not (ichar< y x)))
            (equal (ichareqv x y)
                   t))
   :hints(("Goal" :in-theory (enable ichar< ichareqv)))))
                          
(defcong ichareqv equal (ichar< x y) 1
  :hints(("Goal" :in-theory (enable ichar<
                                    ichareqv
                                    char-downcase-redefinition
                                    standard-char-p-of-char-downcase))))

(defcong ichareqv equal (ichar< x y) 2
  :hints(("Goal" :in-theory (enable ichar<
                                    ichareqv
                                    char-downcase-redefinition
                                    standard-char-p-of-char-downcase))))

(defthm ichar<-trichotomy-strong
  (equal (ichar< x y)
         (and (not (ichareqv x y))
              (not (ichar< y x))))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))





(defund icharlist< (x y)

  ":Doc-Section Str
  Case-insensitive character-list less-than test~/

  We determine whether one character list alphabetically preceeds another, where
  each character is tested with ~il[char<] and shorter strings are said to come 
  before longer strings. ~/
 
  ~l[ichar<] and ~pl[istr<]"

  (declare (xargs :guard (and (character-listp x)
                              (character-listp y))
                  :verify-guards nil))

  (mbe :logic (cond ((atom y)
                     nil)
                    ((atom x)
                     t)
                    ((ichar< (car x) (car y))
                     t)
                    ((ichar< (car y) (car x))
                     nil)
                    (t
                     (icharlist< (cdr x) (cdr y))))
       :exec
       (cond ((atom y)
              nil)
             ((atom x)
              t)             
             (t
              (let* ((xc     (the (unsigned-byte 8) (char-code (the character (car x)))))
                     (yc     (the (unsigned-byte 8) (char-code (the character (car y)))))
                     (xc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) xc))
                                      (<= (the (unsigned-byte 8) xc) (the (unsigned-byte 8) 90)))
                                 (the (unsigned-byte 8) (+ (the (unsigned-byte 8) xc) 32))
                               (the (unsigned-byte 8) xc)))
                     (yc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) yc))
                                      (<= (the (unsigned-byte 8) yc) (the (unsigned-byte 8) 90)))
                                 (the (unsigned-byte 8) (+ (the (unsigned-byte 8) yc) 32))
                               (the (unsigned-byte 8) yc))))
                (cond ((< (the (unsigned-byte 8) xc-fix) (the (unsigned-byte 8) yc-fix))
                       t)
                      ((< (the (unsigned-byte 8) yc-fix) (the (unsigned-byte 8) xc-fix))
                       nil)
                      (t
                       (icharlist< (cdr x) (cdr y)))))))))

(verify-guards icharlist<
               :hints(("Goal" :in-theory (e/d (ichar<)
                                              (ichar<-trichotomy-strong)))))

(defthm icharlist<-irreflexive
  (equal (icharlist< x x)
         nil)
  :hints(("Goal" :in-theory (enable icharlist<))))

(defthm icharlist<-antisymmetric
  (implies (icharlist< x y)
           (not (icharlist< y x)))
  :hints(("Goal" :in-theory (enable icharlist<))))

(defthm icharlist<-transitive
  (implies (and (icharlist< x y)
                (icharlist< y z))
           (icharlist< x z))
  :hints(("Goal" :in-theory (enable icharlist<))))

(defthm icharlist<-trichotomy-weak
   (implies (and (not (icharlist< x y))
                 (not (icharlist< y x)))
            (equal (icharlisteqv x y)
                   t))
   :hints(("Goal" :in-theory (enable icharlist<))))

(defcong icharlisteqv equal (icharlist< x y) 1
  :hints(("Goal" :in-theory (enable icharlist<))))

(defcong icharlisteqv equal (icharlist< x y) 2
  :hints(("Goal" :in-theory (enable icharlist< icharlisteqv))))

(defthm icharlist<-trichotomy-strong
  (equal (icharlist< x y)
         (and (not (icharlisteqv x y))
              (not (icharlist< y x))))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))




(defund istr<-aux (x y n xl yl)
  (declare (type string x)
           (type string y)
           (type integer n)
           (type integer xl)
           (type integer yl)
           (xargs :guard (and (stringp x)
                              (stringp y)
                              (natp n)
                              (<= n (length x))
                              (<= n (length y))
                              (equal xl (length x))
                              (equal yl (length y)))
                  :verify-guards nil
                  :measure (nfix (- (nfix xl) (nfix n)))))
  (mbe :logic
       (cond ((zp (- (nfix yl) (nfix n)))
              nil)
             ((zp (- (nfix xl) (nfix n)))
              t)
             ((ichar< (char x n) (char y n))
              t)
             ((ichar< (char y n) (char x n))
              nil)
             (t
              (istr<-aux x y (+ (nfix n) 1) xl yl)))
       :exec 
       (cond ((= (the integer n) (the integer yl))
              nil)
             ((= (the integer n) (the integer xl))
              t)
             (t 
              (let* ((xc     (the (unsigned-byte 8)
                               (char-code (the character 
                                            (char (the string x) (the integer n))))))
                     (yc     (the (unsigned-byte 8) 
                               (char-code (the character 
                                            (char (the string y) (the integer n))))))
                     (xc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) xc))
                                      (<= (the (unsigned-byte 8) xc) (the (unsigned-byte 8) 90)))
                                 (the (unsigned-byte 8) (+ (the (unsigned-byte 8) xc) 32))
                               (the (unsigned-byte 8) xc)))
                     (yc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) yc))
                                      (<= (the (unsigned-byte 8) yc) (the (unsigned-byte 8) 90)))
                                 (the (unsigned-byte 8) (+ (the (unsigned-byte 8) yc) 32))
                               (the (unsigned-byte 8) yc))))
                (cond ((< (the (unsigned-byte 8) xc-fix) (the (unsigned-byte 8) yc-fix))
                       t)
                      ((< (the (unsigned-byte 8) yc-fix) (the (unsigned-byte 8) xc-fix))
                       nil)
                      (t
                       (istr<-aux (the string x)
                                  (the string y)
                                  (the integer (+ (the integer n) 1))
                                  (the integer xl)
                                  (the integer yl)))))))))

(verify-guards istr<-aux
               :hints(("Goal" :in-theory (e/d (ichar<)
                                              (ichar<-trichotomy-strong)))))

(defthm istr<-aux-correct
  (implies (and (stringp x)
                (stringp y)
                (natp n)
                (<= n (length x))
                (<= n (length y))
                (equal xl (length x))
                (equal yl (length y)))
           (equal (istr<-aux x y n xl yl)
                  (icharlist< (nthcdr n (coerce x 'list))
                              (nthcdr n (coerce y 'list)))))
  :hints(("Goal" :in-theory (enable istr<-aux icharlist<))))



(defun istr< (x y)

  ":Doc-Section Str
  Case-insensitive string less-than test~/

  We determine whether one string alphabetically preceeds another, where each 
  character is tested with ~il[char<] and shorter strings are said to come 
  before longer strings. 

  Logically, ~c[(istr< x y)] is ~c[(icharlist< (coerce x 'list) (coerce y 'list)],
  but we use a more efficient implementation which avoids coercing the strings.~/
 
  ~l[ichar<] and ~pl[icharlist<]"

  (declare (type string x)
           (type string y))

  (mbe :logic 
       (icharlist< (coerce x 'list) (coerce y 'list))
       
       :exec 
       (istr<-aux (the string x)
                  (the string y)
                  (the integer 0)
                  (the integer (length (the string x)))
                  (the integer (length (the string y))))))


       
                   

