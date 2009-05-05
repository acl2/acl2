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
(local (include-book "arithmetic"))

(defthm equal-of-char-code-and-char-code
  (implies (and (characterp x)
                (characterp y))
           (equal (equal (char-code x) (char-code y))
                  (equal x y)))
  :hints(("Goal" :use acl2::equal-char-code)))

(defthm equal-of-char-code-and-constant
  (implies (syntaxp (quotep c))
           (equal (equal (char-code x) c)
                  (if (characterp x)
                      (and (natp c)
                           (<= c 255)
                           (equal x (code-char c)))
                    (equal c 0)))))

(defthm code-char-when-not-natp
  (implies (not (natp x))
           (equal (code-char x)
                  (code-char 0)))
  :hints(("Goal" :use ((:instance acl2::completion-of-code-char)))))

(defthm equal-of-char-code-of-plus
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep const))
                (characterp a)
                (natp y)
                (natp const)
                (<= (+ const y) 255))
           (equal (equal a (code-char (+ const y)))
                  (equal y (- (char-code a) const)))))


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
   :rule-classes :definition))


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
                            (m m)))))))

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
                            (m (char-code x))))))))
