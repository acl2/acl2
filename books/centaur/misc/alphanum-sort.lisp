; Centaur Miscellaneous Books
; Copyright (C) 2021 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "defsort/defsort" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(local
 (defsection string-<-transitive
   (local
    (encapsulate nil
      (local (defun-sk string<-l-under-iff-prop (l1 l2)
               (forall i
                       (implies (and (syntaxp (not (equal i ''0)))
                                     i)
                                (iff (string<-l l1 l2 i)
                                     (string<-l l1 l2 0))))
               :rewrite :direct))
      (local (in-theory (disable string<-l-under-iff-prop)))
      (local (defthm string<-l-under-iff-lemma
               (string<-l-under-iff-prop l1 l2)
               :hints(("Goal" :induct (string<-l l1 l2 i)
                       :in-theory (enable string<-l))
                      (and stable-under-simplificationp
                           `(:expand (,(car (last clause))))))))
      (defthm string<-l-under-iff
        (implies (and (syntaxp (not (equal i ''0)))
                      i)
                 (iff (string<-l l1 l2 i)
                      (string<-l l1 l2 0))))))

   (defthm string<-l-transitive-strong
     (implies (and (string<-l x y 0)
                   (string<-l y z 0))
              (string<-l x z 0))
     :hints(("Goal" :in-theory (enable string<-l))))

   (defthm string<-l-negation-transitive
     (implies (and (not (string<-l x y 0))
                   (not (string<-l y z 0))
                   (character-listp x)
                   (character-listp z)
                   (character-listp y))
              (not (string<-l x z 0)))
     :hints(("Goal" :in-theory (enable string<-l chareqv))))

   ;; (defthm string<-l-transitive-variant1
   ;;   (implies (and (not (string<-l y x 0))
   ;;                 (string<-l y z 0)
   ;;                 (character-listp x)
   ;;                 (character-listp z)
   ;;                 (character-listp y))
   ;;            (string<-l x z 0))
   ;;   :hints(("Goal" :in-theory (enable string<-l character-listp chareqv))))

   ;; (defthm string<-l-transitive-variant2
   ;;   (implies (and (string<-l x y 0)
   ;;                 (not (string<-l z y 0))
   ;;                 (character-listp x)
   ;;                 (character-listp z)
   ;;                 (character-listp y))
   ;;            (string<-l x z 0))
   ;;   :hints(("Goal" :in-theory (enable string<-l character-listp chareqv))))

   (defthm string<-transitive
     (implies (and (string< x y)
                   (string< y z))
              (string< x z))
     :hints(("Goal" :in-theory (enable string<))))

   (defthm string<-negation-transitive
     (implies (and (not (string< x y))
                   (not (string< y z)))
              (not (string< x z)))
     :hints(("Goal" :in-theory (enable string<))))

   (defthmd string<-trichotomy
     (implies (and (not (string< x y))
                   (stringp x)
                   (stringp y))
              (iff (string< y x)
                   (not (equal x y))))
     :hints(("Goal" :in-theory (enable string<))))))


(local
 (defsection alphanum-sort-theory
   (defthm take-of-equal-len
     (implies (equal (nfix n) (len x))
              (equal (take n x) (true-list-fix x))))

   
   (defthmd equal-cons-strong
     (equal (equal (cons a b) c)
            (and (consp c)
                 (equal (car c) a)
                 (equal (cdr c) b))))

   (defthmd nthcdr-too-large-strong
     (implies (and (true-listp x)
                   (<= (len x) (nfix n)))
              (not (nthcdr n x))))
   

   (defthm len-equal-0
     (equal (equal (len x) 0)
            (atom x)))

   (defthm dec-digit-chars-value-bound
     (< (str::dec-digit-chars-value x) (expt 10 (len x)))
     :hints(("Goal" :in-theory (enable str::dec-digit-chars-value expt)))
     :rule-classes :linear)

   (defthm expt-posp
     (implies (and (posp b) (natp i))
              (posp (expt b i)))
     :rule-classes :type-prescription)

   (defun equal-sum-same-ind (y1 y2)
     (if (zp y1)
         y2
       (equal-sum-same-ind (- y1 1) (- y2 1))))

   (defthm equal-sum-same
     (implies (and (natp x1) (natp x2)
                   (natp y1) (natp y2)
                   (posp e)
                   (< x1 e) (< x2 e))
              (equal (equal (+ x1 (* y1 e))
                            (+ x2 (* y2 e)))
                     (and (equal x1 x2)
                          (equal y1 y2))))
     :hints (("goal" :induct (equal-sum-same-ind y1 y2))
             (and stable-under-simplificationp
                  '(:cases ((equal y2 0))))
             (and stable-under-simplificationp
                  '(:nonlinearp t))))

   (defun ind (x y)
     (if (atom x)
         y
       (ind (cdr x) (cdr y))))

   (defthm equal-of-dec-digit-chars-value
     (implies (and (str::dec-digit-char-listp x)
                   (str::dec-digit-char-listp y)
                   (equal (len x) (len y)))
              (equal (equal (str::dec-digit-chars-value x) (str::dec-digit-chars-value y))
                     (equal (true-list-fix x) (true-list-fix y))))
     :hints (("goal" :induct (ind x y)
              :in-theory (enable str::dec-digit-chars-value
                                 str::dec-digit-char-listp
                                 true-list-fix))
             (and stable-under-simplificationp
                  '(:cases ((consp (cdr x)))))))

   (defthm character-listp-of-nthcdr
     (implies (character-listp x)
              (character-listp (nthcdr n x)))
     :hints(("Goal" :in-theory (enable nthcdr))))

   (defthm character-listp-of-take
     (implies (and (character-listp x)
                   (<= (nfix n) (len x)))
              (character-listp (take n x)))
     :hints(("Goal" :in-theory (enable nthcdr))))

   (defthm equal-of-implode
     (implies (and (character-listp x)
                   (character-listp y))
              (equal (equal (implode x) (implode y))
                     (equal x y))))

   (defun not-equal-take-ind (n m x y)
     (if (or (zp n) (zp m))
         (list x y)
       (not-equal-take-ind (1- n) (1- m) (cdr x) (cdr y))))

   (defthm not-equal-take-when-not-equal
     (implies (and (not (equal x y))
                   (equal (nthcdr n x) (nthcdr m y))
                   (<= (nfix n) (len x))
                   (<= (nfix m) (len y)))
              (not (equal (take n x) (take m y))))
     :hints (("goal" :induct (not-equal-take-ind n m x y))))))



(local (in-theory (disable char)))

(local (defthm characterp-nth-character-list
         (implies (and (< (nfix n) (len x))
                       (character-listp x))
                  (characterp (nth n x)))))

(local (defthm characterp-char
         (implies (and (< (nfix n) (length x))
                       (stringp x))
                  (characterp (char x n)))
         :hints(("Goal" :in-theory (enable char)))))

(define numericp ((x characterp))
  (b* ((ch (char-code x)))
    (and (<= (char-code #\0) ch)
         (<= ch (char-code #\9))))
  ///
  (defthm numericp-redef
    (equal (numericp x)
           (str::dec-digit-char-p x))
    :hints(("Goal" :in-theory (enable str::dec-digit-char-p)))))

(fty::deffixcong acl2::nat-equiv equal (char x i) i
  :hints(("Goal" :in-theory (enable char))))

(local (defthm char-when-gte-length
         (implies (<= (length x) (nfix n))
                  (equal (char x n) nil))
         :hints(("Goal" :in-theory (enable char length)))))

(local (in-theory (disable (tau-system))))

(define count-non-numeric ((x character-listp))
  :returns (count natp :rule-classes :type-prescription)
  (cond ((atom x) 0)
        ((numericp (car x)) 0)
        (t (+ 1 (count-non-numeric (cdr x)))))
  ///
  (defret <fn>-equal-0
    (implies (consp x)
             (equal (equal 0 count)
                    (str::dec-digit-char-p (car x)))))

  (defret <fn>-when-atom
    (implies (atom x)
             (equal count 0)))

  (defret <fn>-bound
    (<= count (len x))
    :rule-classes :linear))
    


(define scan-for-numeric ((i natp)
                          (xl (equal xl (length x)))
                          (x stringp))
  :guard (<= i xl)
  :measure (nfix (- (length x) (nfix i)))
  :returns (nexti maybe-natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (length x) (nfix i)))
                   :exec (eql i xl)))
        nil)
       ((when (numericp (char x i)))
        (lnfix i)))
    (scan-for-numeric (1+ (lnfix i)) xl x))
  ///
  (defret <fn>-bound
    (implies nexti
             (<= (nfix i) nexti))
    :rule-classes :linear)

  (defret <fn>-bound-strong
    (implies (and nexti
                  (not (str::dec-digit-char-p (char x i))))
             (< (nfix i) nexti))
    :rule-classes :linear)

  (defret <fn>-upper-bound
    (implies nexti
             (< nexti (length x)))
    :rule-classes :linear)

  (defret <fn>-correct
    (implies nexti
             (and (str::dec-digit-char-p (char x nexti))
                  (implies (and (< (nfix n) nexti)
                                (<= (nfix i) (nfix n)))
                           (not (str::dec-digit-char-p (char x n))))))
    :hints (("goal" :induct <call>
             :in-theory (enable* arith-equiv-forwarding))))

  (defret <fn>-none
    (implies (and (not nexti)
                  (<= (nfix i) (nfix n)))
             (not (str::dec-digit-char-p (char x n))))
    :hints (("goal" :in-theory (enable* arith-equiv-forwarding))))

  (std::defretd <fn>-in-terms-of-count-non-numeric
    (implies (stringp x)
             (equal nexti
                    (let ((nonnum-count (count-non-numeric (nthcdr i (explode x)))))
                      (and (< nonnum-count (- (length x) (nfix i)))
                           (+ (nfix i) nonnum-count)))))
    :hints(("Goal" 
            :induct <call>
            :in-theory (enable char)
            :expand ((count-non-numeric (nthcdr i (explode x)))))))

  (defret <fn>-under-iff
    (implies (stringp x)
             (iff nexti
                  (< (count-non-numeric (nthcdr i (explode x))) (- (length x) (nfix i)))))
    :hints(("Goal" :in-theory (enable <fn>-in-terms-of-count-non-numeric))))

  (defret <fn>-when-value
    (implies (and (stringp x)
                  (< (count-non-numeric (nthcdr i (explode x))) (- (length x) (nfix i))))
             (equal nexti
                  (+ (nfix i) (count-non-numeric (nthcdr i (explode x))))))
    :hints(("Goal" :in-theory (enable <fn>-in-terms-of-count-non-numeric)))))

(define count-numeric ((x character-listp))
  :returns (count natp :rule-classes :type-prescription)
  (cond ((atom x) 0)
        ((numericp (car x)) (+ 1 (count-numeric (cdr x))))
        (t 0))
  ///
  (defthm take-leading-dec-digit-chars-in-terms-of-count-numeric
    (equal (str::take-leading-dec-digit-chars x)
           (take (count-numeric x) x))
    :hints(("Goal" :in-theory (enable str::take-leading-dec-digit-chars))))

  (defret <fn>-when-dec-digit-char-listp
    (implies (str::dec-digit-char-listp x)
             (equal count (len x))))

  (defret <fn>-equal-0
    (implies (consp x)
             (equal (equal 0 count)
                    (not (str::dec-digit-char-p (car x))))))

  (defret <fn>-when-atom
    (implies (atom x)
             (equal count 0)))

  (defret <fn>-bound
    (<= count (len x))
    :rule-classes :linear)

  (defret <fn>-bound-strong
    (implies (not (str::dec-digit-char-listp x))
             (< count (len x)))
    :rule-classes :linear)

  (defret dec-digit-char-listp-take-of-<fn>
    (str::dec-digit-char-listp (take count x))))

(define scan-for-nonnumeric ((i natp)
                          (xl (equal xl (length x)))
                          (x stringp))
  :guard (<= i xl)
  :measure (nfix (- (length x) (nfix i)))
  :returns (nexti maybe-natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (length x) (nfix i)))
                   :exec (eql i xl)))
        nil)
       ((when (numericp (char x i)))
        (scan-for-nonnumeric (1+ (lnfix i)) xl x)))
    (lnfix i))
  ///
  (defret <fn>-bound
    (implies nexti
             (<= (nfix i) nexti))
    :rule-classes :linear)

  (defret <fn>-bound-strong
    (implies (and nexti
                  (str::dec-digit-char-p (char x i)))
             (< (nfix i) nexti))
    :rule-classes :linear)

  (defret <fn>-upper-bound
    (implies nexti
             (< nexti (length x)))
    :rule-classes :linear)

  (defret <fn>-correct
    (implies nexti
             (and (not (str::dec-digit-char-p (char x nexti)))
                  (implies (and (< (nfix n) nexti)
                                (<= (nfix i) (nfix n)))
                           (str::dec-digit-char-p (char x n)))))
    :hints (("goal" :induct <call>
             :in-theory (enable* arith-equiv-forwarding))))

  (defret <fn>-none
    (implies (and (not nexti)
                  (<= (nfix i) (nfix n))
                  (< (nfix n) (length x)))
             (str::dec-digit-char-p (char x n)))
    :hints (("goal" :in-theory (enable* arith-equiv-forwarding))))

  (defthm scan-for-nonnumeric-under-iff
    (implies (stringp x)
             (iff (scan-for-nonnumeric xi xl x)
                  (not (str::dec-digit-char-listp (nthcdr xi (explode x))))))
    :hints(("Goal" :in-theory (enable scan-for-nonnumeric
                                      str::dec-digit-char-listp
                                      char))))

  (defthm acl2-numberp-of-scan-for-nonnumeric
           (implies (stringp y)
                    (iff (acl2-numberp (scan-for-nonnumeric yi xl y))
                         (not (str::dec-digit-char-listp (nthcdr yi (explode y))))))
           :hints (("Goal" :use ((:instance scan-for-nonnumeric-under-iff
                                  (x y) (xi yi)))
                    :in-theory (disable scan-for-nonnumeric-under-iff)
                    :do-not-induct t)))

   (defthmd take-leading-dec-digit-chars-in-terms-of-scan-for-nonnumeric
     (equal (str::take-leading-dec-digit-chars (nthcdr xi (explode x)))
            (let ((idx (scan-for-nonnumeric xi xl x)))
              (if idx
                  (take (- idx (nfix xi)) (nthcdr xi (explode x)))
                (nthcdr xi (explode x)))))
     :hints(("Goal" :in-theory (enable str::take-leading-dec-digit-chars
                                       scan-for-nonnumeric
                                       char)
             :induct (scan-for-nonnumeric xi xl x)
             :expand ((str::take-leading-dec-digit-chars (nthcdr xi (explode x)))
                      (count-numeric (nthcdr xi (explode x)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable equal-cons-strong
                                      nthcdr-too-large-strong)))))

   (std::defretd <fn>-in-terms-of-count-numeric
     (implies (stringp x)
              (equal nexti
                     (let ((num-count (count-numeric (nthcdr i (explode x)))))
                       (and (< num-count (- (length x) (nfix i)))
                            (+ (nfix i) num-count)))))
     :hints(("Goal" :induct <call>
             :expand ((count-numeric (nthcdr i (explode x))))
             :in-theory (enable char))))

   (defret <fn>-in-terms-of-count-numeric-when-value
     (implies (and (stringp x)
                   (not (str::dec-digit-char-listp (nthcdr i (explode x)))))
              (equal nexti
                     (let ((num-count (count-numeric (nthcdr i (explode x)))))
                       (+ (nfix i) num-count))))
     :hints(("Goal" :use <fn>-in-terms-of-count-numeric
             :do-not-induct t))
    :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))))

(defthm char-of-nfix
  (equal (char x (nfix n))
         (char x n))
  :hints(("Goal" :in-theory (enable char))))


(define alphanum-<-aux ((xi natp) (x stringp)
                        (yi natp) (y stringp))
  :guard (and (<= xi (length x))
              (<= yi (length y)))
  :measure (max (nfix (- (length x) (nfix xi))) (nfix (- (length y) (nfix yi))))
  :guard-debug t
  :hints (("goal" ;:in-theory (disable scan-for-nonnumeric-under-iff)
           :in-theory (enable char)
           :do-not-induct t))
  :prepwork ((local (in-theory (disable STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP
                                        count-non-numeric-when-atom
                                        count-numeric-when-atom
                                        scan-for-numeric-when-value
                                        scan-for-nonnumeric-in-terms-of-count-numeric-when-value
                                        scan-for-numeric-under-iff
                                        scan-for-nonnumeric-under-iff
                                        take-of-equal-len))))
  (b* (;; base case return (x is "shorter than" y)
       ((when (<= (length x) (lnfix xi))) (not (<= (length y) (lnfix yi))))
       ((when (<= (length y) (lnfix yi))) nil)
       (xnump (numericp (char x (lnfix xi))))
       (ynump (numericp (char y (lnfix yi))))
       ((when xnump)
        (b* (((unless ynump) t)
             (xinext (scan-for-nonnumeric xi (length x) x))
             (yinext (scan-for-nonnumeric yi (length y) y))
             ((mv xnumpart ?xnumlen) (str::parse-nat-from-string
                                      x 0 0 xi (length x)))
             ((mv ynumpart ?ynumlen) (str::parse-nat-from-string
                                      y 0 0 yi (length y)))
             ((when (< xnumpart ynumpart)) t)
             ((when (< ynumpart xnumpart)) nil)
             ((when (< xnumlen ynumlen)) t)
             ((when (< ynumlen xnumlen)) nil)
             ((when (and xinext yinext))
              (alphanum-<-aux xinext x yinext y))
             ((when yinext) t)) ;; x is "shorter than" y
          nil))
       ((when ynump) nil)
       (xinext (scan-for-numeric xi (length x) x))
       (yinext (scan-for-numeric yi (length y) y))
       (xnonnumpart (subseq x (lnfix xi) xinext))
       (ynonnumpart (subseq y (lnfix yi) yinext))
       ((when (string< xnonnumpart ynonnumpart)) t)
       ((when (string< ynonnumpart xnonnumpart)) nil)
       ((when (and xinext yinext))
        (alphanum-<-aux xinext x yinext y))
       ((when yinext) t)) ;; x is "shorter than" y
    nil)
  ///
  (local (in-theory (disable subseq nth not len default-cdr (:d alphanum-<-aux)
                             nthcdr expt take)))
  (defthm alphanum-<-aux-transitive
    (implies (and (alphanum-<-aux xi x yi y)
                  (alphanum-<-aux yi y zi z)
                  (stringp x)
                  (stringp y)
                  (stringp z))
             (alphanum-<-aux xi x zi z))
    :hints (("goal" :induct t
             :in-theory (disable (:d alphanum-<-aux))
             :expand ((alphanum-<-aux xi x yi y)
                  (alphanum-<-aux yi y zi z)
                  (alphanum-<-aux xi x zi z)))))

  (defthm alphanum-<-aux-negation-transitive
    (implies (and (not (alphanum-<-aux xi x yi y))
                  (not (alphanum-<-aux yi y zi z))
                  (stringp x)
                  (stringp y)
                  (stringp z))
             (not (alphanum-<-aux xi x zi z)))
    :hints (("goal" :induct t
             :in-theory (disable (:d alphanum-<-aux))
             :expand ((alphanum-<-aux xi x yi y)
                  (alphanum-<-aux yi y zi z)
                  (alphanum-<-aux xi x zi z)))))

  (local (in-theory (enable subseq)))

  (local (defthmd not-equal-of-nthcdr-by-len
           (implies (not (equal (nfix (- (len x) (nfix xi)))
                                (nfix (- (len y) (nfix yi)))))
                    (not (equal (nthcdr xi x) (nthcdr yi y))))
           :hints (("goal" :use ((:instance len-of-nthcdr (n xi) (l x))
                                 (:instance len-of-nthcdr (n yi) (l y)))
                    :in-theory (disable len-of-nthcdr)))))

  ;; (local (defthmd not-equal-of-nthcdr-by-nth
  ;;          (implies (not (equal (nth xi x) (nth yi y)))
  ;;                   (not (equal (nthcdr xi x) (nthcdr yi y))))
  ;;          :hints (("goal" :use ((:instance car-of-nthcdr (i xi) (x x))
  ;;                                (:instance car-of-nthcdr (i yi) (x y)))
  ;;                   :in-theory (disable car-of-nthcdr)))))

  ;; (local (defthmd nth-equal-by-nthcdr
  ;;          (implies (not (equal (nth xi x) (nth yi y)))
  ;;                   (not (equal (nthcdr xi x) (nthcdr yi y))))
  ;;          :hints (("goal" :use ((:instance car-of-nthcdr (i xi) (x x))
  ;;                                (:instance car-of-nthcdr (i yi) (x y)))
  ;;                   :in-theory (disable car-of-nthcdr)))))

  (local (defthm nthcdr-of-plus-equal
           (implies (and (equal (nthcdr xi x) (nthcdr yi y))
                         (natp xi) (natp yi) (natp c))
                    (equal (equal (nthcdr (+ xi c) x) (nthcdr (+ yi c) y))
                           t))
           :hints (("goal" :use ((:instance nthcdr-of-nthcdr (a c) (b xi) (x x))
                                 (:instance nthcdr-of-nthcdr (a c) (b yi) (x y)))
                    :in-theory (disable nthcdr-of-nthcdr)))))

  (local (defthmd nth-car-of-nthcdr
           (equal (nth n x)
                  (car (nthcdr n x)))))

  (defthm alphanum-<-aux-strict
    (implies (and (equal (subseq x xi nil)
                         (subseq y yi nil))
                  (stringp x) (stringp y)
                  (natp xi) (natp yi))
             (not (alphanum-<-aux xi x yi y)))
    :hints (("goal" :induct (alphanum-<-aux xi x yi y)
             :expand ((alphanum-<-aux xi x yi y))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (take-leading-dec-digit-chars-in-terms-of-scan-for-nonnumeric
                                      string<-trichotomy
                                      nthcdr-too-large-strong
                                      not-equal-of-nthcdr-by-len
                                      nth-car-of-nthcdr
                                      char
                                      take-of-equal-len
                                      scan-for-numeric-when-value
                                        scan-for-nonnumeric-in-terms-of-count-numeric-when-value
                                        scan-for-numeric-under-iff
                                        scan-for-nonnumeric-under-iff)
                                   (car-of-nthcdr))))))

  (local (defthm len-of-take
           (equal (len (take n x)) (nfix n))
           :hints(("Goal" :in-theory (enable take len)))))

  (local (defthm dec-digit-char-listp-take-when-equal-count-numeric
           (implies (equal n (count-numeric x))
                    (str::dec-digit-char-listp (take n x)))))

  (defthm alphanum-<-aux-trichotomy
    (implies (and (not (alphanum-<-aux xi x yi y))
                  (natp xi) (natp yi)
                  (stringp x) (stringp y))
             (iff (alphanum-<-aux yi y xi x)
                  (not (equal (subseq x xi nil)
                              (subseq y yi nil)))))
    :hints (("goal" :induct t :do-not-induct t
             :expand ((alphanum-<-aux yi y xi x)
                      (alphanum-<-aux xi x yi y)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (take-leading-dec-digit-chars-in-terms-of-scan-for-nonnumeric
                                      string<-trichotomy
                                      nthcdr-too-large-strong
                                      ; not-equal-of-nthcdr-by-len
                                      nth-car-of-nthcdr
                                      char
                                      take-of-equal-len
                                      scan-for-numeric-when-value
                                        scan-for-nonnumeric-in-terms-of-count-numeric-when-value
                                        scan-for-numeric-under-iff
                                        scan-for-nonnumeric-under-iff)
                                   (car-of-nthcdr))
                   :use ((:instance not-equal-of-nthcdr-by-len
                          (x (explode x)) (y (explode y))))))))


  (local (in-theory (disable subseq)))


  (defthmd alphanum-<-aux-asymmetric
    (implies (and (alphanum-<-aux xi x yi y)
                  (stringp x) (stringp y)
                  (natp xi) (natp yi))
             (not (alphanum-<-aux yi y xi x)))
    :hints(("Goal" :in-theory (disable alphanum-<-aux
                                       alphanum-<-aux-transitive)
            :use ((:instance alphanum-<-aux-transitive
                   (zi xi) (z x)))))))

(define alphanum-< ((x stringp) (y stringp))
  :parents (alphanum-sort)
  :short "Compares two strings alphanumerically."
  :long " <p>This is the string comparison function used for @(see
alphanum-sort). Additionally, @(see alphanum-obj-<) extends this comparison to
arbitrary objects.</p>

<p>To compare two strings alphanumerically, we divide them into alternating
numeric (decimal) and non-numeric pieces.  The first pair of pieces that are
not equal determine which string is lesser (earlier in sorted order). The pieces
are compared according to the following rules:</p>
<ul>
<li>A numeric substring is always less than a non-numeric substring.</li>
<li>Non-numeric substrings are compared using @(see string<).</li>
<li>If two numeric substrings have different decimal values, the lesser valued
one is the lesser of the two.</li>
<li>If two numeric substrings have equal decimal values but different
lengths (due to leading zeros), the shorter one is the lesser of the two.</li>
</ul>
"
  (alphanum-<-aux 0 x 0 y))

(define alphanum-obj-< (x y)
  :parents (alphanum-sort)
  :short "Compares two objects using alphanumeric comparison on component strings and symbols."
  :long "
<p>This is the comparison function used for @(see alphanum-sort).  It orders objects as follows:</p>
<ul>
<li>Strings (alphanumerically sorted using @(see alphanum-<))</li>
<li>Symbols (alphanumerically sorted using @(see alphanum-<), first on the package name and then on the symbol name)</li>
<li>Other atoms (sorted using @(see alphorder))</li>
<li>Conses, recursively sorted using this function first on car, then cdr.</li>
</ul>
"
  (cond ((atom x)
         (if (atom y)
             (cond ((stringp x)
                    (if (stringp y)
                        (alphanum-< x y)
                      t))
                   ((stringp y) nil)
                   ((symbolp x)
                    (if (symbolp y)
                        (cond ((equal (symbol-package-name x)
                                      (symbol-package-name y))
                               (alphanum-< (symbol-name x) (symbol-name y)))
                              (t (alphanum-< (symbol-package-name x) (symbol-package-name y))))
                      t))
                   ((symbolp y) nil)
                   ((equal x y) nil)
                   (t (alphorder x y)))
           t))
        ((atom y) nil)
        ((alphanum-obj-< (car x) (car y)) t)
        ((equal (car x) (car y)) (alphanum-obj-< (cdr x) (cdr y)))
        (t nil))
  ///
  (defthm alphanum-obj-<-transitive
    (implies (and (alphanum-obj-< x y)
                  (alphanum-obj-< y z))
             (alphanum-obj-< x z))
    :hints(("Goal" :in-theory (enable alphanum-< alphanum-<-aux-trichotomy
                                      alphanum-<-aux-asymmetric))))

  (local (defthm equal-symbol-package-name
           (implies (and (equal (Symbol-name x) (symbol-name y))
                         (symbolp x) (symbolp y))
                    (iff (equal (symbol-package-name x) (symbol-package-name y))
                         (equal x y)))
           :hints (("goal" :use ((:instance intern-in-package-of-symbol-symbol-name)
                                 (:instance intern-in-package-of-symbol-symbol-name (x y)))
                    :in-theory (disable intern-in-package-of-symbol-symbol-name)))))

  (defthmd alphanum-obj-<-trichotomy
    (implies (and (not (alphanum-obj-< x y))
                  (not (equal x y)))
             (alphanum-obj-< y x))
    :hints(("Goal" :in-theory (enable alphanum-<))))

  (local (in-theory (enable alphanum-obj-<-trichotomy)))

  (defthm alphanum-obj-<-negation-transitive
    (implies (and (not (alphanum-obj-< x y))
                  (not (alphanum-obj-< y z)))
             (not (alphanum-obj-< x z)))
    :hints(("Goal" :in-theory (enable alphanum-<))))

  (defthm alphanum-obj-<-strict
    (not (alphanum-obj-< x x))
    :hints(("Goal" :in-theory (enable alphanum-<)))))

(acl2::defsort alphanum-sort
  :prefix alpha
  :compare< alphanum-obj-<
  ;; :comparablep (lambda (x) t)
  ;; :comparable-listp true-listp
  :true-listp t)

(defxdoc alphanum-sort
  :parents (defsort)
  :short "Sorts lists using alphanumeric comparison."
  :long "<p>@('(alphanum-sort x)') sorts list @('x') using the @(see
alphanum-obj-<) comparison function, which orders strings and symbols according
to alphanumeric comparison.</p>")

(local
 (defconst *test-list*
  '("abc10def1"
    "abc10def0"
    "abc8def1"
    "abc8def0"
    "abc08def1"
    "abc08def0"
    "ab10def1"
    "ab10def0"
    "ab8def1"
    "ab8def0"
    "ab08def1"
    "ab08def0"
    "abc10de1"
    "abc10de0"
    "abc8de1"
    "abc8de0"
    "abc08de1"
    "abc08de0"
    "ab10de1"
    "ab10de0"
    "ab8de1"
    "ab8de0"
    "ab08de1"
    "ab08de0")))

(local
 (define shuffle-list ((x true-listp)
                       (len (equal len (len x)))
                       state)
   :measure (len x)
   :hints(("Goal" :in-theory (enable random$)))
   :guard-hints (("goal" :in-theory (enable random$)))
   :prepwork ((local (defthm len-of-take
                       (equal (len (take n x)) (nfix n))))
              (local (in-theory (disable nthcdr-of-cdr))))
   (b* ((len (mbe :logic (len x) :exec len))
        ((when (atom x)) (mv nil state))
        ((mv idx state) (random$ len state))
        (next (nth idx x))
        (new-x (append (take idx x)
                       (nthcdr (+ 1 idx) x)))
        ((mv rest state) (shuffle-list new-x (1- len) state)))
     (mv (cons next rest) state))))

(assert-event 
 (b* (((mv lst state) (shuffle-list *test-list* (len *test-list*) state)))
   (mv 
    (equal (alphanum-sort lst)
           '("ab8de0" "ab8de1" "ab8def0" "ab8def1"
             "ab08de0" "ab08de1"
             "ab08def0" "ab08def1"
             "ab10de0" "ab10de1"
             "ab10def0" "ab10def1"
             "abc8de0" "abc8de1"
             "abc8def0" "abc8def1"
             "abc08de0" "abc08de1"
             "abc08def0" "abc08def1"
             "abc10de0" "abc10de1"
             "abc10def0" "abc10def1"))
    state))
 :stobjs-out '(nil state))
