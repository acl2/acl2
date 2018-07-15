; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

(in-package "ACL2")

(include-book "coi/symbol-fns/symbol-fns" :dir :system)

(defun gensym::genvar2-rec (n base vars)
  (declare (type symbol base)
	   (type (integer 0 *) n)
	   (type (satisfies true-listp) vars))
  (if (zp n) nil
    (let ((symbol (symbol-fns::suffix base n)))
      (if (not (member symbol vars))
	  symbol
	(gensym::genvar2-rec (1- n) base vars)))))

(defthm symbolp-genvar2-rec
  (symbolp (gensym::genvar2-rec n base vars)))

(defthm gensym::genvar2-rec-non-member
  (implies
   (gensym::genvar2-rec n base vars)
   (not (member (gensym::genvar2-rec n base vars) vars)))
  :rule-classes (:rewrite :forward-chaining))

(defun gensym::genvar2 (base vars)
  (declare (type symbol base)
	   (type (satisfies true-listp) vars))
  (gensym::genvar2-rec (1+ (len vars)) base vars))

(defthm symbolp-genvar2
  (symbolp (gensym::genvar2 base vars)))

(defthm gensym::genvar2-non-member
  (implies
   (gensym::genvar2 base vars)
   (not (member (gensym::genvar2 base vars) vars)))
  :rule-classes (:forward-chaining))

(in-theory (disable gensym::genvar2))

(local
 (progn

(encapsulate
 ()

 (local (include-book "coi/util/ordinal-order" :dir :system))

 (local
  (encapsulate
   ()

   (defthmd equal-symbol-reduction
     (implies
      (symbolp x)
      (iff (equal x y)
	   (and (symbolp y)
		(equal (symbol-name x) (symbol-name y))
		(equal (symbol-package-name x) (symbol-package-name y)))))
     :hints (("Goal" :in-theory (e/d
				 (symboltoo)
				 (equal-symboltoo-reduction
				  equal-stringtoo-reduction
				  ))
	      :use (equal-symboltoo-reduction
		    (:instance equal-stringtoo-reduction
			       (x (symbol-name x))
			       (y (symbol-name y)))
		    (:instance equal-stringtoo-reduction
			       (x (symbol-package-name x))
			       (y (symbol-package-name y)))))))

   (defthmd equal-symbol-nil
     (equal (equal x nil)
	    (and (equal (symbol-name x) "NIL")
		 (equal (symbol-package-name x) "COMMON-LISP")))
     :hints (("Goal" :use (:instance equal-symbol-reduction
				     (x x)
				     (y nil)))))

   (defthmd iff-symbol
     (implies
      (not (equal (symbol-name x) "NIL"))
      (equal (equal x nil)
	     nil))
     :hints (("Goal" :use equal-symbol-nil)))

   (DEFTHMd not-equal-intern-in-package-of-symbol-nil
     (IMPLIES (AND (STRINGP STRING)
		   (SYMBOLP SYMBOL)
		   (NOT (EQUAL STRING "NIL")))
	      (EQUAL (EQUAL (INTERN-IN-PACKAGE-OF-SYMBOL STRING SYMBOL)
			    NIL)
		     NIL))
     :INSTRUCTIONS (:PRO (:DV 1)
			 (:REWRITE IFF-SYMBOL)
			 (:DV 1)
			 (:DV 1)
			 (:REWRITE SYMBOL-NAME-INTERN-IN-PACKAGE-OF-SYMBOL)
			 :TOP :S))

   ))

 (DEFTHMd iff-intern-in-package-of-symbol
   (IMPLIES (AND (STRINGP STRING)
		 (SYMBOLP SYMBOL)
		 (NOT (EQUAL STRING "NIL")))
	    (INTERN-IN-PACKAGE-OF-SYMBOL STRING SYMBOL))
   :hints (("Goal" :use not-equal-intern-in-package-of-symbol-nil)))

 (defthmd equal-string-coerce-reduction
   (implies
    (and
     (stringp x)
     (stringp y))
    (equal (equal x y)
	   (equal (coerce x 'list) (coerce y 'list)))))

 )


(defthm equal-coerce-nil
  (implies
   (character-listp list)
   (equal (equal (coerce list 'string) "NIL")
	  (equal list `(#\N #\I #\L))))
  :hints (("Goal" :in-theory (enable equal-string-coerce-reduction))))

(defthm character-listp-append
  (implies
   (true-listp x)
   (equal (character-listp (append x y))
	  (and (character-listp x)
	       (character-listp y)))))

(defthm append-nil
  (implies
   (true-listp x)
   (equal (append x nil) x)))

(defun contains-numerics (list)
  (if (consp list)
      (or (member (car list) '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
	  (contains-numerics (cdr list)))
    nil))

(defthm character-listp-EXPLODE-NONNEGATIVE-INTEGER
  (implies
   (character-listp list)
   (character-listp (EXPLODE-NONNEGATIVE-INTEGER n b list))))

(defthm character-listp-implies-true-listp
  (implies
   (character-listp list)
   (true-listp list)))

(defthmd CONTAINS-NUMERICS-EXPLODE-NONNEGATIVE-INTEGER
  (implies
   (not (zp n))
   (contains-numerics (EXPLODE-NONNEGATIVE-INTEGER N 10 list))))

(defthmd number-strings-contain-numerics
  (implies
   (natp n)
   (contains-numerics (coerce (symbol-fns::to-string n) 'list)))
  :hints (("Goal" :cases ((zp n))
	   :in-theory (enable CONTAINS-NUMERICS-EXPLODE-NONNEGATIVE-INTEGER
			      symbol-fns::to-string))))

(defthmd on-containing-numerics
  (implies
   (and
    (contains-numerics list1)
    (not (contains-numerics list2)))
   (not (equal list1 list2))))

(defthm contains-numerics-append
  (equal (contains-numerics (append x y))
	 (or (contains-numerics x)
	     (contains-numerics y))))

(defthm len-0-non-member
  (implies
   (equal (len vars) 0)
   (not (consp vars)))
  :rule-classes (:forward-chaining))

(defthm symbolp-safe-witness-fn
  (implies
   (symbolp base)
   (symbolp (symbol-fns::safe-witness base))))

(defthmd not-equal-symbols
  (implies
   (and
    (symbolp x)
    (symbolp y)
    (not (equal (symbol-name x)
		(symbol-name y))))
   (not (equal x y))))


(defthmd not-equal-coerce-string
  (implies
   (and
    (character-listp x)
    (character-listp y)
    (not (equal x y)))
   (not (equal (coerce x 'string)
	       (coerce y 'string))))
  :hints (("Goal" :in-theory (enable
			      equal-string-coerce-reduction
			      ))))

(defthmd not-equal-coerce-list
  (implies
   (and
    (stringp string1)
    (stringp string2)
    (not (equal string1 string2)))
   (not (equal (coerce string1 'list)
	       (coerce string2 'list))))
  :hints (("Goal" :in-theory (enable
			      equal-string-coerce-reduction
			      ))))

(defthm equal-append-common-base
  (equal (equal (append x y)
		(append x z))
	 (equal y z)))

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (local
    (include-book "arithmetic-3/bind-free/top" :dir :system))

   (local
    (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
						  HIST PSPV))))

   (local
    (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

   (defun decompose (n)
     (if (zp n) 0
       (+ (* 10 (decompose (floor n 10))) (mod n 10))))

   (defthmd decompose-natp
     (implies
      (natp n)
      (equal (decompose n) n)))

   (defthmd equal-nat-to-equal-decomposition
     (implies
      (and
       (natp n)
       (natp m))
      (equal (equal n m)
	     (equal (decompose n)
		    (decompose m))))
     :hints (("Goal" :in-theory (enable decompose-natp))))

   (in-theory (disable digit-to-char))

   (defun enni (n)
     (if (zp n) nil
       (cons (digit-to-char (mod n 10)) (enni (floor n 10)))))

   (defthmd EXPLODE-NONNEGATIVE-INTEGER-to-enni-consp
     (implies
      (consp list)
      (equal (EXPLODE-NONNEGATIVE-INTEGER N 10 LIST)
	     (revappend (enni n) list))))

   (defthmd EXPLODE-NONNEGATIVE-INTEGER-to-enni
     (equal (EXPLODE-NONNEGATIVE-INTEGER N 10 list)
	    (if (zp n) (or list (list #\0))
	      (revappend (enni n) list)))
     :hints (("Goal" :in-theory (enable EXPLODE-NONNEGATIVE-INTEGER-to-enni-consp))))


   (defun nm-induction (n m)
     (if (or (zp n) (zp m)) (list n m)
       (nm-induction (floor n 10) (floor m 10))))

   (defthm not-equal-digit-to-char
     (implies
      (and
       (< n 10)
       (< m 10)
       (natp n)
       (natp m)
       (not (equal n m)))
      (not (equal (digit-to-char n) (digit-to-char m))))
     :hints (("Goal" :in-theory (enable mod digit-to-char))))

   (defthm mod-10-bound
     (implies
      (integerp n)
      (and (< (mod n 10) 10)
	   (<= 0 (mod n 10))))
     :rule-classes (:linear)
     :hints (("Goal" :in-theory (enable mod))))

   (defthm not-equal-enni-decompose
     (implies
      (and
       (natp n)
       (natp m)
       (not (equal (decompose n)
		   (decompose m))))
      (not (equal (enni n)
		  (enni m))))
     :hints (("Goal" :induct (nm-induction n m))))

   (defthm not-equal-enni
     (implies
      (and
       (natp n)
       (natp m)
       (not (equal n m)))
      (not (equal (enni n)
		  (enni m))))
     :hints (("Goal" :use not-equal-enni-decompose
	      :in-theory `(equal-nat-to-equal-decomposition))))

   (defun revappend-x-y-induction (x y a b)
     (if (and (consp x) (consp y))
	 (revappend-x-y-induction (cdr x) (cdr y) (cons (car x) a) (cons (car y) b))
       (list x y a b)))

   (defthm len-revappend
     (equal (len (revappend x y))
	    (+ (len x) (len y))))

   (defthm inequality-by-len
     (implies
      (not (equal (len x) (len y)))
      (not (equal x y))))

   (defthm x-implies-nz-len
     (implies (and (true-listp x) x) (< 0 (len x)))
     :rule-classes (:linear))

   (defthm not-equal-revappend-x
     (implies
      (not (equal a b))
      (not (equal (revappend x a)
		  (revappend x b)))))

   (defthm not-equal-revappend
     (implies
      (and
       (true-listp x)
       (true-listp y)
       (equal (len a) (len b))
       (not (equal x y)))
      (not (equal (revappend x a)
		  (revappend y b))))
     :hints (("Goal" :induct (revappend-x-y-induction x y a b))))

   (defthm not-equal-explode-nonnegative-integer
     (implies
      (and
       (natp n)
       (natp m)
       (not (equal n m)))
      (not (equal (explode-nonnegative-integer n 10 nil)
		  (explode-nonnegative-integer m 10 nil))))
     :hints (("Goal" :in-theory (enable EXPLODE-NONNEGATIVE-INTEGER-to-enni))
	     ("Subgoal 1" :expand ((DIGIT-TO-CHAR N) (enni n) (ENNI (FLOOR N 10))))
	     ("Subgoal 2" :expand ((DIGIT-TO-CHAR M) (enni m) (ENNI (FLOOR M 10))))))

   (defthm not-equal-integer-to-string
     (implies
      (and
       (natp n)
       (natp m)
       (not (equal n m)))
      (not (equal (symbol-fns::to-string n)
		  (symbol-fns::to-string m))))
     :hints (("Goal" :in-theory (enable
				 not-equal-coerce-string
				 symbol-fns::to-string
				 ))))

   ))

 (defun new-symbol (n base)
   (INTERN-IN-PACKAGE-OF-SYMBOL
    (COERCE (APPEND (COERCE (SYMBOL-FNS::TO-STRING BASE)
			    'LIST)
		    (COERCE (SYMBOL-FNS::TO-STRING N)
			    'LIST))
	    'STRING)
    (SYMBOL-FNS::SAFE-WITNESS BASE)))

 (defthm not-equal-new-symbol
   (implies
    (and
     (natp n)
     (natp m)
     (symbolp base)
     (not (equal n m)))
    (not (equal (new-symbol n base)
		(new-symbol m base))))
   :hints (("Goal" :in-theory (enable
			       not-equal-symbols
			       not-equal-coerce-string
			       not-equal-coerce-list
			       EQUAL-APPEND-COMMON-BASE
			       NOT-EQUAL-INTEGER-TO-STRING
			       ))))

 )

(defthm iff-new-symbol
  (implies
   (and
    (natp n)
    (symbolp base))
   (new-symbol n base))
  :hints (("Goal" :in-theory (enable
			      EQUAL-STRING-COERCE-REDUCTION
			      COERCE-INVERSE-1
			      ON-CONTAINING-NUMERICS
			      NUMBER-STRINGS-CONTAIN-NUMERICS
			      IFF-INTERN-IN-PACKAGE-OF-SYMBOL
			      ))))

(in-theory (disable new-symbol))

(include-book "coi/bags/top" :dir :system)
(include-book "coi/lists/set" :dir :system)

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (defun gensym::genvar2-symbols (n base)
     (if (zp n) nil
       (let ((symbol (new-symbol n base)))
	 (cons symbol (gensym::genvar2-symbols (1- n) base)))))

   (defthm greater-n-not-memberp-genvar2-symbols
     (implies
      (and
       (symbolp base)
       (natp n)
       (natp m)
       (< m n))
      (not (list::memberp (new-symbol n base) (gensym::genvar2-symbols m base)))))

   (defthm unique-genvar2-symbols
     (implies
      (symbolp base)
      (bag::unique (gensym::genvar2-symbols n base)))
     :hints (("Goal" :in-theory (enable bag::unique))))

   (defthm len-genvar2-symbols
     (equal (len (gensym::genvar2-symbols n base)) (nfix n)))

   ;; A better definition ..
   (defun genvar3-rec (n base vars)
     (if (zp n) nil
       (let ((symbol (new-symbol n base)))
	 (if (not (list::memberp symbol vars)) symbol
	   (genvar3-rec (1- n) base vars)))))

   (defthm genvar3-rec-implies-subsetp
     (implies
      (and
       (symbolp base)
       (natp n)
       (not (list::subsetp (gensym::genvar2-symbols n base) vars)))
      (genvar3-rec n base vars))
     :hints (("Goal" :in-theory (enable list::memberp)))
     :otf-flg t)

   (defun unique-subset-bound-induction (big small)
     (if (consp big)
	 (if (list::memberp (car big) small)
	     (unique-subset-bound-induction (cdr big) (remove (car big) small))
	   (list big small))
       nil))

   (defthm len-remove
     (implies
      (list::memberp a list)
      (< (len (remove a list))
	 (len list)))
     :rule-classes (:linear))

   (defthm unique-subset-size-bound
     (implies
      (and
       (< (len small) (len big))
       (bag::unique big))
      (not (list::subsetp big small)))
     :hints (("Goal" :induct (unique-subset-bound-induction big small))))

   (defthm iff-genvar2-rec
     (implies
      (and
       (symbolp base)
       (natp n)
       (< (len vars) n))
      (genvar3-rec n base vars)))

   (defthm gensym::genvar2-rec-to-genvar3-rec
     (equal (gensym::genvar2-rec n base vars)
	    (genvar3-rec n base vars))
     :hints (("Goal" :in-theory (enable new-symbol))))

   ))

 (defthm iff-genvar2
   (implies
    (symbolp base)
    (gensym::genvar2 base vars))
   :hints (("Goal" :in-theory (enable gensym::genvar2))))

 )

(defthm non-membership-property
  (implies
   (and
    (list::subsetp list vars)
    (not (list::memberp x vars)))
   (not (list::memberp x list))))

(defthm gensym::genvar2-non-memberp-trigger
  (implies
   (symbolp base)
   (not (list::memberp (gensym::genvar2 base vars) vars)))
  :hints (("Goal" :use gensym::genvar2-non-member))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::genvar2 base vars)))))


))

(include-book "coi/lists/memberp" :dir :system)

(defun gensym::gensym (base vars)
  (declare (type (satisfies true-listp) vars))
  (let ((base (if (and base (symbolp base)) base 'gensym::gensym)))
    (if (list::memberp base vars)
	(gensym::genvar2 base vars)
      base)))

(defun non-nil-symbolp (x)
  (declare (type t x))
  (and (symbolp x)
       x))

(defthm implies-non-nil-symbolp
  (implies
   (and (symbolp x) x)
   (non-nil-symbolp x))
  :rule-classes (:rewrite :type-prescription))

(defthm non-nil-symbolp-implication
  (implies
   (non-nil-symbolp x)
   (and (symbolp x)
        x))
  :rule-classes (:forward-chaining))

(defthm gensym::non-nil-symbolp-gensym
  (non-nil-symbolp (gensym::gensym base vars))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym base vars)))))

(in-theory (disable non-nil-symbolp))

(defthm gensym::gensym-non-memberp
  (not (list::memberp (gensym::gensym base vars) vars))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym base vars)))))

(in-theory (disable gensym::gensym))
  
