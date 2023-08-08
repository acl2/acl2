; Copyright (C) 2023, ForrestHunt, Inc.
; Written by J Moore, June, 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This work owes a debt to books/projects/paco/ where I implemented a
; simplified version of ACL2 in :logic mode.  Many of the definitions in Paco
; were taken from the source code in the then-current ACL2, Version 2.7
; (November, 2002).  Termination was proved.  So Paco offered a guide to some
; of the functions below, most notably, the termination of one-way-unify1.  The
; Paco project did not verify guards.

(in-package "ACL2")

(encapsulate nil
  (local (include-book "arithmetic/top" :dir :system))

  (local
   (defthm x-*-conjugate-x-lemma

; The hyp on xi just means xi = #c(0 1) = i.  We use ``xi'' instead of ``i''
; for this variable so that it is associated down to the end where (* xi xi)
; becomes -1.

     (implies (and (rationalp r)
                   (rationalp s)
                   (equal (* xi xi) -1))
              (equal (+ (* r r)
                        (* r xi s)
                        (* r xi (- s))
                        (* xi s xi (- s)))
                     (+ (* r r) (* s s))))))

  (defthm x-*-conjugate-x
    (implies (acl2-numberp x)
             (equal (* x (conjugate x))
                    (+ (* (realpart x) (realpart x))
                       (* (imagpart x) (imagpart x)))))
    :hints (("Goal" :in-theory (enable complex-definition)))))

(verify-termination one-way-unify1-quotep-subproblems
  (declare (xargs :guard-hints (("Goal" :in-theory (disable conjugate))))))

(defthm pseudo-termp-mv-nth-0-one-way-unify1-quotep-subproblems
  (implies (and (pseudo-termp pat)
                (nvariablep pat)
                (not (fquotep pat))
                (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term))
                (not (eq (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)) t)))
           (pseudo-termp (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)))))

(defthm acl2-count-mv-nth-0-one-way-unify1-quotep-subproblems
  (implies (and (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term))
                (not (eq (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)) t)))
           (< (acl2-count (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)))
              (acl2-count pat)))
  :rule-classes :linear)

(defthm pseudo-termp-mv-nth-1-one-way-unify1-quotep-subproblems
  (pseudo-termp (mv-nth 1 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term))))

(defthm quotep-mv-nth-1-one-way-unify1-quotep-subproblems
  (implies (and (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term))
                (not (eq (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)) t)))
           (quotep (mv-nth 1 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)))))

(defthm pseudo-termp-mv-nth-2-one-way-unify1-quotep-subproblems
  (implies (and (pseudo-termp pat)
                (nvariablep pat)
                (not (fquotep pat))
                (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term))
                (not (eq (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)) t)))
           (pseudo-termp (mv-nth 2 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)))))

(defthm acl2-count-mv-nth-2-one-way-unify1-quotep-subproblems
  (implies (and (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term))
                (not (eq (mv-nth 0 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)) t)))
           (< (acl2-count (mv-nth 2 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)))
              (acl2-count pat)))
  :rule-classes :linear)

(defthm pseudo-termp-mv-nth-3-one-way-unify1-quotep-subproblems
  (implies (pseudo-termp term)
           (pseudo-termp (mv-nth 3 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)))))

(defthm quotep-mv-nth-3-one-way-unify1-quotep-subproblems
  (implies (and (mv-nth 2 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term))
                (quotep term))
           (quotep (mv-nth 3 (ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS pat term)))))

(in-theory (disable one-way-unify1-quotep-subproblems
                    mv-nth))

; The following is one-way-unify1 except I added :measures, turned off guard
; verification for this step, and replaced (null pl) by (endp pl) in
; vtg-one-way-unify1-lst.  The measure used below is the same one used in
; books/projects/paco/foundations.lisp.

(verify-termination one-way-unify1)

(include-book "tools/flag" :dir :system)

(make-flag flag-one-way-unify1 one-way-unify1)

(defthm-flag-one-way-unify1
  (defthm alistp-mv-nth-1-one-way-unify1
    (implies (alistp alist)
             (alistp (mv-nth 1 (one-way-unify1 pat term alist))))
    :flag one-way-unify1)
  (defthm alistp-mv-nth-1-one-way-unify1-lst
    (implies (alistp alist)
             (alistp (mv-nth 1 (one-way-unify1-lst pl tl alist))))
    :flag one-way-unify1-lst)
  (defthm alistp-mv-nth-1-one-way-unify1-equal1
    (implies (alistp alist)
             (alistp (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist))))
    :flag one-way-unify1-equal1)
  (defthm alistp-mv-nth-1-one-way-unify1-equal
    (implies (alistp alist)
             (alistp (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist))))
    :flag one-way-unify1-equal)
  )

(verify-guards one-way-unify1)

;;-----------------------------------------------------------------
;; (defun one-way-unify (pat term)
;;   (declare (xargs :guard (and (pseudo-termp pat)
;;                               (pseudo-termp term))))

;; ; This function returns two values.  The first is T or NIL, according to
;; ; whether unification succeeded.  The second value returned is a symbol alist
;; ; that when substituted into pat will produce term, when the unification
;; ; succeeded.

;; ; The use of the phrase ``unify'' here is somewhat opaque but is
;; ; historically justified by its usage in nqthm.  Really, all we are
;; ; doing is matching because we do not treat the ``variable symbols''
;; ; in term as instantiable.

;; ; Note that the fact that this function returns nil should not be
;; ; taken as a sign that no substitution makes pat equal to term in the
;; ; current theory.  For example, we fail to unify (+ x x) with '2 even
;; ; though '((x . 1)) does the job.

;;   (one-way-unify1 pat term nil))

(verify-termination one-way-unify)

(verify-termination alistp-listp)

(verify-termination one-way-unify-restrictions1)

(verify-termination one-way-unify-restrictions)

(local (include-book "ihs/ihs-lemmas" :dir :system))

(defthm justify-integer-floor-recursion

; To use this, be sure to disable acl2-count and floor.  If you
; leave acl2-count enabled, then prove a version of this
; appropriate to that setting.

  (implies
   (and (integerp i)
        (integerp j)
        (not (equal i 0))
        (not (equal i -1))
        (> j 1))
   (< (acl2-count (floor i j)) (acl2-count i)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable floor))))

(defun enni (n) ; = Explode Non-Negative Integer
  (declare (xargs :hints
                  (("Goal"
                    :in-theory (disable acl2-count floor)))))
  (cond ((zp n) nil)
        (t (cons (digit-to-char (mod n 10))
                 (enni (floor n 10))))))

(defun enni-induct (i j)
  (declare (xargs :hints
                  (("Goal"
                    :in-theory (disable acl2-count floor)))))
  (cond ((zp i) nil)
        ((zp j) nil)
        (t (enni-induct (floor i 10) (floor j 10)))))

; Here's the basic uniqueness result vis-a-vis the printed
; representation (even though enni ``prints'' in the reverse
; order and ``prints'' 0 as the empty string of characters).

(defthm enni-unique
  (equal (equal (enni i) (enni j))
         (equal (nfix i) (nfix j)))

  :hints (("Goal" :induct (enni-induct i j))))

; So here is the explanation of the accumulator.

(defun rev (x)
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

(defthm explode-nonnegative-integer-is-enni
  (equal (explode-nonnegative-integer n 10 a)
         (append (rev (enni n))
                 (if (and (null a) (zp n)) '(#\0) a)))

  :hints (("Goal" :in-theory (disable digit-to-char floor mod))))

; So now we must prove that explode-nonnegative-integer produces
; unique representations.  That is surprisingly hard, because of
; all the ways the append expression above can seem to identify
; results.  As an indication of how messy it is, consider how
; many lemmas I need about append, reverse, and enni below.  All
; of these are here simply to get the uniqueness result for
; explode-nonnegative-integer.

(defthm assoc-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm len-append
   (equal (len (append a b))
          (+ (len a) (len b))))

(defthm equal-len-0
   (equal (equal (len x) 0)
          (endp x)))

(defthm append-id-implies-endp
   (equal (equal (append x a) a)
          (endp x))
   :hints (("Goal"
            :use (:instance len-append (a x) (b a))
            :in-theory (disable len-append))))

(defun double-cdr-hint (x y)
   (cond ((endp x) t)
         ((endp y) t)
         (t (double-cdr-hint (cdr x) (cdr y)))))

(defthm equal-append-append
  (implies (and (true-listp a)
                (true-listp c)
                (or (equal (len a) (len c))
                    (equal (len b) (len d))))
           (equal (equal (append a b)
                         (append c d))
                  (and (equal a c)
                       (equal b d))))
  :hints (("Goal" :induct (double-cdr-hint a c))))

(defthm equal-append-singleton
   (equal (equal (append a b) (list e))
          (if (consp a)
              (and (equal (car a) e)
                   (endp (cdr a))
                   (null b))
            (equal b (list e)))))

(defthm consp-rev
   (equal (consp (rev x)) (consp x)))

(defthm true-listp-rev
   (true-listp (rev x))
   :rule-classes :type-prescription)

(defthm equal-rev-rev
   (implies (and (true-listp a)
                 (true-listp b))
            (equal (equal (rev a)
                          (rev b))
                   (equal a b)))
   :hints (("Goal" :induct (double-cdr-hint a b))))

(defthm car-append
   (equal (car (append a b))
          (if (consp a) (car a) (car b))))

; Neat fact: The leading digit in the printed representation is
; #\0 only if the number is 0.

(defthm enni-minnie-zero
  (implies (not (zp i))
           (not (equal (car (rev (enni i))) #\0)))
  :hints (("Goal" :in-theory (disable floor mod))))

(defthm consp-enni
  (equal (consp (enni i)) (not (zp i))))

(defthm equal-rev-singleton
  (equal (equal (rev x) (list e))
         (and (consp x)
              (equal (car x) e)
              (endp (cdr x)))))

(defthm digit-to-char-equal-0
  (implies (and (integerp i)
                (< 0 i)
                (< i 10))
           (not (equal (digit-to-char i) #\0))))

; And here is the uniqueness result we wanted.

(defthm explode-nonnegative-integer-unique
  (equal (equal (explode-nonnegative-integer i 10 a)
                (explode-nonnegative-integer j 10 a))
         (equal (nfix i) (nfix j)))

  :hints (("Goal" :in-theory (disable floor mod digit-to-char)))
  :otf-flg t)

(in-theory (disable explode-nonnegative-integer-is-enni))

;-----------------------------------------------------------------
; We are headed toward genvar1.  But ACL2's genvar1 contains the subterm

; (intern-in-package-of-symbol
;  (coerce
;   (append char-lst
;           (explode-nonnegative-integer cnt 10 nil))
;   'string)
;  pkg-witness)

; and we need several properties of this expression.  So following Paco, we
; introduced gsym to be that subterm (it's easier to type and lemmas about gsym
; are easier to match than lemmas about the inter-in-package-of-symbol above).
; So now we prove key properties of gsym.

(defthm character-listp-explode-nonnegative-integer
  (implies (character-listp ans)
           (character-listp (explode-nonnegative-integer cnt 10 ans))))

(verify-termination gsym)

; We're headed for the theorem that gsyms are unique if their
; cnts are unique.

; Note: The interns-unique theorem below is actually trivial.  If str1 = str2,
; clearly the intern-in-package-of-symbol terms are equal.  In the other
; direction, if the two intern-in-package-of-symbol terms are equal then by the
; substitutivity property for equality,

; x=y --> f(x) = f(y)

; for the f = symbol-name, we know that the symbol-names of the two
; intern-in-package-of-symbol terms are equal.  But those two symbol-name terms
; simplify to sym1 and sym2 respectivity, by the axiom
; symbol-name-intern-in-package-of-symbol.  Unfortunately, ACL2 is not very
; good at applying the substitution property!  So we have to tell it ``to prove
; str1 = str2 apply symbol-name to both sides of that equality hypothesis.''

(encapsulate
 nil
 (local
  (defthm substitution-property-for-symbol-name
    (implies
     (and (stringp str1)
          (stringp str2)
          (symbolp pkg-witness)
          (equal (symbol-name
                  (intern-in-package-of-symbol str1 pkg-witness))
                 (symbol-name
                  (intern-in-package-of-symbol str2 pkg-witness))))
     (equal str1 str2))
    :rule-classes nil))

 (defthm interns-unique
   (implies (and (stringp str1)
                 (stringp str2)
                 (symbolp pkg-witness))
            (iff (equal (intern-in-package-of-symbol str1 pkg-witness)
                        (intern-in-package-of-symbol str2 pkg-witness))
                 (equal str1 str2)))
   :hints (("Subgoal 1" :use substitution-property-for-symbol-name))))

(encapsulate nil
  (local (defthm substitution-property-for-coerce-list
           (implies (and (character-listp x)
                         (character-listp y)
                         (equal (coerce (coerce x 'string) 'list)
                                (coerce (coerce y 'string) 'list)))
                    (equal x y))
           :rule-classes nil))
  (defthm coerce-string-unique
    (implies (and (character-listp x)
                  (character-listp y))
             (iff (equal (coerce x 'string)
                         (coerce y 'string))
                  (equal x y)))
    :hints (("Subgoal 1" :use substitution-property-for-coerce-list))))


; So here is our first major lemma about gsym!

(defthm gsym-unique
  (implies (and (character-listp char-lst)
                (symbolp pkg-witness))
           (iff (equal (gsym pkg-witness char-lst i)
                       (gsym pkg-witness char-lst j))
                (equal (nfix i) (nfix j)))))

(in-theory (disable gsym))

; Below is a function that collects all the symbols genvar1 tries up to cnt.
; Genvar1 could keep track of this list but has no need for it (except to
; explain why it terminates).  (Historical note: as early as the 1970s ``ghost
; variables'' were used in Hoare logics.  These are variables manipulated by
; the code but actually playing no role in results or effects of the program.
; They were used to specify invariants.  Rather than add a ghost variable to
; our code for genvar1 we simply compute what its value would be if it were
; there.)

(defun genvar1-rejected-names-so-far (pkg-witness char-lst cnt)
  (cond ((zp cnt) nil)
        (t (cons (gsym pkg-witness char-lst (- cnt 1))
                 (genvar1-rejected-names-so-far pkg-witness
                                   char-lst
                                   (- cnt 1))))))

(defun genvar1-rejectable-names (pkg-witness avoid-lst)

; We here list all the illegal variable names that could be generated by a call
; of gsym on a pkg-witness that names neither the "KEYWORD" package nor the
; *MAIN-LISP-PACKAGE-NAME* (e.g., "COMMON-LISP"), and a non-empty char-lst that
; begins with a character different from #\* and #\&.  It is permissible here
; to include names that could be rejected but are not!  For example, it could
; be that V1 was imported into the package named by pkg-witness.  If gsym
; generates V1 it would be accepted as a legal variable name.  But we can
; include it in this list because if a rejectable name is accepted genvar1
; doesn't recur, so there's nothing to justify.

; Note: This list is typically very long.  *COMMON-LISP-SPECIALS-AND-CONSTANTS*
; has over 120 elements and it is not unusual to see *ACL2-EXPORTS* imported
; into user-defined packages and that constant contains over 1500 symbols.

  (append avoid-lst
          (pkg-imports (symbol-package-name pkg-witness))
          *COMMON-LISP-SPECIALS-AND-CONSTANTS*))

(defun count-non-members (lst1 lst2)
; We count the number of elements of lst2 that are not in lst1.
  (cond ((endp lst2) 0)
        ((member (car lst2) lst1)
         (count-non-members lst1 (cdr lst2)))
        (t (+ 1 (count-non-members lst1 (cdr lst2))))))

(defthm key-count-non-members-property
  (implies (and (subsetp lit big)
                (member e rejectable-lst)
                (member e big)
                (not (member e lit)))
           (< (count-non-members big rejectable-lst)
              (count-non-members lit rejectable-lst))))

; If you look ahead to genvar1-measure-crux you'll see where we're going.  That
; lemma is the key to why genvar1 terminates.  It is really based on
; key-count-non-members-property above, but we have to relieve the hypotheses
; when big and lit are replaced by certain rejected-names-so-far expressions.

(defthm subsetp-cons
  (implies (subsetp a b)
           (subsetp a (cons e b))))

(defthm subsetp-x-x
  (subsetp x x))

(defthm genvar1-rejected-names-so-far-grows-monotonically
  (implies (and (integerp i)
                (integerp j)
                (<= 0 i)
                (<= i j)
                (character-listp char-lst)
                (symbolp pkg-witness))
           (subsetp (genvar1-rejected-names-so-far pkg-witness char-lst i)
                    (genvar1-rejected-names-so-far pkg-witness char-lst j)))
  :hints (("Goal" :induct (genvar1-rejected-names-so-far pkg-witness char-lst j))))

(defthm not-member-equal-gsym
  (implies (and (integerp i)
                (integerp j)
                (<= 0 i)
                (<= i j)
                (character-listp char-lst)
                (symbolp pkg-witness))
           (not (member-equal (gsym pkg-witness char-lst j)
                              (genvar1-rejected-names-so-far pkg-witness char-lst i)))))

(defthm genvar1-measure-crux
  (implies (and (integerp cnt)
                (<= 0 cnt)
                (character-listp char-lst)
                (symbolp pkg-witness)
                (member (gsym pkg-witness char-lst cnt) rejectable-lst))
           (< (count-non-members
               (genvar1-rejected-names-so-far pkg-witness char-lst (+ 1 cnt))
               rejectable-lst)
              (count-non-members
               (genvar1-rejected-names-so-far pkg-witness char-lst cnt)
               rejectable-lst)))
  :rule-classes :linear)

(defthm member-avoid-lst-implies-member-rejectionables
  (implies (member e avoid-lst)
           (member e (genvar1-rejectable-names pkg-witness avoid-lst))))

; (defthm explode-nonnegative-integer-non-nil
;   (implies (true-listp ans)
;            (consp (explode-nonnegative-integer cnt 10 ans))))

(defthm equal-intern-in-package-of-symbol
 (implies (and (stringp str)
               (symbolp pkg-witness)
               (symbolp s2))
          (equal (equal (intern-in-package-of-symbol str pkg-witness) s2)
                 (and (equal (if (member-symbol-name str (pkg-imports (symbol-package-name pkg-witness)))
                                 (symbol-package-name
                                  (car (member-symbol-name str (pkg-imports (symbol-package-name pkg-witness)))))
                                 (symbol-package-name pkg-witness))
                             (symbol-package-name s2))
                      (equal str
                             (symbol-name s2)))))
 :hints
 (("Goal" :use (:instance symbol-equality
                          (s1 (intern-in-package-of-symbol str pkg-witness))
                          (s2 s2)))))

(defthm gsym-not-equal-t
  (implies (and (natp cnt)
                (character-listp char-lst)
                (consp char-lst)
                (symbolp pkg-witness))
           (not (equal (gsym pkg-witness char-lst cnt) t)))
  :hints (("Goal" :in-theory (enable gsym)
           :do-not-induct t)))

; Here is the analogous thm stating that gsym can't return NIL.  Unfortunately,
; the equality with nil eliminated and we don't automatically apply
; equal-intern-in-package-of-symbol, so we have to give it as a hint.  The
; other complication is that we have to prove that (coerce (append char-lst
; (explode-nonnegative-integer ...)) 'string) is different from "NIL".  The T
; case was easier because we just observed that the coerce had length greater
; than 1.  Here we have to observe that the last char in the explode is a
; digit, not #\L.  Yuck.

(defthm car-last-append
  (equal (car (last (append a b)))
         (if (endp b)
             (car (last a))
             (car (last b)))))

(defthm gsym-not-equal-nil-lemma-lemma
  (implies (and (consp b)
                (not (equal (car (last b)) #\L)))
           (not (equal (append char-lst b) '(#\N #\I #\L)))))

(defun digit-character-listp (lst)
  (cond
   ((endp lst) t)
   (t (and (member (car lst)
                   '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
           (digit-character-listp (cdr lst))))))

(defthm digit-character-listp-explode-nonnegative-integer
  (implies (digit-character-listp ans)
           (digit-character-listp (explode-nonnegative-integer cnt '10 ans))))

(defthm car-last-digit-character-listp-not-L
  (implies (digit-character-listp lst)
           (not (equal (car (last lst)) #\L))))

(defthm gsym-not-equal-nil-lemma
  (implies (and (natp cnt)
                (character-listp char-lst)
                (consp char-lst))
           (not (equal (append char-lst
                               (explode-nonnegative-integer cnt 10 nil))
                       '(#\N #\I #\L))))
  :hints (("Goal"
           :do-not-induct t
           :use (:instance
                 (:theorem (implies (not (equal (car (last lst1))
                                                (car (last lst2))))
                                    (not (equal lst1 lst2))))
                 (lst1 (append char-lst
                               (explode-nonnegative-integer cnt 10 nil)))
                 (lst2 '(#\N #\I #\L))))))

(defthm gsym-not-equal-nil
  (implies (and (natp cnt)
                (character-listp char-lst)
                (consp char-lst)
                (symbolp pkg-witness))
           (gsym pkg-witness char-lst cnt)) ; not NIL
  :hints (("Goal"
           :in-theory (e/d (gsym)
                           (equal-intern-in-package-of-symbol))
           :use (:instance equal-intern-in-package-of-symbol
                           (str (coerce (append char-lst
                                                (explode-nonnegative-integer cnt 10 nil))
                                        'string))
                           (pkg-witness pkg-witness)
                           (s2 nil)))))

(encapsulate nil
  (local (defthm member-symbol-name-implies-member-car
           (implies (member-symbol-name str lst)
                    (member-equal (car (member-symbol-name str lst))
                                  lst))
           :rule-classes nil
           :hints (("Goal" :in-theory (enable member-symbol-name)))))

  (defthm member-intern-in-package-of-symbol-pkg-imports
    (implies (and (stringp x)
                  (symbolp y)
                  (not (equal (symbol-package-name
                               (intern-in-package-of-symbol x y))
                              (symbol-package-name y))))
             (member-equal (intern-in-package-of-symbol x y)
                           (pkg-imports (symbol-package-name y))))
    :hints
    (("Goal"
      :in-theory (disable symbol-name-intern-in-package-of-symbol
                          symbol-package-name-intern-in-package-of-symbol
                          intern-in-package-of-symbol-is-identity)
      :use ((:instance symbol-name-intern-in-package-of-symbol
                       (s x)
                       (any-symbol y))
            symbol-package-name-intern-in-package-of-symbol
            intern-in-package-of-symbol-is-identity
            (:instance member-symbol-name-implies-member-car
                       (str x)
                       (lst (pkg-imports (symbol-package-name y)))))))))

(defthm member-gsym-pkg-imports
  (implies (and (natp cnt)
                (character-listp char-lst)
                (symbolp pkg-witness)
                (not (equal (symbol-package-name (gsym pkg-witness char-lst cnt))
                            (symbol-package-name pkg-witness))))
           (member-equal (gsym pkg-witness char-lst cnt)
                         (pkg-imports (symbol-package-name pkg-witness))))
  :hints
  (("Goal" :in-theory (enable gsym))))

(defthm member-append
  (iff (member e (append a b))
       (or (member e a)
           (member e b))))

(defthm member-gsym-rejectable-names
  (implies (and (natp cnt)
                (character-listp char-lst)
                (symbolp pkg-witness)
                (not (equal (symbol-package-name (gsym pkg-witness char-lst cnt))
                            (symbol-package-name pkg-witness))))
           (member-equal (gsym pkg-witness char-lst cnt)
                         (genvar1-rejectable-names pkg-witness avoid-lst))))

(defthm symbol-name-gsym
  (implies (and (symbolp pkg-witness)
                (character-listp char-lst)
                (consp char-lst))
           (equal (car (coerce (symbol-name (gsym pkg-witness char-lst cnt)) 'list))
                  (car char-lst)))
  :hints
  (("Goal" :in-theory (enable gsym))))

(defthm rejected-gsyms-are-rejectable
  (implies (and (symbolp pkg-witness)
                (character-listp char-lst)
                (consp char-lst)
                (let ((p (symbol-package-name pkg-witness)))
                  (and (not (equal p "KEYWORD"))
                       (not (equal p *main-lisp-package-name*))))
                (not (equal (car char-lst) #\*))
                (not (equal (car char-lst) #\&))
                (integerp cnt)
                (<= 0 cnt)
                (not
                 (equal (legal-variable-or-constant-namep
                         (gsym pkg-witness char-lst cnt))
                        'variable)))
           (member (gsym pkg-witness char-lst cnt)
                   (genvar1-rejectable-names pkg-witness avoid-lst)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (LEGAL-VARIABLE-OR-CONSTANT-NAMEP)
                           (member-equal
                            (:executable-counterpart member-equal))))))

(in-theory (disable genvar1-rejected-names-so-far
                    (:executable-counterpart genvar1-rejected-names-so-far)
                    genvar1-rejectable-names
                    EQUAL-INTERN-IN-PACKAGE-OF-SYMBOL))

; So here is the measure that will explain genvar1.

(defun genvar1-measure (pkg-witness char-lst avoid-lst cnt)
  (let* ((pkg-witness
          (if (symbolp pkg-witness) pkg-witness 'rewrite))
         (char-lst
          (if (character-listp char-lst) char-lst '(#\X)))
         (cnt (nfix cnt)))
    (count-non-members (genvar1-rejected-names-so-far pkg-witness char-lst cnt)
                       (genvar1-rejectable-names pkg-witness avoid-lst))))

; In the defun of genvar1 below we have an mbe requiring that we prove this.
; It's trivial by opening up the defun of gsym.  But we want to keep gsym
; disabled in the admission.  Rather than give a guard-goal-specific hint in
; the defun of genvar1 we just prove this very restrictive theorem that
; recognizes their equality without rewriting gsym.

(defthm gsym-is-intern-in-package-of-symbol
  (equal (equal (gsym pkg-witness char-lst cnt)
                (intern-in-package-of-symbol
                 (coerce
                  (append char-lst
                          (explode-nonnegative-integer cnt 10 nil))
                  'string)
                 pkg-witness))
         t)
  :hints (("Goal" :in-theory (enable gsym))))

(verify-termination genvar1-guardp)

(local (in-theory (disable member-equal)))

; Matt K. comment.  After fiddling with the xargs in the ACL2 source definition
; of genvar1, I managed to get "make devel-check" to succeed with an acl2-devel
; ACL2 executable.  But then the following caused certification to fail with a
; normal ACL2 executable -- where we don't need the next form anyhow, so I'm
; restricting it to acl2-devel runs.
#+acl2-devel
(verify-termination genvar1
  (declare (xargs :guard
                  (genvar1-guardp pkg-witness char-lst avoid-lst cnt)
                  :measure
                  (genvar1-measure pkg-witness char-lst avoid-lst cnt))))

(defthm not-member-genvar1-avoid-lst
  (implies (genvar1-guardp pkg-witness char-lst avoid-lst cnt)
           (not (member (genvar1 pkg-witness char-lst avoid-lst cnt) avoid-lst))))

(defthm legal-variablep-genvar1
  (implies (genvar1-guardp pkg-witness char-lst avoid-lst cnt)
           (legal-variablep (genvar1 pkg-witness char-lst avoid-lst cnt))))

(in-theory (disable legal-variablep))

;;-----------------------------------------------------------------
;; (defun genvar (pkg-witness prefix n avoid-lst)

;; ; This is THE function that ACL2 uses to generate new variable names.
;; ; Prefix is a string and n is either nil or a natural number.  Together we
;; ; call prefix and n the "root" of the variable we generate.

;; ; We generate from prefix a legal variable symbol in the same package as
;; ; pkg-witness that does not occur in avoid-lst.  If n is nil, we first try the
;; ; symbol with symbol-name prefix first and otherwise suffix prefix with
;; ; increasingly large naturals (starting from 0) to find a suitable variable.
;; ; If n is non-nil it had better be a natural and we immediately begin trying
;; ; suffixes from there.  Since no legal variable begins with #\* or #\&, we tack
;; ; a #\V on the front of our prefix if prefix starts with one of those chars.
;; ; If prefix is empty, we use "V".

;; ; Note: This system will eventually contain a lot of code to generate
;; ; "suggestive" variable names.  However, we make the convention that
;; ; in the end every variable name generated is generated by this
;; ; function.  Thus, all other code associated with variable name
;; ; generation is heuristic if this one is correct.

;;   (let* ((pkg-witness (cond ((let ((p (symbol-package-name pkg-witness)))
;;                                (or (equal p "KEYWORD")
;;                                    (equal p *main-lisp-package-name*)))
;; ; If pkg-witness is in an inappropriate package, we default it to the
;; ; "ACL2" package.
;;                              'genvar)
;;                             (t pkg-witness)))
;;          (sym (if (null n) (intern-in-package-of-symbol prefix pkg-witness) nil))
;;          (cnt (if n n 0)))
;;     (cond ((and (null n)
;;                 (legal-variablep sym)
;;                 (not (member sym avoid-lst)))
;;            sym)
;;           (t (let ((prefix (coerce prefix 'list)))
;;                (cond ((null prefix) (genvar1 pkg-witness '(#\V) avoid-lst cnt))
;;                      ((and (consp prefix)
;;                            (or (eql (car prefix) #\*)
;;                                (eql (car prefix) #\&)))
;;                       (genvar1 pkg-witness (cons #\V prefix) avoid-lst cnt))
;;                      (t (genvar1 pkg-witness prefix avoid-lst cnt))))))))

(verify-termination genvar-guardp)
(verify-termination genvar)

(verify-termination abstract-pat1)

(make-flag flag-abstract-pat1 abstract-pat1)

(defthm-flag-abstract-pat1

  (defthm true-listp-mv-nth-1-abstract-pat1
    (implies (true-listp vars)
             (true-listp (mv-nth 1 (abstract-pat1 k-flg pat vars))))
    :flag abstract-pat1)

  (defthm true-listp-mv-nth-1-abstract-pat1-lst
    (implies (true-listp vars)
             (true-listp (mv-nth 1 (abstract-pat1-lst k-flg pats vars))))
    :flag abstract-pat1-lst))

(defun len-mv-nth-0-abstract-pat1-lst-induction (k-flg pats vars)
  (declare (ignorable k-flg vars))
  (if (endp pats)
      t
      (mv-let (new-pat new-vars)
        (abstract-pat1 k-flg (car pats) vars)
        (declare (ignore new-pat))
        (len-mv-nth-0-abstract-pat1-lst-induction
         k-flg
         (cdr pats)
         new-vars))))

(defthm len-mv-nth-0-abstract-pat1-lst
  (equal (len (mv-nth 0 (abstract-pat1-lst k-flg pats vars)))
         (len pats))
  :hints (("Goal" :induct (len-mv-nth-0-abstract-pat1-lst-induction k-flg pats vars))))

(defthm-flag-abstract-pat1

  (defthm pseudo-termp-mv-nth-0-abstract-pat1
    (implies (pseudo-termp pat)
             (pseudo-termp (mv-nth 0 (abstract-pat1 k-flg pat vars))))
    :flag abstract-pat1)

  (defthm pseudo-term-listp-mv-nth-0-abstract-pat1-lst
    (implies (pseudo-term-listp pats)
             (pseudo-term-listp (mv-nth 0 (abstract-pat1-lst k-flg pats vars))))
    :flag abstract-pat1-lst))

(verify-guards abstract-pat1)

(make-flag flag-all-vars1 all-vars1)

(defthm-flag-all-vars1
  (defthm true-listp-all-vars1
    (implies (true-listp ans)
             (true-listp (all-vars1 term ans)))
    :flag all-vars1)
  (defthm true-listp-all-vars1-lst
    (implies (true-listp ans)
             (true-listp (all-vars1-lst lst ans)))
    :flag all-vars1-lst))

(verify-termination abstract-pat)

(verify-termination symbol-alist-to-keyword-value-list)

(verify-termination brr-criteria-alistp)

(defthm brr-criteria-listp-implies-alistp
  (implies (brr-criteria-alistp alist)
           (alistp alist))
  :rule-classes :forward-chaining)

(defthm brr-criteria-alistp-has-natp-depth
  (implies (and (brr-criteria-alistp alist)
                (assoc :depth alist))
           (natp (cdr (assoc :depth alist)))))

(defthm brr-criteria-alistp-has-pseudo-termp-abstraction
  (implies (and (brr-criteria-alistp alist)
                (assoc :abstraction alist))
           (pseudo-termp (cdr (assoc :abstraction alist)))))

(defthm brr-criteria-alistp-has-booleanp-lambda
  (implies (and (brr-criteria-alistp alist)
                (assoc :lambda alist)
                (cdr (assoc :lambda alist)))
           (equal (cdr (assoc :lambda alist)) t)))

(verify-termination make-built-in-brr-near-miss-msg)

(verify-termination get-brr-one-way-unify-info)

(verify-termination built-in-brr-near-missp)
