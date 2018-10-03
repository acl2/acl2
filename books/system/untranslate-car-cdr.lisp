; Copyright (C) 2014, Regents of the University of Texas
; Written by J Strother Moore, October, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; To recertify:
; (certify-book "untranslate-car-cdr")

; Proof of the Correctness of CADR Centric Untranslation
; J Strother Moore
; Georgetown, TX, October, 2014

; Abstract

; When ACL2 displays a formula to the user, it ``untranslates'' formal
; (internal-form) terms into terms involving macros.  For example, (CAR (CDR
; X)) is displayed as (CADR X).  Common Lisp provides 28 macros for the
; combinations of CARs and CDRs up to four deep.  Given all these available
; abbreviations how should (CAR (CDR (CDR (CAR (CDR X))))) be displayed?

; For the first 25 years of ACL2's history, the term above was displayed as
; (CADDAR (CDR X)).

; The code verified here displays it as (CADDR (CADR X)).

; The old method availed itself of all 28 of the car-cdr macros.  The new
; method only introduces 6 of them: CADR, CADDR, CADDDR, CDDR, CDDDR, CDDDDR.
; This code never introduces such macros as CAAR or CDDAAR, preferring CARs and
; CDRs when necessary.  Lisp programmers tend to recognize CADR, CADDR, and
; CADDDR as the accessors for the 1st, 2nd, and 3rd (0-based) elements of a
; list.

; We call this style of untranslation ``CADR Centric'' because it emphasizes
; the most common use of the car-cdr macros: accessing particular elements of
; linear lists.

; Perhaps the most important advantage of CADR Centric untranslation is that it
; operates from the inside out, where the old method operated from the outside
; in.  The inside out approach is more likely to give related elements related
; names.  For example, consider the formula

; (p (car (cdr (car (cdr x))))
;    (car (cdr (cdr (car (cdr x))))))

; In the old style this would be displayed as

; (p (cadadr x)
;    (caddar (cdr x)))

; whereas in the new style it is displayed as

; (p (cadr (cadr x))
;    (caddr (cadr x)))

; which makes it clear that p is being applied to the 1st and 2nd elements of
; the 1st element of x.

; Because I found the code confusing, I decided to prove that the untranslation
; preserved the meaning of the original term.  The main theorem proved at the
; bottom of this book is:

; (DEFTHM UNTRANSLATE-CAR-CDR-NEST-CORRECT
;   (EQUAL (EVAD TERM ALIST)
;          (EVAD (UNTRANSLATE-CAR-CDR-NEST TERM) ALIST))
;   :RULE-CLASSES NIL)

; where evad is an ACL2 evaluator that can handle CAR, CDR, and the six macros
; possibly introduced by CADR Centric untranslation.  Note that evad cannot be
; introduced by defevaluator because that event only allows function symbols to
; be interpreted, whereas CADR, CDDR, etc., are macro symbols.  But the
; constraints on evad are exactly analogous to what defevaluator generates.
; For example,

; (DEFTHM EVAD-constraint-12
;   (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'CADDR))
;            (EQUAL (EVAD X A)
;                   (CADDR (EVAD (CADR X) A)))))

; Note also that UNTRANSLATE-CAR-CDR-NEST-CORRECT does not establish that
; untranslate-car-cdr-nest returns a well-formed term.

; The problem with well-formedness in this context is that there are two senses
; of that word: well-formed before untranslation and well-formed after
; untranslation.  In practice in the ACL2 system, the input to untranslation is
; a formal (``translated'') ACL2 term: no macros are used.  The output is
; ``well-formed'' in a different sense, meaning that the macros introduced
; expand without error.  For example, ACL2's untranslator may see
; (IF a b (IF c d e)) as input and return (COND (a b) (c d) (T e)) as
; input and they are well-formed in different senses.

; The function untranslate-car-cdr-nest verified here operates in two phases.
; Phase 1 extracts a list of As and Ds corresponding to the cAr and cDr symbols
; surrounding some base.  Phase 1 returns the list and the base.  Phase 2 then
; wraps a nest of the CADR Centric functions and macros around the base.  But
; when this code is used by ACL2's full untranslate mechanism, a recursive call
; of ACL2's mechanism is interposed on the base between phases 1 and 2.  Thus,
; the base identified by phase 1 is in translated form but the term supplied to
; phase 2 is in untranslated form.  Thus, the senses in which the inputs to
; phases 1 and 2 are well-formed are different.

; But in this book, we ignore ACL2's full untranslation mechanism.  We just
; compose phases 1 and 2, make no assumptions about the shapes of the terms
; being manipulated, and just prove that the input and output have the same
; meaning in the EVAD sense.

; -----------------------------------------------------------------
; Implementation: This single page contains the implementation (and its
; termination proof).  The rest of this ridiculously long file is the
; specification and proof of correctness!

(in-package "ACL2")

(program)

(defun make-reversed-ad-list (term ans)

; We treat term as a CAR/CDR nest around some ``base'' and return (mv ad-lst
; base), where ad-lst is the reversed list of #\A and #\D characters and base
; is the base of the CAR/CDR nest.  Thus, (CADDR B) into (mv '(#\D #\D #\A) B).
; If term is not a CAR/CDR nest, adr-lst is nil.

  (cond ((variablep term)
         (mv ans term))
        ((fquotep term)
         (mv ans term))
        ((eq (ffn-symb term) 'CAR)
         (make-reversed-ad-list (fargn term 1) (cons '#\A ans)))
        ((eq (ffn-symb term) 'CDR)
         (make-reversed-ad-list (fargn term 1) (cons '#\D ans)))
        (t (mv ans term))))

(defun car-cdr-abbrev-name (adr-lst)
; Given an adr-lst we turn it into one of the CAR/CDR abbreviation names.  We
; assume the adr-lst corresponds to a legal name, e.g., its length is no
; greater than five (counting the #\R).
  (intern (coerce (cons #\C adr-lst) 'string) "ACL2"))

(defun pretty-parse-ad-list (ad-list dr-list n base)
  (cond
   ((eql n 5)
    (pretty-parse-ad-list ad-list '(#\R) 1
                          (list (car-cdr-abbrev-name dr-list) base)))
   ((endp ad-list)
    (cond ((eql n 1) base)
          (t (list (car-cdr-abbrev-name dr-list) base))))
   ((eql (car ad-list) #\A)
    (pretty-parse-ad-list (cdr ad-list) '(#\R) 1
                          (list (car-cdr-abbrev-name (cons #\A dr-list)) base)))
   (t ; (eql (car ad-list) '#\D)
    (pretty-parse-ad-list (cdr ad-list) (cons #\D dr-list) (+ 1 n) base))))

(defun untranslate-car-cdr-nest (term)

; Examples:
; (untranslate-car-cdr-nest '(car (cdr (car b))))
; ==> (CADR (CAR B))
; (untranslate-car-cdr-nest '(car (cdr (cdr b))))
; ==> (CADDR B)
; (untranslate-car-cdr-nest '(car (car (cdr (cdr b)))))
; ==> (CAR (CADDR B))

  (mv-let (ad-list base)
          (make-reversed-ad-list term nil)
          (cond
           ((null ad-list) base)
           (t (pretty-parse-ad-list ad-list '(#\R) 1 base)))))

; -----------------------------------------------------------------
; Conversion to Logic Mode

(logic)
(include-book "ordinals/lexicographic-ordering" :dir :system)

(verify-termination make-reversed-ad-list)
(verify-termination car-cdr-abbrev-name)
(verify-termination pretty-parse-ad-list
 (declare (xargs :measure (llist (acl2-count ad-list) (nfix n))
                 :well-founded-relation l<)))
(verify-termination untranslate-car-cdr-nest)

; -----------------------------------------------------------------
; Specification Related Functions and Simple Theorems about Them

; There are three types of lists of interest here: lists of #\As and #\Ds,
; lists of #\Ds with last element #\R, and list of that second type optionally
; extended with a single #\A.  We call these ``AD'', ``DR'', and ``ADR'' lists,
; respectively.

(defun ad-listp (x)
  (cond ((endp x) (eq x nil))
        ((eql (car x) #\A) (ad-listp (cdr x)))
        ((eql (car x) #\D) (ad-listp (cdr x)))
        (t nil)))

(defun dr-listp (x)
  (cond ((endp x) nil)
        ((eql (car x) #\R) (equal (cdr x) nil))
        ((eql (car x) #\D) (dr-listp (cdr x)))
        (t nil)))

(defun adr-listp (x)
  (cond ((endp x) nil)
        ((eql (car x) #\A)
         (dr-listp (cdr x)))
        (t (dr-listp x))))

(defun compose-ad (ad-list term)

; We treat ad-list as a list of #\A and #\D, ignoring all other elements.  This
; allows us to call it on lists of #\D terminated by #\R, which is another
; ``data type'' in this system.

  (cond ((endp ad-list) term)
        ((eql (car ad-list) #\A)
         (compose-ad (cdr ad-list) (list 'CAR term)))
        ((eql (car ad-list) #\D)
         (compose-ad (cdr ad-list) (list 'CDR term)))
        (t (compose-ad (cdr ad-list) term))))

; Imagine we allowed macros to be ``function symbols'' in defevaluator.
; Then this form:

; (defevaluator evad evad-lst
;   ((CAR x)
;    (CDR x)
;    (CADR x)
;    (CDDR x)
;    (CADDR x)
;    (CDDDR x)
;    (CADDDR x)
;    (CDDDDR x)))

; would expand to:

(ENCAPSULATE
 (((EVAD * *) => *)
  ((EVAD-LST * *) => *))
 (SET-INHIBIT-WARNINGS "theory")
 (LOCAL (IN-THEORY *DEFEVALUATOR-FORM-BASE-THEORY*))
 (LOCAL (DEFUN-NX APPLY-FOR-DEFEVALUATOR (FN ARGS)
          (DECLARE (XARGS :VERIFY-GUARDS NIL
                          :NORMALIZE NIL))
          (COND ((EQUAL FN 'CAR) (CAR (CAR ARGS)))
                ((EQUAL FN 'CDR) (CDR (CAR ARGS)))
                ((EQUAL FN 'CADR) (CADR (CAR ARGS)))
                ((EQUAL FN 'CDDR) (CDDR (CAR ARGS)))
                ((EQUAL FN 'CADDR) (CADDR (CAR ARGS)))
                ((EQUAL FN 'CDDDR) (CDDDR (CAR ARGS)))
                ((EQUAL FN 'CADDDR) (CADDDR (CAR ARGS)))
                ((EQUAL FN 'CDDDDR) (CDDDDR (CAR ARGS)))
                (T NIL))))
 (LOCAL
  (MUTUAL-RECURSION
   (DEFUN-NX
     EVAD (X A)
     (DECLARE
      (XARGS
       :VERIFY-GUARDS NIL
       :MEASURE (ACL2-COUNT X)
       :WELL-FOUNDED-RELATION O<
       :NORMALIZE NIL
       :HINTS (("goal" :IN-THEORY (ENABLE (:TYPE-PRESCRIPTION ACL2-COUNT))))
       :MODE :LOGIC))
     (COND ((SYMBOLP X)
            (AND X (CDR (ASSOC-EQ X A))))
           ((ATOM X) NIL)
           ((EQ (CAR X) 'QUOTE) (CAR (CDR X)))
           (T (LET ((ARGS (EVAD-LST (CDR X) A)))
                   (COND ((CONSP (CAR X))
                          (EVAD (CAR (CDR (CDR (CAR X))))
                                (PAIRLIS$ (CAR (CDR (CAR X))) ARGS)))
                         ((NOT (SYMBOLP (CAR X))) NIL)
                         (T (APPLY-FOR-DEFEVALUATOR (CAR X)
                                                    ARGS)))))))
   (DEFUN-NX EVAD-LST (X-LST A)
     (DECLARE (XARGS :MEASURE (ACL2-COUNT X-LST)
                     :WELL-FOUNDED-RELATION O<))
     (COND ((ENDP X-LST) NIL)
           (T (CONS (EVAD (CAR X-LST) A)
                    (EVAD-LST (CDR X-LST) A)))))))
 (LOCAL (IN-THEORY (DISABLE EVAD EVAD-LST APPLY-FOR-DEFEVALUATOR)))
 ;; Mihir M. mod: this is one of a small number of unusual books
 ;; which use true-list fix (enabled by default) while also
 ;; including books which bring in list-fix and disable the
 ;; underlying function true-list-fix. It needs this theory hint for
 ;; proofs to succeed.
 (LOCAL
  (DEFTHM EVAL-LIST-KWOTE-LST
    (EQUAL (EVAD-LST (KWOTE-LST ARGS) A)
           (FIX-TRUE-LIST ARGS))
    :HINTS (("goal" :EXPAND ((:FREE (X Y) (EVAD-LST (CONS X Y) A))
                             (EVAD-LST NIL A)
                             (:FREE (X) (EVAD (LIST 'QUOTE X) A)))
             :IN-THEORY (ENABLE TRUE-LIST-FIX)
             :INDUCT (TRUE-LIST-FIX ARGS)))))
 (LOCAL
  (DEFTHM FIX-TRUE-LIST-EV-LST
    (EQUAL (FIX-TRUE-LIST (EVAD-LST X A))
           (EVAD-LST X A))
    :HINTS (("goal" :INDUCT (LEN X)
             :IN-THEORY (E/D ((:INDUCTION LEN)))
             :EXPAND ((EVAD-LST X A) (EVAD-LST NIL A))))))
 (LOCAL (DEFTHM EV-COMMUTES-CAR
          (EQUAL (CAR (EVAD-LST X A))
                 (EVAD (CAR X) A))
          :HINTS (("goal" :EXPAND ((EVAD-LST X A) (EVAD NIL A))
                   :IN-THEORY (ENABLE DEFAULT-CAR)))))
 (LOCAL (DEFTHM EV-LST-COMMUTES-CDR
          (EQUAL (CDR (EVAD-LST X A))
                 (EVAD-LST (CDR X) A))
          :HINTS (("Goal" :EXPAND ((EVAD-LST X A) (EVAD-LST NIL A))
                   :IN-THEORY (ENABLE DEFAULT-CDR)))))
 (DEFTHMD
   EVAD-CONSTRAINT-0
   (IMPLIES (AND (CONSP X)
                 (SYNTAXP (NOT (EQUAL A ''NIL)))
                 (NOT (EQUAL (CAR X) 'QUOTE)))
            (EQUAL (EVAD X A)
                   (EVAD (CONS (CAR X)
                               (KWOTE-LST (EVAD-LST (CDR X) A)))
                         NIL)))
   :HINTS (("Goal" :EXPAND ((:FREE (X) (HIDE X))
                            (EVAD X A)
                            (:FREE (ARGS)
                             (EVAD (CONS (CAR X) ARGS) NIL)))
            :IN-THEORY '(EVAL-LIST-KWOTE-LST FIX-TRUE-LIST-EV-LST
                                             CAR-CONS CDR-CONS))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-0)))
 (DEFTHM EVAD-CONSTRAINT-1
   (IMPLIES (SYMBOLP X)
            (EQUAL (EVAD X A)
                   (AND X (CDR (ASSOC-EQUAL X A)))))
   :HINTS (("Goal" :EXPAND ((EVAD X A)))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-1)))
 (DEFTHM EVAD-CONSTRAINT-2
   (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'QUOTE))
            (EQUAL (EVAD X A) (CADR X)))
   :HINTS (("Goal" :EXPAND ((EVAD X A)))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-2)))
 (DEFTHM EVAD-CONSTRAINT-3
   (IMPLIES (AND (CONSP X) (CONSP (CAR X)))
            (EQUAL (EVAD X A)
                   (EVAD (CADDR (CAR X))
                         (PAIRLIS$ (CADR (CAR X))
                                   (EVAD-LST (CDR X) A)))))
   :HINTS (("Goal" :EXPAND ((EVAD X A)))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-3)))
 (DEFTHM EVAD-CONSTRAINT-4
   (IMPLIES (NOT (CONSP X-LST))
            (EQUAL (EVAD-LST X-LST A) NIL))
   :HINTS (("Goal" :EXPAND ((EVAD-LST X-LST A)))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-4)))
 (DEFTHM EVAD-CONSTRAINT-5
   (IMPLIES (CONSP X-LST)
            (EQUAL (EVAD-LST X-LST A)
                   (CONS (EVAD (CAR X-LST) A)
                         (EVAD-LST (CDR X-LST) A))))
   :HINTS (("Goal" :EXPAND ((EVAD-LST X-LST A)))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-5)))
 (DEFTHMD EVAD-CONSTRAINT-6
   (IMPLIES (AND (NOT (CONSP X)) (NOT (SYMBOLP X)))
            (EQUAL (EVAD X A) NIL))
   :HINTS (("Goal" :EXPAND ((EVAD X A)))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-6)))
 (DEFTHMD EVAD-CONSTRAINT-7
   (IMPLIES (AND (CONSP X) (NOT (CONSP (CAR X))) (NOT (SYMBOLP (CAR X))))
            (EQUAL (EVAD X A) NIL))
   :HINTS (("Goal" :EXPAND ((EVAD X A)))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-7)))
 (DEFTHM
   EVAD-CONSTRAINT-8
   (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'CAR))
            (EQUAL (EVAD X A)
                   (CAR (EVAD (CADR X) A))))
   :HINTS (("Goal" :EXPAND ((EVAD X A)
                            (:FREE (X) (HIDE X))
                            (:FREE (FN ARGS)
                             (APPLY-FOR-DEFEVALUATOR FN ARGS))))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-8)))
 (DEFTHM
   EVAD-CONSTRAINT-9
   (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'CDR))
            (EQUAL (EVAD X A)
                   (CDR (EVAD (CADR X) A))))
   :HINTS (("Goal" :EXPAND ((EVAD X A)
                            (:FREE (X) (HIDE X))
                            (:FREE (FN ARGS)
                             (APPLY-FOR-DEFEVALUATOR FN ARGS))))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-9)))
 (DEFTHM
   EVAD-CONSTRAINT-10
   (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'CADR))
            (EQUAL (EVAD X A)
                   (CADR (EVAD (CADR X) A))))
   :HINTS (("Goal" :EXPAND ((EVAD X A)
                            (:FREE (X) (HIDE X))
                            (:FREE (FN ARGS)
                             (APPLY-FOR-DEFEVALUATOR FN ARGS))))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-10)))
 (DEFTHM
   EVAD-CONSTRAINT-11
   (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'CDDR))
            (EQUAL (EVAD X A)
                   (CDDR (EVAD (CADR X) A))))
   :HINTS (("Goal" :EXPAND ((EVAD X A)
                            (:FREE (X) (HIDE X))
                            (:FREE (FN ARGS)
                             (APPLY-FOR-DEFEVALUATOR FN ARGS))))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-11)))
 (DEFTHM
   EVAD-CONSTRAINT-12
   (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'CADDR))
            (EQUAL (EVAD X A)
                   (CADDR (EVAD (CADR X) A))))
   :HINTS (("Goal" :EXPAND ((EVAD X A)
                            (:FREE (X) (HIDE X))
                            (:FREE (FN ARGS)
                             (APPLY-FOR-DEFEVALUATOR FN ARGS))))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-12)))
 (DEFTHM
   EVAD-CONSTRAINT-13
   (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'CDDDR))
            (EQUAL (EVAD X A)
                   (CDDDR (EVAD (CADR X) A))))
   :HINTS (("Goal" :EXPAND ((EVAD X A)
                            (:FREE (X) (HIDE X))
                            (:FREE (FN ARGS)
                             (APPLY-FOR-DEFEVALUATOR FN ARGS))))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-13)))
 (DEFTHM
   EVAD-CONSTRAINT-14
   (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'CADDDR))
            (EQUAL (EVAD X A)
                   (CADDDR (EVAD (CADR X) A))))
   :HINTS (("Goal" :EXPAND ((EVAD X A)
                            (:FREE (X) (HIDE X))
                            (:FREE (FN ARGS)
                             (APPLY-FOR-DEFEVALUATOR FN ARGS))))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-14)))
 (DEFTHM
   EVAD-CONSTRAINT-15
   (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'CDDDDR))
            (EQUAL (EVAD X A)
                   (CDDDDR (EVAD (CADR X) A))))
   :HINTS (("Goal" :EXPAND ((EVAD X A)
                            (:FREE (X) (HIDE X))
                            (:FREE (FN ARGS)
                             (APPLY-FOR-DEFEVALUATOR FN ARGS))))))
 (LOCAL (IN-THEORY (DISABLE EVAD-CONSTRAINT-15))))

; We are actually only interested in ADR lists whose lengths lie between 2 and
; 5, and there are only a finite number of them.  Proofs are easier if we just
; enumerate the cases.

(defthm enumerate-dr-listps
  (implies (and (dr-listp dr-list)
;                (<= 2 (len dr-list)) ; !!!
                (<= (len dr-list) 5))
           (member dr-list
                   '((#\R)
                     (#\D #\R)
                     (#\D #\D #\R)
                     (#\D #\D #\D #\R)
                     (#\D #\D #\D #\D #\R))))
  :rule-classes nil)

(defthm enumerate-adr-listps
  (implies (and (adr-listp adr-list)
;                (<= 2 (len adr-list)) ; !!!
                (<= (len adr-list) 5))
           (member adr-list
                   '((#\R)
                     (#\A #\R)
                     (#\D #\R)
                     (#\A #\D #\R)
                     (#\D #\D #\R)
                     (#\A #\D #\D #\R)
                     (#\D #\D #\D #\R)
                     (#\A #\D #\D #\D #\R)
                     (#\D #\D #\D #\D #\R))))
  :rule-classes nil)

(in-theory (disable car-cdr-abbrev-name))

(defun rev (x)
  (if (endp x)
      nil
      (append (rev (cdr x)) (list (car x)))))

(defthm evad-list-car-cdr-abbrev-name
  (implies (and (adr-listp adr-list)
                (<= 2 (len adr-list))
                (<= (len adr-list) 5))
           (equal (evad (list (car-cdr-abbrev-name adr-list) base) alist)
                  (evad (compose-ad (rev adr-list) base) alist)))
  :hints (("Goal" :use enumerate-adr-listps)))

(defun equal-evad-compose-ad-hint (ad-list x y)
  (cond ((endp ad-list) (list x y))
        ((eql (car ad-list) #\A)
         (equal-evad-compose-ad-hint (cdr ad-list) (list 'CAR x) (list 'CAR y)))
        ((eql (car ad-list) #\D)
         (equal-evad-compose-ad-hint (cdr ad-list) (list 'CDR x) (list 'CDR y)))
        (t (equal-evad-compose-ad-hint (cdr ad-list) x y))))

(defthm equal-evad-compose-ad
  (implies (equal (evad x alist)
                  (evad y alist))
           (equal (equal (evad (compose-ad ad-list x) alist)
                         (evad (compose-ad ad-list y) alist))
                  t))
  :hints (("Goal" :induct (equal-evad-compose-ad-hint ad-list x y))))


; It would be nice if the above could be a congruence rule but unfortunately
; the equivalence relation is not dyadic.

(in-theory (disable mv-nth))

(defthm compose-ac-append
  (equal (compose-ad (append a b) base)
         (compose-ad b (compose-ad a base))))



;-----------------------------------------------------------------
; The Proof

(defthm make-reversed-ad-list-spec
  (implies (ad-listp ans)
           (and (implies ans (mv-nth 0 (make-reversed-ad-list term ans)))
                (implies (not (mv-nth 0 (make-reversed-ad-list term ans)))
                         (equal (mv-nth 1 (make-reversed-ad-list term ans)) term))
                (ad-listp (mv-nth 0 (make-reversed-ad-list term ans)))
                (equal (evad (compose-ad (mv-nth 0 (make-reversed-ad-list term ans))
                                         (mv-nth 1 (make-reversed-ad-list term ans)))
                             alist)
                       (evad (compose-ad ans term) alist)))))

; The inductive part of the proof that pretty-parse-ad-list is correct is for
; the case when adr-list is actually just a dr-listp.  The case where adr-list
; is an adr-listp is just a case split away.

(defthm dr-listp-len-1-rev
  (implies (and (dr-listp dr-list)
                (equal (len dr-list) 1))
           (equal (rev dr-list) '(#\R))))

(defthm car-cdr-abbrev-name-adr-list-not-quote
   (implies (and (adr-listp adr-list)
;                 (<= 2 (len adr-list)) ; !!!
                 (<= (len adr-list) 5))
            (not (equal (car-cdr-abbrev-name adr-list) 'quote)))
   :hints (("Goal" :use enumerate-adr-listps)))

(defthm car-cdr-abbrev-name-dr-list-not-quote
   (implies (and (dr-listp adr-list)
;                 (<= 2 (len adr-list)) ; !!!
                 (<= (len adr-list) 5))
            (not (equal (car-cdr-abbrev-name adr-list) 'quote)))
   :hints (("Goal" :use enumerate-dr-listps)))

(defun evad-pretty-parse-ad-list-hint (ad-list dr-list n x y)
  (declare (xargs :measure (llist (acl2-count ad-list) (nfix n))
                  :well-founded-relation l<))
  (cond
   ((eql n 5)
    (evad-pretty-parse-ad-list-hint
     ad-list '(#\R)
     1
     (list (car-cdr-abbrev-name dr-list)
           x)
     (list (car-cdr-abbrev-name dr-list)
           y)))
   ((endp ad-list)
    (list x y))
   ((eql (car ad-list) #\A)
    (evad-pretty-parse-ad-list-hint
     (cdr ad-list)
     '(#\R)
     1
     (list (car-cdr-abbrev-name (cons #\A dr-list))
           x)
     (list (car-cdr-abbrev-name (cons #\A dr-list))
           y)))
   (t (evad-pretty-parse-ad-list-hint
       (cdr ad-list)
       (cons #\D dr-list)
       (+ 1 n)
       x
       y))))

(defthm evad-pretty-parse-ad-list
  (implies (and (equal (evad x alist)
                       (evad y alist))
                (ad-listp ad-list)
                (dr-listp dr-list)
                (equal (len dr-list) n)
                (<= 1 n)
                (<= n 5))
           (equal (equal (evad (pretty-parse-ad-list ad-list dr-list n x) alist)
                         (evad (pretty-parse-ad-list ad-list dr-list n y) alist))
                  t))
  :hints (("Goal" :induct (evad-pretty-parse-ad-list-hint ad-list dr-list n x y))
          ("Subgoal *1/2'''" :in-theory (enable evad-constraint-0))
          ("Subgoal *1/1''"  :in-theory (enable evad-constraint-0))))

; By the way, evad-constraint-0, enabled above, allows us to evad (fn x ...)
; for any fn other than QUOTE, expressing the answer in terms of the evads of
; the x....

(encapsulate
 nil
 (local (defun compose-d (lst base)
          (cond ((endp lst) base)
                ((eql (car lst) #\R) (compose-d (cdr lst) base))
                (t (list 'cdr (compose-d (cdr lst) base))))))

 (local
  (defthm compose-d-lemma1
    (implies (dr-listp dr-list)
             (equal (compose-ad dr-list base)
                    (compose-d dr-list base)))
    :hints (("Goal" :induct (compose-ad dr-list base)))))

 (local
  (defthm compose-d-lemma2
    (implies (dr-listp dr-list)
             (equal (compose-ad (rev dr-list) base)
                    (compose-d dr-list base)))))

 (defthm rev-dr-list-is-no-op
   (implies (dr-listp dr-list)
            (equal (compose-ad (rev dr-list) base)
                   (compose-ad dr-list base)))))

(defthm pretty-parse-ad-list-spec
  (implies (and (ad-listp ad-list)
                (dr-listp dr-list)
                (equal (len dr-list) n)
                (<= 1 n)
                (<= n 5))
           (equal (evad (pretty-parse-ad-list ad-list dr-list n base) alist)
                  (evad (compose-ad ad-list (compose-ad (rev dr-list) base)) alist)))
  :hints (("Goal" :induct (pretty-parse-ad-list ad-list dr-list n base))
          ("Subgoal *1/3'''" :use enumerate-dr-listps)
          ("Subgoal *1/1" :use enumerate-dr-listps)))

(defthm untranslate-car-cdr-nest-correct
  (equal (evad term alist)
         (evad (untranslate-car-cdr-nest term) alist))
  :rule-classes nil)
