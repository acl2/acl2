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

; (DEFTHM EVAD-CONSTRAINT-10
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

(encapsulate
 (((evad * *) => *)
  ((evad-lst * *) => *))
 (set-inhibit-warnings "theory")
 (local (in-theory *defevaluator-form-base-theory*))
 (local (mutual-recursion
         (defun-nx evad (x a)
           (declare (xargs :verify-guards nil
                           :measure (acl2-count x)
                           :well-founded-relation o<
                           :mode :logic))
           (cond ((symbolp x)
                  (and x (cdr (assoc-eq x a))))
                 ((atom x) nil)
                 ((eq (car x) 'quote) (car (cdr x)))
                 ((consp (car x))
                  (evad (car (cdr (cdr (car x))))
                        (pairlis$ (car (cdr (car x)))
                                  (evad-lst (cdr x) a))))
                 ((equal (car x) 'car)
                  (car (evad (car (cdr x)) a)))
                 ((equal (car x) 'cdr)
                  (cdr (evad (car (cdr x)) a)))
                 ((equal (car x) 'cadr)
                  (cadr (evad (car (cdr x)) a)))
                 ((equal (car x) 'cddr)
                  (cddr (evad (car (cdr x)) a)))
                 ((equal (car x) 'caddr)
                  (caddr (evad (car (cdr x)) a)))
                 ((equal (car x) 'cdddr)
                  (cdddr (evad (car (cdr x)) a)))
                 ((equal (car x) 'cadddr)
                  (cadddr (evad (car (cdr x)) a)))
                 ((equal (car x) 'cddddr)
                  (cddddr (evad (car (cdr x)) a)))
                 (t nil)))
         (defun-nx evad-lst (x-lst a)
           (declare (xargs :measure (acl2-count x-lst)
                           :well-founded-relation o<))
           (cond ((endp x-lst) nil)
                 (t (cons (evad (car x-lst) a)
                          (evad-lst (cdr x-lst) a)))))))
 (local (defthm eval-list-kwote-lst
          (equal (evad-lst (kwote-lst args) a)
                 (fix-true-list args))))
 (defthmd
   evad-constraint-0
   (implies (and (consp x)
                 (syntaxp (not (equal a ''nil)))
                 (not (equal (car x) 'quote)))
            (equal (evad x a)
                   (evad (cons (car x)
                               (kwote-lst (evad-lst (cdr x) a)))
                         nil)))
   :hints
   (("Goal" :expand ((:free (x) (hide x)) (evad x a))
     :in-theory (disable (:executable-counterpart evad)))))
 (defthm evad-constraint-1
   (implies (symbolp x)
            (equal (evad x a)
                   (and x (cdr (assoc-equal x a))))))
 (defthm evad-constraint-2
   (implies (and (consp x) (equal (car x) 'quote))
            (equal (evad x a) (cadr x))))
 (defthm evad-constraint-3
   (implies (and (consp x) (consp (car x)))
            (equal (evad x a)
                   (evad (caddar x)
                         (pairlis$ (cadar x)
                                   (evad-lst (cdr x) a))))))
 (defthm evad-constraint-4
   (implies (not (consp x-lst))
            (equal (evad-lst x-lst a) nil)))
 (defthm evad-constraint-5
   (implies (consp x-lst)
            (equal (evad-lst x-lst a)
                   (cons (evad (car x-lst) a)
                         (evad-lst (cdr x-lst) a)))))
 (defthm evad-constraint-6
   (implies (and (consp x) (equal (car x) 'car))
            (equal (evad x a)
                   (car (evad (cadr x) a)))))
 (defthm evad-constraint-7
   (implies (and (consp x) (equal (car x) 'cdr))
            (equal (evad x a)
                   (cdr (evad (cadr x) a)))))
 (defthm evad-constraint-8
   (implies (and (consp x) (equal (car x) 'cadr))
            (equal (evad x a)
                   (cadr (evad (cadr x) a)))))
 (defthm evad-constraint-9
   (implies (and (consp x) (equal (car x) 'cddr))
            (equal (evad x a)
                   (cddr (evad (cadr x) a)))))
 (defthm evad-constraint-10
   (implies (and (consp x) (equal (car x) 'caddr))
            (equal (evad x a)
                   (caddr (evad (cadr x) a)))))
 (defthm evad-constraint-11
   (implies (and (consp x) (equal (car x) 'cdddr))
            (equal (evad x a)
                   (cdddr (evad (cadr x) a)))))
 (defthm evad-constraint-12
   (implies (and (consp x) (equal (car x) 'cadddr))
            (equal (evad x a)
                   (cadddr (evad (cadr x) a)))))
 (defthm evad-constraint-13
   (implies (and (consp x) (equal (car x) 'cddddr))
            (equal (evad x a)
                   (cddddr (evad (cadr x) a))))))

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
