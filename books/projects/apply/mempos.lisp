; Copyright (C) 2019, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)

; This book rewrites
; (member-equal newvar lst)
; to
; (< (mempos newvar lst) (len lst))

; and provides lemmas about mempos comparable to those about member-equal in
; projects/apply/loop.lisp.

; More interestingly, perhaps, it deals with the so-called ``correspondence
; problem'' for loop$s involving multiple iteration variables.  Consider the
; special loop$ guard conjectures for something like

; (loop$ x1 in t1 as x2 in t2 as x3 in t3 ...)

; The special guard conjectures introduce the hypothesis

; (member-equal newvar (loop$-as (list t1 t2 t3 ...)))

; Newvar represents the values of the iteration variables, x1, x2, x3, ...,
; at an arbitrary point in the scan down the targets.  It is easy to show
; that the member-equal above implies:

; (member-equal (car newvar) t1)   ; x1 is in t1
; (member-equal (cadr newvar) t2)  ; x2 is in t2
; (member-equal (caddr newvar) t3) ; x3 is in t3
; ...

; These facts might be needed to prove guards or type specs on the iteration
; variables from guards on their respective targets.  They are proved
; in books/projects/apply/loop.lisp.

; But the user might need the stronger fact that the value of x1, x2, x3, ...,
; are in correspondence with the elements of t1, t2, t3, ...

; The following encapsulate exports a rewrite rule, named mempos-correspondence
; that rewrites the (member-equal newvar (loop$-as (list t1 ... ))) into the
; salient facts the components of newvar.  However, it only handles the first
; three cases, for (list t1), (list t1 t2), and (list t1 t2 t3).

; Note: Other cases can easily be proved from within the encapsulate, following
; the proof pattern shown by cases 1, 2, and 3.  But we thought they are not
; likely to be needed.  A comment just before mempos-correspondence explains
; how to handle the case for 4.

; The ``salient facts,'' say for the case of (list t1 t2), are
; (1) (< (mempos newvar (loop$-as (list t1 t2)))
;        (len (loop$-as (list t1 t2))))

; (2) (true-listp newvar)
; (3) (equal (len newvar) 2)

; (4) (<= (mempos newvar (loop$-as (list t1 t2))) (len t1))
; (5) (<= (mempos newvar (loop$-as (list t1 t2))) (len t2))

; (6) (equal (car newvar)
;            (nth (mempos newvar (loop$-as (list t1 t2))) t1))
; (7) (equal (cadr newvar)
;            (nth (mempos newvar (loop$-as (list t1 t2))) t2))

; To explain these facts, let m be the mempos expression,

; (mempos newvar (loop$-as (list t1 t2)))

; which is known to be a natp.

; Fact (1) is equivalent to the original member-equal and is here just to
; preserve that hypothesis -- albeit in a somewhat awkward form -- without
; sending the rewriter into a loop.  Facts (2) and (3) state the basic shape of
; newvar.  Facts (4) and (5) establish that m is a legal index into the two
; component targets, t1 and t2.  Finally, facts (6) and (7) show that the car
; and cadr of newvar are in fact corresponding elements of t1 and t2
; respectively.  In particular, they are both at position m in their respective
; component targets.

(encapsulate nil
  (local
   (defthm len-nth-cdr-loop$-as-tuple
     (implies (and (natp n)
                   (< n (len tuple))
                   (CONSP TUPLE)
                   (NOT (EMPTY-LOOP$-AS-TUPLEP TUPLE)))
              (< (LEN (NTH N (CDR-LOOP$-AS-TUPLE TUPLE)))
                 (len (nth n tuple))))
     :rule-classes :linear))

  (local
   (defthm len-loop$-as-v-len-component
     (implies (and (natp n)
                   (< n (len tuple)))
              (<= (len (loop$-as tuple)) (len (nth n tuple))))
     :rule-classes :linear))

  (local
   (defun nth-loop$-as (n tuple)
     (cond ((endp tuple) nil)
           ((empty-loop$-as-tuplep tuple) nil)
           ((zp n) (car-loop$-as-tuple tuple))
           (t (nth-loop$-as (- n 1) (cdr-loop$-as-tuple tuple))))))

  (local
   (defthm nth-loop$-as-lemma
     (implies  (and (natp m)
                    (< m (len (loop$-as tuple))))
               (equal (nth m (loop$-as tuple))
                      (nth-loop$-as m tuple)))))

  (local
   (defthm nth-car-loop$-as-tuple
     (implies (and (natp n)
                   (< n (len tuple)))
              (equal (nth n (car-loop$-as-tuple tuple))
                     (car (nth n tuple))))))

  (local
   (defthm nth-cdr-loop$-as-tuple
     (implies (and (natp n)
                   (< n (len tuple)))
              (equal (nth n (cdr-loop$-as-tuple tuple))
                     (cdr (nth n tuple))))))

  (local
   (defthm nth-nth-loop$-as
     (implies (and (natp n)
                   (natp m)
                   (< n (len tuple))
                   (< m (len (loop$-as tuple))))
              (equal (nth n (nth m (loop$-as tuple)))
                     (nth m (nth n tuple))))
     :rule-classes nil))

  (local
   (defthm member-equal-is-<-mempos-len
     (iff (member-equal newvar target)
          (< (mempos newvar target) (len target))))
;     :rule-classes nil))
   )
  (local
   (defthm mempos-basic
     (implies (< (mempos newvar target) (len target))
              (equal (nth (mempos newvar target) target) newvar))))


  (local
   (defthm member-equal-loop$-as-1
     (iff (member-equal newvar (loop$-as (list t1)))
          (and (< (mempos newvar (loop$-as (list t1)))
                  (len (loop$-as (list t1))))
               (equal (car newvar)
                      (nth (mempos newvar (loop$-as (list t1))) t1))))
     :hints
     (("Goal"
       :use (;(:instance member-equal-is-<-mempos-len
             ;           (target (loop$-as (list t1))))
             (:instance nth-nth-loop$-as
                        (n 0)
                        (m (mempos newvar (loop$-as (list t1))))
                        (tuple (list t1))))))))
  (local
   (defthm member-equal-loop$-as-2
     (iff (member-equal newvar (loop$-as (list t1 t2)))
          (and (< (mempos newvar (loop$-as (list t1 t2)))
                  (len (loop$-as (list t1 t2))))
               (equal (car newvar)
                      (nth (mempos newvar (loop$-as (list t1 t2))) t1))
               (equal (cadr newvar)
                      (nth (mempos newvar (loop$-as (list t1 t2))) t2))))
     :hints
     (("Goal"
       :use (;(:instance member-equal-is-<-mempos-len
             ;           (target (loop$-as (list t1 t2))))
             (:instance nth-nth-loop$-as
                        (n 0)
                        (m (mempos newvar (loop$-as (list t1 t2))))
                        (tuple (list t1 t2)))
             (:instance nth-nth-loop$-as
                        (n 1)
                        (m (mempos newvar (loop$-as (list t1 t2))))
                        (tuple (list t1 t2))))))))

  (local
   (defthm member-equal-loop$-as-3
     (iff (member-equal newvar (loop$-as (list t1 t2 t3)))
          (and (< (mempos newvar (loop$-as (list t1 t2 t3)))
                  (len (loop$-as (list t1 t2 t3))))
               (equal (car newvar)
                      (nth (mempos newvar (loop$-as (list t1 t2 t3))) t1))
               (equal (cadr newvar)
                      (nth (mempos newvar (loop$-as (list t1 t2 t3))) t2))
               (equal (caddr newvar)
                      (nth (mempos newvar (loop$-as (list t1 t2 t3))) t3))))
     :hints
     (("Goal"
       :use (;(:instance member-equal-is-<-mempos-len
             ;           (target (loop$-as (list t1 t2 t3))))
             (:instance nth-nth-loop$-as
                        (n 0)
                        (m (mempos newvar (loop$-as (list t1 t2 t3))))
                        (tuple (list t1 t2 t3)))
             (:instance nth-nth-loop$-as
                        (n 1)
                        (m (mempos newvar (loop$-as (list t1 t2 t3))))
                        (tuple (list t1 t2 t3)))
             (:instance nth-nth-loop$-as
                        (n 2)
                        (m (mempos newvar (loop$-as (list t1 t2 t3))))
                        (tuple (list t1 t2 t3))))))))

  (local
   (defthm mempos-loop$-as-basics
     (implies (< (mempos newvar (loop$-as tuple))
                 (len (loop$-as tuple)))
              (and (true-listp newvar)
                   (equal (len newvar) (len tuple))))
     :hints (("Goal" :induct (loop$-as tuple)))))

  (local
   (defthm len-loop$-as-<-len-1
     (<= (len (loop$-as (list t1))) (len t1))
     :rule-classes :linear))

  (local
   (defthm len-loop$-as-<-len-2
     (and (<= (len (loop$-as (list t1 t2))) (len t1))
          (<= (len (loop$-as (list t1 t2))) (len t2)))
     :hints (("Goal" :induct (pairlis$ t1 t2)))
     :rule-classes :linear))

  (local
   (defthm len-loop$-as-<-len-3
     (and (<= (len (loop$-as (list t1 t2 t3))) (len t1))
          (<= (len (loop$-as (list t1 t2 t3))) (len t2))
          (<= (len (loop$-as (list t1 t2 t3))) (len t3)))
     :hints (("Goal" :induct (list (pairlis$ t1 t2)
                                   (pairlis$ t2 t3))))
     :rule-classes :linear))

; Note: To handle the case of (list t1 t2 t3 t4) you'll have to prove the
; ``4-version'' of member-equal-loop$-as-3, providing the 4-version of the
; hint, and you have to prove the 4-version of len-loop$-as-<-len-3, providing
; the 4-version of its hint.  Then :use the new member-equal-loop$-as-4 to
; prove the 4-version of the rewrite rule for (member-equal newvar (loop$-as
; ...)), as done below for the 1-, 2-, and 3-versions.

  (defthm mempos-correspondence ; for cases 0,1,2, and 3
    (and (implies (syntaxp (not (and (consp lst)
                                     (eq (car lst) 'LOOP$-AS))))
                  (iff (member-equal newvar lst)
                       (< (mempos newvar lst) (len lst))))
         (iff (member-equal newvar (loop$-as (list t1)))
              (and (< (mempos newvar (loop$-as (list t1)))
                      (len (loop$-as (list t1))))
                   (true-listp newvar)
                   (equal (len newvar) 1)
                   (<= (mempos newvar (loop$-as (list t1))) (len t1))
                   (equal (car newvar)
                          (nth (mempos newvar (loop$-as (list t1))) t1))))
         (iff (member-equal newvar (loop$-as (list t1 t2)))
              (and (< (mempos newvar (loop$-as (list t1 t2)))
                      (len (loop$-as (list t1 t2))))
                   (true-listp newvar)
                   (equal (len newvar) 2)
                   (<= (mempos newvar (loop$-as (list t1 t2))) (len t1))
                   (<= (mempos newvar (loop$-as (list t1 t2))) (len t2))
                   (equal (car newvar)
                          (nth (mempos newvar (loop$-as (list t1 t2))) t1))
                   (equal (cadr newvar)
                          (nth (mempos newvar (loop$-as (list t1 t2))) t2))))
         (iff (member-equal newvar (loop$-as (list t1 t2 t3)))
              (and (< (mempos newvar (loop$-as (list t1 t2 t3)))
                      (len (loop$-as (list t1 t2 t3))))
                   (true-listp newvar)
                   (equal (len newvar) 3)
                   (<= (mempos newvar (loop$-as (list t1 t2 t3))) (len t1))
                   (<= (mempos newvar (loop$-as (list t1 t2 t3))) (len t2))
                   (<= (mempos newvar (loop$-as (list t1 t2 t3))) (len t3))
                   (equal (car newvar)
                          (nth (mempos newvar (loop$-as (list t1 t2 t3))) t1))
                   (equal (cadr newvar)
                          (nth (mempos newvar (loop$-as (list t1 t2 t3))) t2))
                   (equal (caddr newvar)
                          (nth (mempos newvar (loop$-as (list t1 t2 t3))) t3))))))

  )

(defthm len-when$
  (<= (len (when$ p lst)) (len lst))
  :rule-classes :linear)

(defthm len-until$
  (<= (len (until$ q lst)) (len lst))
  :rule-classes :linear)

(defthm mempos-when$
  (iff (< (mempos e (when$ p lst))
          (len (when$ p lst)))
       (and (< (mempos e lst) (len lst))
            (apply$ p (list e)))))

(defthm mempos-until$
  (equal (mempos newv (until$ q lst))
         (if (< (mempos newv lst)
                (len (until$ q lst)))
             (mempos newv lst)
             (len (until$ q lst)))))

; For fancy loop$s

(defthm len-when$+
  (<= (len (when$+ p pglob lst)) (len lst))
  :rule-classes :linear)

(defthm len-until$+
  (<= (len (until$+ q qglob lst)) (len lst))
  :rule-classes :linear)

(defthm len-loop$-as-car
  (implies (consp tuple)
           (<= (len (loop$-as tuple))
               (len (car tuple))))
  :rule-classes :linear)

(defthm len-loop$-as-cadr
  (implies (consp (cdr tuple))
           (<= (len (loop$-as tuple))
               (len (cadr tuple))))
  :rule-classes :linear)

(defthm mempos-when$+
  (iff (< (mempos e (when$+ p pglob lst)) (len (when$+ p pglob lst)))
       (and
        (< (mempos e lst) (len lst))
        (apply$ p (list pglob e)))))

(defthm mempos-until$+
  (equal (mempos newv (until$+ q qglob lst))
         (if (< (mempos newv lst)
                (len (until$+ q qglob lst)))
             (mempos newv lst)
             (len (until$+ q qglob lst)))))

; -----------------------------------------------------------------

; Universal Quantifier Instantiation Machinery 
;  -- Deducing Properties of Elements from Properties of Lists

; A crucial part of reasoning about loop$ guards is deducing properties of the
; elements of a list from properties of the list, e.g., if newv is an element
; of lst and lst is a list of numbers, then newv is a number.  For want of a
; better name we call this ``universal quantifier instantiation'' or ``uqi''.
; In general we tackle uqi by looking at (always$ fn lst) and deducing (fn
; newv).  Rather than setting up backchaining rules (which are too fragile
; because a property may have many rewritable parts and each would need a
; rule), or forward chaining rules (which suffer from leaving the deductions
; invisible to the user and to the rewriter) we actually will insert the
; deduction into the conjecture with a rewrite that ``eliminates'' the
; quantifier but hides it to maintain equality.

; There are some commonly used legacy ``implicit always$ loops'' expressed with
; recursion.  We build them into our handling of extraction.

; integer-listp --> integerp
; rational-listp --> rationalp
; acl2-number-listp --> acl2-numberp
; symbol-listp --> symbolp
; true-list-listp --> true-listp

; We need to formalize these basic facts:

; integer-listp --> integerp
(defthm mempos-integer-listp-implies-integerp
  (implies (and (< (mempos newv lst) (len lst))
                (integer-listp lst))
           (integerp newv)))

; rational-listp --> rationalp
(defthm mempos-rational-listp-implies-rationalp
  (implies (and (< (mempos newv lst) (len lst))
                (rational-listp lst))
           (rationalp newv)))

; acl2-number-listp --> acl2-numberp
(defthm mempos-acl2-number-listp-implies-acl2-numberp
  (implies (and (< (mempos newv lst) (len lst))
                (acl2-number-listp lst))
           (acl2-numberp newv)))

; symbol-listp --> symbolp
(defthm mempos-symbol-listp-implies-symbolp
  (implies (and (< (mempos newv lst) (len lst))
                (symbol-listp lst))
           (symbolp newv)))

; true-list-listp --> true-listp
(defthm mempos-true-list-listp-implies-true-listp
  (implies (and (< (mempos newv lst) (len lst))
                (true-list-listp lst))
           (true-listp newv)))

; And the general rule:

(defthm mempos-always$-p-lst-implies-p-element
  (implies (and (always$ fnp lst)
                (< (mempos newv lst) (len lst)))
           (apply$ fnp (list newv))))

; NOTE: These rules will have to be disabled after we've set up the rest of this
; machinery!  See the

; (in-theory (disable integerp-listp-implies-integerp
;                     ...))

; below!


; We don't want the plain-uqi lemmas firing on (mempos newv (LOOP$-AS ...)) so
; we intall a syntaxp hyp on each.

(defthm mempos-plain-uqi-always$
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ fnp lst)
                (<= xxx (len lst))
                (not (apply$ fnp (list newv))))
           (not (< (mempos newv lst) xxx))))

; (defthm integer-listp-implies-always$-integerp
;   (implies (integer-listp lst)
;            (always$ 'integerp lst)))

(defthm mempos-plain-uqi-integer-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'integerp lst)
                (<= xxx (len lst))
                (not (apply$ 'integerp (list newv))))
           (not (< (mempos newv lst) xxx))))

; (defthm rational-listp-implies-always$-rationalp
;   (implies (rational-listp lst)
;            (always$ 'rationalp lst)))

(defthm mempos-plain-uqi-rational-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'rationalp lst)
                (<= xxx (len lst))
                (not (apply$ 'rationalp (list newv))))
           (not (< (mempos newv lst) xxx))))

; (defthm acl2-number-listp-implies-always$-acl2-numberp
;   (implies (acl2-number-listp lst)
;            (always$ 'acl2-numberp lst)))

(defthm mempos-plain-uqi-acl2-number-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'acl2-numberp lst)
                (<= xxx (len lst))
                (not (apply$ 'acl2-numberp (list newv))))
           (not (< (mempos newv lst) xxx))))

; (defthm symbol-listp-implies-always$-symbolp
;   (implies (symbol-listp lst)
;            (always$ 'symbolp lst)))

(defthm mempos-plain-uqi-symbol-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'symbolp lst)
                (<= xxx (len lst))
                (not (apply$ 'symbolp (list newv))))
           (not (< (mempos newv lst) xxx))))

; (defthm true-list-listp-implies-always$-true-listp
;   (implies (true-list-listp lst)
;            (always$ 'true-listp lst)))

(defthm mempos-plain-uqi-true-list-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'true-listp lst)
                (<= xxx (len lst))
                (not (apply$ 'true-listp (list newv))))
           (not (< (mempos newv lst) xxx))))

(defthm mempos-plain-uqi-rational-list-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'rational-listp lst)
                (<= xxx (len lst))
                (not (apply$ 'rational-listp (list newv))))
           (not (< (mempos newv lst) xxx))))


; That takes care of all the plain cases.  Now we work on LOOP$-AS

(encapsulate
  nil
  (local (defthm mempos-nth-car-loop$-as-tuple
           (implies (and (CONSP TUPLE)
                         (NOT (EMPTY-LOOP$-AS-TUPLEP TUPLE))
                         (natp n)
                         (< n (len tuple)))
                    (< (mempos (NTH N (CAR-LOOP$-AS-TUPLE TUPLE))
                               (NTH N TUPLE))
                       (len (NTH N TUPLE))))))

  (local (defthm mempos-nth-cdr-loop$-as-tuple
           (implies (and (CONSP TUPLE)
                         (NOT (EMPTY-LOOP$-AS-TUPLEP TUPLE))
                         (< (mempos (NTH N NEWV)
                                    (NTH N (CDR-LOOP$-AS-TUPLE TUPLE)))
                            (len (NTH N (CDR-LOOP$-AS-TUPLE TUPLE)))))
                    (< (mempos (nth n newv) (nth n tuple))
                       (len (nth n tuple))))))

  (local (defthm mempos-loop$-as-implies-mempos-nth
           (implies (and (< (mempos newv (loop$-as tuple))
                            (len (loop$-as tuple)))
                         (natp n)
                         (< n (len tuple)))
                    (< (mempos (nth n newv) (nth n tuple))
                       (len (nth n tuple))))))

  (defthm mempos-general-always$-nth-loop$-as-tuple
    (implies (and (always$ fnp (nth n tuple))
                  (not (apply$ fnp (list (nth n newv))))
                  (natp n)
                  (< n (len tuple)))
             (not (< (mempos newv (loop$-as tuple))
                     (len (loop$-as tuple)))))
    :rule-classes nil))

(defthm mempos-fancy-uqi-always$-1
  (implies (and (always$ fnp lst1)
                (not (apply$ fnp (list (car newv)))))
           (not (< (mempos newv (loop$-as (cons lst1 rest)))
                   (len (loop$-as (cons lst1 rest))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm mempos-fancy-uqi-always$-2
  (implies (and (always$ fnp lst2)
                (not (apply$ fnp (list (cadr newv)))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest))))
                   (len (loop$-as (cons lst1 (cons lst2 rest)))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm mempos-fancy-uqi-always-3
  (implies (and (always$ fnp lst3)
                (not (apply$ fnp (list (caddr newv)))))
           (not (< (mempos newv (loop$-as
                                 (cons lst1 (cons lst2 (cons lst3 rest)))))
                   (len (loop$-as
                         (cons lst1 (cons lst2 (cons lst3 rest))))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                                  (n 2)))))

(defthm mempos-fancy-uqi-integer-1
  (implies (and (integer-listp lst1)
                (not (integerp (car newv))))
           (not (< (mempos newv (loop$-as (cons lst1 rest)))
                   (len (loop$-as (cons lst1 rest))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'integerp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm mempos-fancy-uqi-integer-2
  (implies (and (integer-listp lst2)
                (not (integerp (cadr newv))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest))))
                   (len (loop$-as (cons lst1 (cons lst2 rest)))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'integerp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm mempos-fancy-uqi-integer-3
  (implies (and (integer-listp lst3)
                (not (integerp (caddr newv))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest))))))))
  :hints (("Goal" :use (:instance
                        mempos-general-always$-nth-loop$-as-tuple
                        (fnp 'integerp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm mempos-fancy-uqi-rational-1
  (implies (and (rational-listp lst1)
                (not (rationalp (car newv))))
           (not (< (mempos newv (loop$-as (cons lst1 rest)))
                   (len (loop$-as (cons lst1 rest))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'rationalp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm mempos-fancy-uqi-rational-2
  (implies (and (rational-listp lst2)
                (not (rationalp (cadr newv))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest))))
                   (len (loop$-as (cons lst1 (cons lst2 rest)))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'rationalp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm mempos-fancy-uqi-rational-3
  (implies (and (rational-listp lst3)
                (not (rationalp (caddr newv))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest))))))))
  :hints (("Goal" :use (:instance
                        mempos-general-always$-nth-loop$-as-tuple
                        (fnp 'rationalp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm mempos-fancy-uqi-acl2-number-1
  (implies (and (acl2-number-listp lst1)
                (not (acl2-numberp (car newv))))
           (not (< (mempos newv (loop$-as (cons lst1 rest)))
                   (len (loop$-as (cons lst1 rest))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'acl2-numberp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm mempos-fancy-uqi-acl2-number-2
  (implies (and (acl2-number-listp lst2)
                (not (acl2-numberp (cadr newv))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest))))
                   (len (loop$-as (cons lst1 (cons lst2 rest)))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'acl2-numberp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm mempos-fancy-uqi-acl2-number-3
  (implies (and (acl2-number-listp lst3)
                (not (acl2-numberp (caddr newv))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest))))))))
  :hints (("Goal" :use (:instance
                        mempos-general-always$-nth-loop$-as-tuple
                        (fnp 'acl2-numberp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm mempos-fancy-uqi-symbol-1
  (implies (and (symbol-listp lst1)
                (not (symbolp (car newv))))
           (not (< (mempos newv (loop$-as (cons lst1 rest)))
                   (len (loop$-as (cons lst1 rest))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'symbolp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm mempos-fancy-uqi-symbol-2
  (implies (and (symbol-listp lst2)
                (not (symbolp (cadr newv))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest))))
                   (len (loop$-as (cons lst1 (cons lst2 rest)))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'symbolp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm mempos-fancy-uqi-symbol-3
  (implies (and (symbol-listp lst3)
                (not (symbolp (caddr newv))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest))))))))
  :hints (("Goal" :use (:instance
                        mempos-general-always$-nth-loop$-as-tuple
                        (fnp 'symbolp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm mempos-fancy-uqi-true-list-1
  (implies (and (true-list-listp lst1)
                (not (true-listp (car newv))))
           (not (< (mempos newv (loop$-as (cons lst1 rest)))
                   (len (loop$-as (cons lst1 rest))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'true-listp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm mempos-fancy-uqi-true-list-2
  (implies (and (true-list-listp lst2)
                (not (true-listp (cadr newv))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest))))
                   (len (loop$-as (cons lst1 (cons lst2 rest)))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'true-listp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm mempos-fancy-uqi-true-list-3
  (implies (and (true-list-listp lst3)
                (not (true-listp (caddr newv))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest))))))))
  :hints (("Goal" :use (:instance
                        mempos-general-always$-nth-loop$-as-tuple
                        (fnp 'true-listp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm mempos-structure-of-loop$-as-elements
  (implies (< (mempos newv (loop$-as tuple))
              (len (loop$-as tuple)))
           (and (true-listp newv)
                (equal (len newv) (len tuple))))
  :hints (("Goal" :induct (loop$-as tuple)))
  :rule-classes nil)

(defthm mempos-structure-of-loop$-as-elements-bridge
  (and (implies (not (true-listp newv))
                (not (< (mempos newv (loop$-as tuple))
                        (len (loop$-as tuple)))))
       (implies (not (equal (len newv) (len tuple)))
                (not (< (mempos newv (loop$-as tuple))
                        (len (loop$-as tuple))))))
  :hints (("Goal" :use mempos-structure-of-loop$-as-elements)))

(defthm mempos-fancy-uqi-rational-listp-1
  (implies (and (always$ 'rational-listp lst1)
                (not (rational-listp (car newv))))
           (not (< (mempos newv (loop$-as (cons lst1 rest)))
                   (len (loop$-as (cons lst1 rest))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'rational-listp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm mempos-fancy-uqi-rational-listp-2
  (implies (and (always$ 'rational-listp lst2)
                (not (rational-listp (cadr newv))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest))))
                   (len (loop$-as (cons lst1 (cons lst2 rest)))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'rational-listp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm mempos-fancy-uqi-rational-listp-3
  (implies (and (always$ 'rational-listp lst3)
                (not (rational-listp (caddr newv))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest))))))))
  :hints (("Goal" :use (:instance
                        mempos-general-always$-nth-loop$-as-tuple
                        (fnp 'rational-listp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm mempos-fancy-uqi-identity-1
  (implies (and (always$ 'identity lst1)
                (not (car newv)))
           (not (< (mempos newv (loop$-as (cons lst1 rest)))
                   (len (loop$-as (cons lst1 rest))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'identity)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm mempos-fancy-uqi-identity-2
  (implies (and (always$ 'identity lst2)
                (not (cadr newv)))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest))))
                   (len (loop$-as (cons lst1 (cons lst2 rest)))))))
  :hints (("Goal" :use (:instance mempos-general-always$-nth-loop$-as-tuple
                                  (fnp 'identity)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm mempos-fancy-uqi-identity-3
  (implies (and (always$ 'identity lst3)
                (not (caddr newv)))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest))))))))
  :hints (("Goal" :use (:instance
                        mempos-general-always$-nth-loop$-as-tuple
                        (fnp 'identity)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

; These plain-uqi lemmas were left out above...

(defthm mempos-general-plain-uqi-integer-listp-tails
  (implies (and (integer-listp lst)
                (not (integer-listp newv)))
           (not (< (mempos newv (tails lst))
                   (len (tails lst)))))
  :rule-classes nil)

(defthm mempos-plain-uqi-integer-listp-tails
  (implies (and (integer-listp lst)
                (not (integer-listp newv)))
           (not (< (mempos newv (tails lst))
                   (len (tails lst)))))
  :hints (("Goal" :use mempos-general-plain-uqi-integer-listp-tails)))

