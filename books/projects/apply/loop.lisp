; Copyright (C) 2019, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

(in-package "ACL2")

(include-book "base")
(include-book "system/apply/loop-scions" :dir :system)

; We don't need mempos warranted, but a user might.
(defun$ mempos (e lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) 0)
        ((equal e (car lst)) 0)
        (t (+ 1 (mempos e (cdr lst))))))

; Lemmas for Relieving Routine Loop$ Guards

; Preservation of true-list-listp

(defthm true-list-listp-tails
  (implies (true-listp lst)
           (true-list-listp (tails lst))))

(defthm true-list-listp-until$
  (implies (true-list-listp lst)
           (true-list-listp (until$ fn lst))))

(defthm true-list-listp-until$+
  (implies (true-list-listp lst)
           (true-list-listp (until$+ fn globals lst))))

(defthm true-list-listp-when$
  (implies (true-list-listp lst)
           (true-list-listp (when$ fn lst))))

(defthm true-list-listp-when$+
  (implies (true-list-listp lst)
           (true-list-listp (when$+ fn globals lst))))

; (defthm true-list-member-pos-true-list-listp
;   (implies (and (true-list-listp lst)
;                 (not (true-listp newv)))
;            (not (< (mempos newv lst) (len lst)))))

(defthm true-listp-car-loop$-as-tuple
  (implies (true-list-listp tuple)
           (true-listp (car-loop$-as-tuple tuple))))

(defthm len-car-loop$-as-tuple
  (equal (len (car-loop$-as-tuple tuple))
         (len tuple)))

(defthm len-cdr-loop$-as-tuple
  (equal (len (cdr-loop$-as-tuple tuple))
         (len tuple)))

(defthm true-list-listp-cdr-loop$-as-tuple
  (implies (true-list-listp tuple)
           (true-list-listp (cdr-loop$-as-tuple tuple))))

(defthm true-list-listp-loop$-as
  (implies (true-list-listp tuple)
           (true-list-listp (loop$-as tuple))))

(defthm len-mempos-loop$-as
  (implies (< (mempos newv (loop$-as tuple)) (len (loop$-as tuple)))
           (equal (len newv) (len tuple)))
  :hints (("Goal" :induct (loop$-as tuple))))

; Preservation of integer-listp

(defthm integer-listp-from-to-by
  (implies (and (integerp i)
                (integerp k))
           (integer-listp (from-to-by i j k))))

(defthm integer-listp-until$
  (implies (integer-listp lst)
           (integer-listp (until$ fn lst))))

(defthm integer-listp-when$
  (implies (integer-listp lst)
           (integer-listp (when$ fn lst))))

; Preservation of member-posship
#||

(defthm member-pos-until$
  (implies (not (member-pos newv lst))
           (not (member-pos newv (until$ fn lst)))))

(defthm member-pos-until$+
  (implies (not (member-pos newv lst))
           (not (member-pos newv (until$+ fn globals lst)))))

(defthm member-pos-when$
  (implies (not (member-pos newv lst))
           (not (member-pos newv (when$ fn lst)))))

(defthm member-pos-when$+
  (implies (not (member-pos newv lst))
           (not (member-pos newv (when$+ fn globals lst)))))

(encapsulate
  nil
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm member-pos-from-to-by-exact
    (implies (and (integerp i)
                  (integerp j)
                  (integerp k)
                  (< 0 k))
             (iff (member-pos newv (from-to-by i j k))
                  (and (integerp newv)
                       (<= i newv)
                       (<= newv j)
                       (equal (mod (- newv i) k) 0)))))

  (in-theory (disable member-pos-from-to-by-exact)))

(defthm member-pos-from-to-by-weak
  (and
   (implies (and (integerp i)
                 (integerp j)
                 (integerp k)
                 (< 0 k)
                 (not (integerp newv)))
            (not (member-pos newv (from-to-by i j k))))
   (implies (and (integerp i)
                 (integerp j)
                 (integerp k)
                 (< 0 k)
                 (< newv i))
            (not (member-pos newv (from-to-by i j k))))
   (implies (and (integerp i)
                 (integerp j)
                 (integerp k)
                 (< 0 k)
                 (< j newv))
            (not (member-pos newv (from-to-by i j k))))))

(defthm member-pos-from-to-by-1
  (implies (and (integerp i)
                (integerp j))
           (iff (member-pos newv (from-to-by i j 1))
                (and (integerp newv)
                     (<= i newv)
                     (<= newv j)))))
||#
; -----------------------------------------------------------------

; Mempos rules

; For plain loop$s

(defthm len-when$
  (<= (len (when$ p lst)) (len lst))
  :rule-classes :linear)

(defthm len-until$
  (<= (len (until$ q lst)) (len lst))
  :rule-classes :linear)

(defthm mempos-when$
  (iff (< (mempos e (when$ p lst)) (len (when$ p lst)))
       (and
        (< (mempos e lst) (len lst))
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
        (apply$ p (list e pglob)))))

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
(defthm integer-listp-implies-integerp
  (implies (and (< (mempos newv lst) (len lst))
                (integer-listp lst))
           (integerp newv)))

; rational-listp --> rationalp
(defthm rational-listp-implies-rationalp
  (implies (and (< (mempos newv lst) (len lst))
                (rational-listp lst))
           (rationalp newv)))

; acl2-number-listp --> acl2-numberp
(defthm acl2-number-listp-implies-acl2-numberp
  (implies (and (< (mempos newv lst) (len lst))
                (acl2-number-listp lst))
           (acl2-numberp newv)))

; symbol-listp --> symbolp
(defthm symbol-listp-implies-symbolp
  (implies (and (< (mempos newv lst) (len lst))
                (symbol-listp lst))
           (symbolp newv)))

; true-list-listp --> true-listp
(defthm true-list-listp-implies-true-listp
  (implies (and (< (mempos newv lst) (len lst))
                (true-list-listp lst))
           (true-listp newv)))

; And the general rule:

(defthm always$-p-lst-implies-p-element
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

(defthm plain-uqi-always$
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ fnp lst)
                (<= xxx (len lst))
                (not (apply$ fnp (list newv))))
           (not (< (mempos newv lst) xxx))))

(defthm integer-listp-implies-always$-integerp
  (implies (integer-listp lst)
           (always$ 'integerp lst)))

(defthm plain-uqi-integer-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'integerp lst)
                (<= xxx (len lst))
                (not (apply$ 'integerp (list newv))))
           (not (< (mempos newv lst) xxx))))

(defthm rational-listp-implies-always$-rationalp
  (implies (rational-listp lst)
           (always$ 'rationalp lst)))

(defthm plain-uqi-rational-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'rationalp lst)
                (<= xxx (len lst))
                (not (apply$ 'rationalp (list newv))))
           (not (< (mempos newv lst) xxx))))

(defthm acl2-number-listp-implies-always$-acl2-numberp
  (implies (acl2-number-listp lst)
           (always$ 'acl2-numberp lst)))

(defthm plain-uqi-acl2-number-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'acl2-numberp lst)
                (<= xxx (len lst))
                (not (apply$ 'acl2-numberp (list newv))))
           (not (< (mempos newv lst) xxx))))

(defthm symbol-listp-implies-always$-symbolp
  (implies (symbol-listp lst)
           (always$ 'symbolp lst)))

(defthm plain-uqi-symbol-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'symbolp lst)
                (<= xxx (len lst))
                (not (apply$ 'symbolp (list newv))))
           (not (< (mempos newv lst) xxx))))

(defthm true-list-listp-implies-always$-true-listp
  (implies (true-list-listp lst)
           (always$ 'true-listp lst)))

(defthm plain-uqi-true-list-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'true-listp lst)
                (<= xxx (len lst))
                (not (apply$ 'true-listp (list newv))))
           (not (< (mempos newv lst) xxx))))

(defthm plain-uqi-rational-list-listp
  (implies (and (syntaxp (not (and (consp lst)
                                   (eq (car lst) 'LOOP$-AS))))
                (always$ 'rational-listp lst)
                (<= xxx (len lst))
                (not (apply$ 'rational-listp (list newv))))
           (not (< (mempos newv lst) xxx))))

; We need to know that the legacy quantifiers hold on constructors of the lists
; we target.

(defthm true-listp-make-list
  (implies (true-listp ac)
           (true-listp (make-list-ac n x ac))))

(defthm integer-listp-make-list-ac
  (implies (and (integer-listp ac)
                (integerp x))
           (integer-listp (make-list-ac n x ac))))

(defthm integer-listp-make-list
  (implies (and (integerp i)
                (integer-listp ac))
           (integer-listp (make-list-ac n i ac))))

(defthm acl2-number-listp-make-list
  (implies (and (acl2-numberp i)
                (acl2-number-listp ac))
           (acl2-number-listp (make-list-ac n i ac))))

(defthm  acl2-number-listp-from-to-by
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (< 0 k))
           (acl2-number-listp (from-to-by i j k))))

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
                         (< (MEMPOS (NTH N NEWV)
                                    (NTH N (CDR-LOOP$-AS-TUPLE TUPLE)))
                            (LEN (NTH N (CDR-LOOP$-AS-TUPLE TUPLE)))))
                    (< (mempos (nth n newv) (nth n tuple))
                       (len (nth n tuple))))))

  (local (defthm mempos-loop$-as-implies-mempos-nth
           (implies (and (< (mempos newv (loop$-as tuple))
                            (len (loop$-as tuple)))
                         (natp n)
                         (< n (len tuple)))
                    (< (mempos (nth n newv) (nth n tuple))
                       (len (nth n tuple))))))

  (defthm general-always$-nth-loop$-as-tuple
    (implies (and (always$ fnp (nth n tuple))
                  (not (apply$ fnp (list (nth n newv))))
                  (natp n)
                  (< n (len tuple)))
             (not (< (mempos newv (loop$-as tuple)) (len (loop$-as tuple)))))
    :rule-classes nil))

(defthm fancy-uqi-always$-1
  (implies (and (always$ fnp lst1)
                (not (apply$ fnp (list (car newv))))
                (<= xxx (len (loop$-as (cons lst1 rest)))))
           (not (< (mempos newv (loop$-as (cons lst1 rest))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm fancy-uqi-always$-2
  (implies (and (always$ fnp lst2)
                (not (apply$ fnp (list (cadr newv))))
                (<= xxx (len (loop$-as (cons lst1 (cons lst2 rest))))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest)))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm fancy-uqi-always-3
  (implies (and (always$ fnp lst3)
                (not (apply$ fnp (list (caddr newv))))
                (<= xxx
                    (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
           (not (< (mempos newv (loop$-as
                                 (cons lst1 (cons lst2 (cons lst3 rest)))))
                   xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                                  (n 2)))))

(defthm fancy-uqi-integer-1
  (implies (and (integer-listp lst1)
                (not (integerp (car newv)))
                (<= xxx (len (loop$-as (cons lst1 rest)))))
           (not (< (mempos newv (loop$-as (cons lst1 rest))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'integerp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm fancy-uqi-integer-2
  (implies (and (integer-listp lst2)
                (not (integerp (cadr newv)))
                (<= xxx (len (loop$-as (cons lst1 (cons lst2 rest))))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest)))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'integerp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm fancy-uqi-integer-3
  (implies (and (integer-listp lst3)
                (not (integerp (caddr newv)))
                (<= xxx
                    (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   xxx)))
  :hints (("Goal" :use (:instance
                        general-always$-nth-loop$-as-tuple
                        (fnp 'integerp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm fancy-uqi-rational-1
  (implies (and (rational-listp lst1)
                (not (rationalp (car newv)))
                (<= xxx (len (loop$-as (cons lst1 rest)))))
           (not (< (mempos newv (loop$-as (cons lst1 rest))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'rationalp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm fancy-uqi-rational-2
  (implies (and (rational-listp lst2)
                (not (rationalp (cadr newv)))
                (<= xxx (len (loop$-as (cons lst1 (cons lst2 rest))))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest)))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'rationalp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm fancy-uqi-rational-3
  (implies (and (rational-listp lst3)
                (not (rationalp (caddr newv)))
                (<= xxx
                    (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   xxx)))
  :hints (("Goal" :use (:instance
                        general-always$-nth-loop$-as-tuple
                        (fnp 'rationalp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm fancy-uqi-acl2-number-1
  (implies (and (acl2-number-listp lst1)
                (not (acl2-numberp (car newv)))
                (<= xxx (len (loop$-as (cons lst1 rest)))))
           (not (< (mempos newv (loop$-as (cons lst1 rest))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'acl2-numberp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm fancy-uqi-acl2-number-2
  (implies (and (acl2-number-listp lst2)
                (not (acl2-numberp (cadr newv)))
                (<= xxx (len (loop$-as (cons lst1 (cons lst2 rest))))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest))))
                   xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'acl2-numberp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm fancy-uqi-acl2-number-3
  (implies (and (acl2-number-listp lst3)
                (not (acl2-numberp (caddr newv)))
                (<= xxx
                    (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   xxx)))
  :hints (("Goal" :use (:instance
                        general-always$-nth-loop$-as-tuple
                        (fnp 'acl2-numberp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm fancy-uqi-symbol-1
  (implies (and (symbol-listp lst1)
                (not (symbolp (car newv)))
                (<= xxx (len (loop$-as (cons lst1 rest)))))
           (not (< (mempos newv (loop$-as (cons lst1 rest))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'symbolp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm fancy-uqi-symbol-2
  (implies (and (symbol-listp lst2)
                (not (symbolp (cadr newv)))
                (<= xxx (len (loop$-as (cons lst1 (cons lst2 rest))))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest)))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'symbolp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm fancy-uqi-symbol-3
  (implies (and (symbol-listp lst3)
                (not (symbolp (caddr newv)))
                (<= xxx
                    (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   xxx)))
  :hints (("Goal" :use (:instance
                        general-always$-nth-loop$-as-tuple
                        (fnp 'symbolp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm fancy-uqi-true-list-1
  (implies (and (true-list-listp lst1)
                (not (true-listp (car newv)))
                (<= xxx (len (loop$-as (cons lst1 rest)))))
           (not (< (mempos newv (loop$-as (cons lst1 rest))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'true-listp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm fancy-uqi-true-list-2
  (implies (and (true-list-listp lst2)
                (not (true-listp (cadr newv)))
                (<= xxx (len (loop$-as (cons lst1 (cons lst2 rest))))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest)))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'true-listp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm fancy-uqi-true-list-3
  (implies (and (true-list-listp lst3)
                (not (true-listp (caddr newv)))
                (<= xxx
                    (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   xxx)))
  :hints (("Goal" :use (:instance
                        general-always$-nth-loop$-as-tuple
                        (fnp 'true-listp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm structure-of-loop$-as-elements
  (implies (< (mempos newv (loop$-as tuple)) (len (loop$-as tuple)))
           (and (true-listp newv)
                (equal (len newv) (len tuple))))
  :rule-classes nil)

(defthm structure-of-loop$-as-elements-bridge
  (and (implies (and (not (true-listp newv))
                     (<= xxx (len (loop$-as tuple))))
                (not (< (mempos newv (loop$-as tuple)) xxx)))
       (implies (and (not (equal (len newv) (len tuple)))
                     (<= xxx (len (loop$-as tuple))))
                (not (< (mempos newv (loop$-as tuple)) xxx))))
  :hints (("Goal" :use structure-of-loop$-as-elements)))



(defthm fancy-uqi-rational-listp-1
  (implies (and (always$ 'rational-listp lst1)
                (not (rational-listp (car newv)))
                (<= xxx (len (loop$-as (cons lst1 rest)))))
           (not (< (mempos newv (loop$-as (cons lst1 rest))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'rational-listp)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm fancy-uqi-rational-listp-2
  (implies (and (always$ 'rational-listp lst2)
                (not (rational-listp (cadr newv)))
                (<= xxx (len (loop$-as (cons lst1 (cons lst2 rest))))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest)))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'rational-listp)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm fancy-uqi-rational-listp-3
  (implies (and (always$ 'rational-listp lst3)
                (not (rational-listp (caddr newv)))
                (<= xxx
                    (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   xxx)))
  :hints (("Goal" :use (:instance
                        general-always$-nth-loop$-as-tuple
                        (fnp 'rational-listp)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm fancy-uqi-identity-1
  (implies (and (always$ 'identity lst1)
                (not (car newv))
                (<= xxx (len (loop$-as (cons lst1 rest)))))
           (not (< (mempos newv (loop$-as (cons lst1 rest))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'identity)
                                  (tuple (cons lst1 rest))
                                  (n 0)))))

(defthm fancy-uqi-identity-2
  (implies (and (always$ 'identity lst2)
                (not (cadr newv))
                (<= xxx (len (loop$-as (cons lst1 (cons lst2 rest))))))
           (not (< (mempos newv (loop$-as (cons lst1 (cons lst2 rest)))) xxx)))
  :hints (("Goal" :use (:instance general-always$-nth-loop$-as-tuple
                                  (fnp 'identity)
                                  (tuple (cons lst1 (cons lst2 rest)))
                                  (n 1)))))

(defthm fancy-uqi-identity-3
  (implies (and (always$ 'identity lst3)
                (not (caddr newv))
                (<= xxx
                    (len (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))))
           (not (< (mempos newv
                           (loop$-as (cons lst1 (cons lst2 (cons lst3 rest)))))
                   xxx)))
  :hints (("Goal" :use (:instance
                        general-always$-nth-loop$-as-tuple
                        (fnp 'identity)
                        (tuple (cons lst1 (cons lst2 (cons lst3 rest))))
                        (n 2)))))

(defthm rational-listp-make-list
  (implies (and (rationalp init)
                (rational-listp ac))
           (rational-listp (make-list-ac n init ac))))

(defthm always-rational-listp-tails
  (implies (rational-listp lst)
           (always$ 'rational-listp (tails lst))))

(defthm no-element-tails-empty
  (always$ 'identity (tails lst)))

; The need for either of the following lemmas disturbs me.  See the
; discussion after the big test in books/system/tests/loop-tests.lisp.

(defthm true-listp-append-rewrite
  (equal (true-listp (append a b)) (true-listp b)))

; or

; (defthm boohoo-lemma
;   (implies (not (true-listp (append a b)))
;            (not (true-listp b))))

; These plain-uqi lemmas were left out above...

(defthm general-plain-uqi-integer-listp-tails
  (implies (and (integer-listp lst)
                (not (integer-listp newv)))
           (not (< (mempos newv (tails lst)) (len (tails lst)))))
  :rule-classes nil)

(defthm plain-uqi-integer-listp-tails
  (implies (and (integer-listp lst)
                (not (integer-listp newv))
                (<= xxx (len (tails lst))))
           (not (< (mempos newv (tails lst)) xxx)))
  :hints (("Goal" :use general-plain-uqi-integer-listp-tails)))

