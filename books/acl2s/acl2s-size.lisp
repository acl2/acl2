(in-package "ACL2")
(include-book "acl2s/cons-size" :dir :system)

(defun acl2s-size (x)
  (declare (xargs :guard t))
  (cond ((consp x)
         (+ 1 (acl2s-size (car x))
            (acl2s-size (cdr x))))
        ((rationalp x)
         (integer-abs (numerator x)))
        ((stringp x)
         (length x))
        (t 0)))

#|

Added these rules as built-in clauses

(defthm acl2s-size-string
  (implies (stringp x)
           (equal (acl2s-size x) (length x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-rational
  (implies (rationalp x)
           (equal (acl2s-size x)
                  (integer-abs (numerator x))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

#|

 Causes rewrite loops. Seems like an ACL2 bug, or at least there is a
 potential for improvement since we should catch such rewrite
 loops. Investigate at some point. (remove similar built-in clauses to
 reproduce) 

(defthm acl2s-size-cons
  (implies (consp (double-rewrite x))
           (equal (acl2s-size x)
                  (+ 1 (acl2s-size (car (double-rewrite x)))
                     (acl2s-size (cdr (double-rewrite x))))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

|#

(defthm acl2s-size-else
  (implies (and (atom (double-rewrite x))
                (not (rationalp x))
                (not (stringp x)))
           (equal (acl2s-size x) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

|#

(defthm acl2s-size-type-fc
  (natp (acl2s-size x))
  :rule-classes
  ((:type-prescription)
   (:forward-chaining :trigger-terms ((acl2s-size x)))))

(defthm acons-acl2s-size-lemma
  (= (acl2s-size (acons x1 x2 x3))
     (+ 2 (acl2s-size x1)
        (acl2s-size x2)
        (acl2s-size x3)))
  :rule-classes ((:rewrite)))

(defthm acl2s-size-of-prod-cons1
  (<= (acl2s-size std::y)
      (acl2s-size (std::prod-cons std::x std::y)))
  :rule-classes :linear)

(defthm acl2s-size-of-prod-cons2
  (<= (acl2s-size std::x)
      (acl2s-size (std::prod-cons std::x std::y)))
  :rule-classes :linear)

(defthm acl2s-size-of-nth-linear
  (implies (consp (double-rewrite x))
           (< (acl2s-size (nth i x))
              (acl2s-size x)))
  :rule-classes ((:linear :backchain-limit-lst 0)))

(defthm acl2s-size-of-nth-linear-weak
  (<= (acl2s-size (nth i x))
      (acl2s-size x))
  :rule-classes :linear)

(defthm acl2s-size-of-nthcdr-linear
  (implies (and (not (zp (double-rewrite n)))
                (consp (double-rewrite x)))
           (< (acl2s-size (nthcdr n x))
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable nthcdr)))
  :rule-classes ((:linear :backchain-limit-lst 1)))

(defthm acl2s-size-of-nthcdr-linear-weak
  (<= (acl2s-size (nthcdr n x))
      (acl2s-size x))
  :hints (("Goal" :in-theory (enable nthcdr)))
  :rule-classes :linear)

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm acl2s-size-of-remove-duplicates
   (<= (acl2s-size (remove-duplicates-equal x))
       (acl2s-size x))
   :rule-classes :linear))

(defthm acl2s-size-when-member
  (implies (member-equal a (double-rewrite x))
           (< (acl2s-size a)
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable member-equal)))
  :rule-classes ((:linear :backchain-limit-lst 1 :match-free :all)
                 (:rewrite :backchain-limit-lst 1 :match-free :all)))

(defthm acl2s-size-of-remove-assoc-equal-upper-bound
  (<= (acl2s-size (remove-assoc-equal a x))
      (acl2s-size x))
  :hints (("Goal" :in-theory (enable remove-assoc-equal)))
  :rule-classes :linear)

(defthm tail-acl2s-size
  (implies (not (set::empty x))
           (< (acl2s-size (set::tail x))
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable set::empty set::tail)))
  :rule-classes ((:rewrite :backchain-limit-lst 0) 
                 (:linear :backchain-limit-lst 0)))

(defthm head-acl2s-size
  (implies (not (set::empty x))
           (< (acl2s-size (set::head x))
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable set::empty set::head)))
  :rule-classes ((:rewrite :backchain-limit-lst 0) 
                 (:linear :backchain-limit-lst 0)))

(defthm split-list-1-acl2s-size
  (implies (consp (double-rewrite x))
           (< (acl2s-size (mv-nth 1 (str::split-list-1 x str::del)))
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable str::split-list-1)))
  :rule-classes ((:rewrite :backchain-limit-lst 0) 
                 (:linear :backchain-limit-lst 0)))

(defthm records-lemma-acl2s-size
  (implies (and (acl2::ifmp v)
                (acl2::well-formed-map v))
           (< (acl2s-size (acl2::mget-wf x v))
              (acl2s-size v)))
  :hints (("goal" :in-theory (enable acl2::mget-wf)))
  :rule-classes ((:linear :backchain-limit-lst 1)))
 
(defthm records-acl2s-size-linear-arith-<=
  (<= (acl2s-size (mget k v))
      (acl2s-size v))
  :hints (("goal" :in-theory (enable mget acl2::acl2->map)))
  :rule-classes :linear)

(defthm records-acl2s-size-linear-arith-<2
  (implies (and (not (equal k (acl2::ill-formed-key)))
                (mget k v))
           (< (acl2s-size (mget k v))
              (acl2s-size v)))
  :hints (("goal" :in-theory (enable mget acl2::acl2->map)))
  :rule-classes ((:linear :backchain-limit-lst 1)))

(defthm records-acl2s-size
  (implies (and (consp v)
                (not (equal x (acl2::ill-formed-key))))
           (< (acl2s-size (mget x v))
              (acl2s-size v)))
  :hints (("goal" :induct (acl2::mget-wf x v)
           :in-theory (enable mget acl2::acl2->map)))
  :rule-classes ((:linear :backchain-limit-lst 1)))

(defthm acl2s-size-evens-weak
  (<= (acl2s-size (evens x))
      (acl2s-size x))
  :hints (("Goal" :induct (evens x)))
  :rule-classes :linear)

(defthm acl2s-size-evens-strong
  (implies (consp (cdr (double-rewrite x)))
           (< (acl2s-size (evens x))
              (acl2s-size x)))
  :rule-classes ((:linear :backchain-limit-lst 1)))

(defthm acl2-size-append
  (<= (acl2-size (append x y))
      (+ (acl2-size x) (acl2-size y) 1))
  :rule-classes ((:linear) (:rewrite)))

(defthm acl2s-size-append-tlp
  (implies (and (true-listp x) (true-listp y))
           (= (acl2s-size (append x y))
              (+ (acl2s-size x) (acl2s-size y))))
  :hints (("goal" :in-theory (enable append)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

#|

 Maybe a replacement for car-of-append

(defthm car-of-append-backchain
  (implies (consp (double-rewrite x))
           (equal (car (append x y))
                  (car x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))
|#

(defthm rev-acl2s-size
  (<= (acl2s-size (rev x))
      (acl2s-size x))
  :hints (("Goal" :in-theory (e/d (rev))))
  :rule-classes ((:linear)))

(defthm rev-acl2s-size-tlp
  (implies (true-listp x)
           (= (acl2s-size (rev x))
              (acl2s-size x)))
  :hints (("Goal" :in-theory (enable rev)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-of-hons-remove-duplicates
  (<= (acl2s-size (acl2::hons-remove-duplicates x))
      (acl2s-size x))
  :hints (("Goal" :in-theory (enable acl2::hons-remove-duplicates)))
  :rule-classes ((:linear) (:rewrite)))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm acl2s-size-<=-acl2-count
   (<= (acl2s-size x)
       (acl2-count x))
   :rule-classes :linear))

#|

 There seems to be no way to get rid of the double-rewrite warning
 without introducing a non-rec warning. Is this what is supposed to
 happen?

|#

(defthm len-<=-acl2s-size
  (<= (len x) (acl2s-size x))
  :rule-classes :linear)


#|

Maybe be useful for replacing acl2-count with acl2s-size.

(defconst *acl2s-size-built-in-clauses*
  (list

; acl2s-size is an ordinal.

   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o-p (acl2s-size x)))
         :all-fnnames '(o-p acl2s-size))

; Car and cdr decrease on consps.
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (car x))
                       (acl2s-size x))
                   (not (consp x)))
         :all-fnnames '(acl2s-size car o< consp not))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (cdr x))
                       (acl2s-size x))
                   (not (consp x)))
         :all-fnnames '(acl2s-size cdr o< consp not))

; Car and cdr decrease on non-atoms.
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (car x))
                       (acl2s-size x))
                   (atom x))
         :all-fnnames '(acl2s-size car o< atom))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (cdr x))
                       (acl2s-size x))
                   (atom x))
         :all-fnnames '(acl2s-size cdr o< atom))

; Car and cdr decrease on non-endps.
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (car x))
                       (acl2s-size x))
                   (endp x))
         :all-fnnames '(acl2s-size car o< endp))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (cdr x))
                       (acl2s-size x))
                   (endp x))
         :all-fnnames '(acl2s-size cdr o< endp))

; 1- decreases on positives and on non-negatives other than 0.  But we
; represent (1- x) three different ways: (1- x), (+ x -1) and (+ -1 x).  And to
; say "other than 0" we can use (not (zp x)) or (integerp x) together
; with the negations of any one of (equal x 0), (= x 0) or (= 0 x).  The
; symmetry of equal is built into unification, but not so =, so we have
; two versions for each =.

; However, in Version 1.8 we made 1- a macro.  Therefore, we have deleted the
; two built-in-clauses for 1-.  If we ever make 1- a function again, we should
; add them again.

   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (binary-+ x '-1))
                       (acl2s-size x))
                   (zp x))
         :all-fnnames '(acl2s-size o< zp))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (binary-+ '-1 x))
                       (acl2s-size x))
                   (zp x))
         :all-fnnames '(acl2s-size o< zp))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (binary-+ x '-1))
                       (acl2s-size x))
                   (not (integerp x))
                   (not (< '0 x)))
         :all-fnnames '(acl2s-size o< integerp < not))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (binary-+ x '-1))
                       (acl2s-size x))
                   (not (integerp x))
                   (< x '0)
                   (= x '0))
         :all-fnnames '(acl2s-size o< integerp not < =))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (binary-+ x '-1))
                       (acl2s-size x))
                   (not (integerp x))
                   (< x '0)
                   (= '0 x))
         :all-fnnames '(acl2s-size o< integerp not < =))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (binary-+ x '-1))
                       (acl2s-size x))
                   (not (integerp x))
                   (< x '0)
                   (equal x '0))
         :all-fnnames '(acl2s-size o< integerp not < equal))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (binary-+ '-1 x))
                       (acl2s-size x))
                   (not (integerp x))
                   (not (< '0 x)))
         :all-fnnames '(acl2s-size o< integerp < not))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (binary-+ '-1 x))
                       (acl2s-size x))
                   (not (integerp x))
                   (< x '0)
                   (= x '0))
         :all-fnnames '(acl2s-size o< integerp not < =))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (binary-+ '-1 x))
                       (acl2s-size x))
                   (not (integerp x))
                   (< x '0)
                   (= '0 x))
         :all-fnnames '(acl2s-size o< integerp not < =))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (binary-+ '-1 x))
                       (acl2s-size x))
                   (not (integerp x))
                   (< x '0)
                   (equal x '0))
         :all-fnnames '(acl2s-size o< integerp not < equal))

; Finally, cdr decreases on non-nil true-listps, but we can say
; "non-nil" as (eq x nil), (eq nil x), (null x) or (equal x nil)
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (cdr x))
                       (acl2s-size x))
                   (not (true-listp x))
                   (eq x 'nil))
         :all-fnnames '(acl2s-size cdr o< true-listp not eq))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (cdr x))
                       (acl2s-size x))
                   (not (true-listp x))
                   (null x))
         :all-fnnames '(acl2s-size cdr o< true-listp not null))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (cdr x))
                       (acl2s-size x))
                   (not (true-listp x))
                   (eq 'nil x))
         :all-fnnames '(acl2s-size cdr o< true-listp not eq))
   (make built-in-clause
         :nume nil
         :rune *fake-rune-for-anonymous-enabled-rule*
         :clause '((o< (acl2s-size (cdr x))
                       (acl2s-size x))
                   (not (true-listp x))
                   (equal x 'nil))
         :all-fnnames '(acl2s-size cdr o< true-listp not equal))))

 (in-package "ACL2")

(make-built-in-clause-rules
 *fake-rune-for-anonymous-enabled-rule*
 nil
 '(implies (consp x) (< (acl2s-size (cdr x)) (acl2s-size x)))
 (w state))

(defun add-acl2s-builtin-clauses (state)
  (declare (xargs :mode :program :stobjs state))
  (let ((rules *acl2s-size-built-in-clauses*))
    (pprogn (f-put-global
             'half-length-built-in-clauses
             (floor (+ (length rules)
                       (length (global-val 'built-in-clauses (w state))))
                    2)
             state)
            (f-put-global
             'built-in-clauses
             (classify-and-store-built-in-clause-rules
              rules
              (global-val 'built-in-clauses (w state))
              (w state))
             state))))

(add-acl2s-builtin-clauses state)

(global-val 'built-in-clauses (w state))
(global-val 'half-length-built-in-clauses (w state))
|#

(defthm acl2s-size-built-in-1
  (o-p (acl2s-size x))
  :rule-classes :built-in-clause)

(defthm acl2s-size-built-int
  (integerp (acl2s-size x))
  :rule-classes :built-in-clause)

(defthm acl2s-size-built-nat
  (<= 0 (acl2s-size x))
  :rule-classes :built-in-clause)

(defthm acl2s-size-o<-<
  (equal (o< (acl2s-size x) (acl2s-size y))
         (< (acl2s-size x) (acl2s-size y))))

; Car and cdr decrease on consps.
(defthm acl2s-size-built-in-2
  (implies (consp x)
           (and (< (acl2s-size (car x))
                   (acl2s-size x))
                (o< (acl2s-size (car x))
                    (acl2s-size x))))
  :rule-classes ((:built-in-clause)))

(defthm acl2s-size-built-in-3
  (implies (consp x)
           (and (< (acl2s-size (cdr x))
                   (acl2s-size x))
                (o< (acl2s-size (cdr x))
                    (acl2s-size x))))
  :rule-classes ((:built-in-clause)))

; Car and cdr decrease on non-atoms.

(defthm acl2s-size-built-in-4
  (implies (not (atom x))
           (and (< (acl2s-size (car x))
                   (acl2s-size x))
                (o< (acl2s-size (car x))
                    (acl2s-size x))))
  :rule-classes :built-in-clause)

(defthm acl2s-size-built-in-5
  (implies (not (atom x))
           (and (< (acl2s-size (cdr x)) 
                   (acl2s-size x))
                (o< (acl2s-size (cdr x)) 
                    (acl2s-size x))))
  :rule-classes :built-in-clause)

; Car and cdr decrease on non-endps.
(defthm acl2s-size-built-in-6
  (implies (not (endp x))
           (and (< (acl2s-size (car x))
                   (acl2s-size x))
                (o< (acl2s-size (car x))
                    (acl2s-size x))))
  :rule-classes :built-in-clause)

(defthm acl2s-size-built-in-7
  (implies (not (endp x))
           (and (< (acl2s-size (cdr x))
                   (acl2s-size x))
                (o< (acl2s-size (cdr x))
                    (acl2s-size x))))
  :rule-classes :built-in-clause)

; 1- decreases on positives and on non-negatives other than 0.  But we
; represent (1- x) three different ways: (1- x), (+ x -1) and (+ -1 x).  And to
; say "other than 0" we can use (not (zp x)) or (integerp x) together
; with the negations of any one of (equal x 0), (= x 0) or (= 0 x).  The
; symmetry of equal is built into unification, but not so =, so we have
; two versions for each =.

; However, in Version 1.8 we made 1- a macro.  Therefore, we have deleted the
; two built-in-clauses for 1-.  If we ever make 1- a function again, we should
; add them again.

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm acl2s-size-built-in-8
   (implies (not (zp x))
            (and (< (acl2s-size (binary-+ x -1))
                    (acl2s-size x))
                 (o< (acl2s-size (binary-+ x -1))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-9
   (implies (not (zp x))
            (and (< (acl2s-size (binary-+ -1 x))
                    (acl2s-size x))
                 (o< (acl2s-size (binary-+ -1 x))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-10
   (implies (and (integerp x)
                 (< 0 x))
            (and (< (acl2s-size (binary-+ x -1))
                    (acl2s-size x))
                 (o< (acl2s-size (binary-+ x -1))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-11
   (implies (and (integerp x)
                 (not (< x 0))
                 (not (= x 0)))
            (and (< (acl2s-size (binary-+ x -1))
                    (acl2s-size x))
                 (o< (acl2s-size (binary-+ x -1))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-12
   (implies (and (integerp x)
                 (not (< x 0))
                 (not (= x 0)))
            (and (< (acl2s-size (binary-+ x -1))
                    (acl2s-size x))
                 (o< (acl2s-size (binary-+ x -1))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-13
   (implies (and (integerp x)
                 (not (< x 0))
                 (not (equal x 0)))
            (and (< (acl2s-size (binary-+ x -1))
                    (acl2s-size x))
                 (o< (acl2s-size (binary-+ x -1))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-14
   (implies (and (integerp x)
                 (< 0 x))
            (and (< (acl2s-size (binary-+ -1 x))
                    (acl2s-size x))
                 (o< (acl2s-size (binary-+ -1 x))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-15
   (implies (and (integerp x)
                 (not (< x 0))
                 (not (= x 0)))
            (and (< (acl2s-size (binary-+ -1 x))
                    (acl2s-size x))
                 (o< (acl2s-size (binary-+ -1 x))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-16
   (implies (and (integerp x)
                 (not (< x 0))
                 (not (= 0 x)))
            (and (< (acl2s-size (binary-+ -1 x))
                    (acl2s-size x))
                 (o< (acl2s-size (binary-+ -1 x))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-17
   (implies (and (integerp x)
                 (not (< x 0))
                 (not (equal 0 x)))
            (and (< (acl2s-size (binary-+ -1 x))
                    (acl2s-size x))
                 (o< (acl2s-size (binary-+ -1 x))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

; Finally, cdr decreases on non-nil true-listps, but we can say
; "non-nil" as (eq x nil), (eq nil x), (null x) or (equal x nil)
 (defthm acl2s-size-built-in-18
   (implies (and (true-listp x)
                 (not (eq x nil)))
            (and (< (acl2s-size (cdr x))
                    (acl2s-size x))
                 (o< (acl2s-size (cdr x))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-19
   (implies (and (true-listp x)
                 (not (null x)))
            (and (< (acl2s-size (cdr x))
                    (acl2s-size x))
                 (o< (acl2s-size (cdr x))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-20
   (implies (and (true-listp x)
                 (not (eq nil x)))
            (and (< (acl2s-size (cdr x))
                    (acl2s-size x))
                 (o< (acl2s-size (cdr x))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)

 (defthm acl2s-size-built-in-21
   (implies (and (true-listp x)
                 (not (equal x nil)))
            (and (< (acl2s-size (cdr x))
                    (acl2s-size x))
                 (o< (acl2s-size (cdr x))
                     (acl2s-size x))))
   :rule-classes :built-in-clause)
 )

#|
(defthm acl2s-size-string
  (implies (stringp x)
           (equal (acl2s-size x) (length x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-rational
  (implies (rationalp x)
           (equal (acl2s-size x)
                  (integer-abs (numerator x))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))
   
(defthm acl2s-size-cons
  (implies (consp x)
           (equal (acl2s-size x)
                  (+ 1 (acl2s-size (car x))
                     (acl2s-size (cdr x)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2s-size-else
  (implies (and (atom x)
                (not (rationalp x))
                (not (stringp x)))
           (equal (acl2s-size x) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(thm (implies (consp x) (o< (acl2s-size (cdr x)) (acl2s-size x))))
(thm (implies (consp x) (< (acl2s-size (cdr x)) (acl2s-size x))))

(thm (implies (consp x) (o< (acl2-count (cdr x)) (acl2-count x))))
(thm (implies (consp x) (< (acl2-count (cdr x)) (acl2-count x))))

|#
