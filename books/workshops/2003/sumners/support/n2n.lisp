(in-package "ACL2")
(set-match-free-default :all)
; cert_param: (non-acl2r)

#| n2n.lisp

This book defines the function nice->nat (and its inverse nat->nice) which
defines an invertible mapping from the set of so-called "nice" objects to the
natural numbers. This mapping is used to lift a fair selector of natural
numbers to a fair selector on "nice" objects. Nice objects are basically a
countable subset of the ACL2 universe consisting of strings, numbers,
characters, booleans, keywords, and conses of nice objects. We only include the
keywords and booleans instead of all symbols due to the inability to construct
an arbitrary symbol in ACL2.

|#

; The following was removed with the addition of natp-compound-recognizer to
; ACL2 2.9.2.
;(defthm natp-compound-recognizer
;  (iff (natp x)
;       (and (integerp x)
;            (>= x 0)))
;  :rule-classes :compound-recognizer)

(in-theory (disable natp))

; The definition of bitp here was deleted April 2016 by Matt K. now that bitp
; is defined in ACL2.

(defun ncdr (n)
  (if (or (zp n) (= n 1)) 0 (1+ (ncdr (- n 2)))))

(defun ncar (n)
  (if (or (zp n) (= n 1)) n (ncar (- n 2))))

(defun lsh (n)
  (if (zp n) 0 (+ (lsh (1- n)) 2)))

(defun ncons (b n) (+ b (lsh n)))

(local
(defthm linear-factoid1
  (implies (and (natp n)
                (natp x))
           (equal (+ (- n) n x) x))))

(local
(defthm linear-factoid2
  (implies (and (natp x)
                (natp y)
                (natp z))
           (equal (+ x y z)
                  (+ y x z)))))

(defthm ncar-of-+2-reduce
  (implies (natp n)
           (equal (ncar (+ 2 n))
                  (ncar n)))
  :rule-classes nil)

(defthm ncar-of-1+-lsh
  (equal (ncar (1+ (lsh n))) 1)
  :hints (("Subgoal *1/2'"
           :use (:instance ncar-of-+2-reduce
                           (n (1+ (lsh (+ -1 n)))))
           :in-theory (disable ncar))))

(defthm ncar-of-lsh+0
  (equal (ncar (lsh n)) 0))

(defthm ncdr-of-lhs+0
  (implies (natp n)
           (equal (ncdr (lsh n)) n)))

(defthm ncdr-of-+2-reduce
  (implies (natp n)
           (equal (ncdr (+ 2 n))
                  (1+ (ncdr n)))))

(defthm ncdr-of-lhs+1
  (implies (natp n)
           (equal (ncdr (1+ (lsh n))) n))
  :hints (("Subgoal *1/3'"
           :use (:instance ncdr-of-+2-reduce
                           (n (1+ (lsh (1- n)))))
           :in-theory (disable ncdr))))

(defthm ncar-of-ncons-reduce
  (implies (and (natp n)
                (bitp b))
           (equal (ncar (ncons b n)) b)))

(defthm ncdr-of-ncons-reduce
  (implies (and (natp n)
                (bitp b))
           (equal (ncdr (ncons b n)) n)))

(defthm ncons-reconstruct
  (implies (natp n)
           (equal (ncons (ncar n) (ncdr n)) n)))

(defthm implies-not-zp-<-ncdr
  (implies (not (zp x))
           (< (ncdr x) x))
  :rule-classes :linear)

(defun nlen (x)
  (if (zp x) 0 (1+ (nlen (ncdr x)))))

(defthm not-zp-ncons-1
  (not (zp (ncons 1 x))))

(defthm natp-ncar-propagate
  (implies (natp x)
           (natp (ncar x)))
  :hints (("Subgoal *1/2" :in-theory (enable zp natp)))
  :rule-classes :type-prescription)

(defthm bitp-ncar-propagate
  (implies (natp x)
           (bitp (ncar x)))
  :hints (("Subgoal *1/2" :in-theory (enable zp natp))))

(defthm natp-ncons-propagate
  (implies (natp b)
           (natp (ncons b n)))
  :rule-classes :type-prescription)

(defthm bitp-implies-natp
  (implies (bitp x) (natp x)))

(local (in-theory (disable linear-factoid1 linear-factoid2)))
(in-theory (disable ncons ncar ncdr bitp))

; Matt K. mod for v2-9.1: Remove support for pre-v2.8.

(defun nicep (x)
  (or (stringp x)
      (characterp x)
      (acl2-numberp x)
      (symbolp x)
      (and (consp x)
           (nicep (car x))
           (nicep (cdr x)))))

(defun simplep (x)
  (or (null x)
      (and (consp x)
           (simplep (car x))
           (simplep (cdr x)))))

; Modified slightly 12/4/2012 by Matt K. to be redundant with new ACL2
; definition.
(defun nat-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (natp (car l))
                (nat-listp (cdr l))))))

(defun nat->list (n)
  (if (zp n) () (cons nil (nat->list (1- n)))))

(defun list->nat (x)
  (if (endp x) 0 (1+ (list->nat (cdr x)))))

(defthm nat->list-inverse
  (implies (natp x)
           (equal (list->nat (nat->list x))
                  x)))

(defthm nat->list-simplep
  (simplep (nat->list n)))

(defun clist->simple (x)
  (if (endp x) ()
    (cons (nat->list (char-code (car x)))
          (clist->simple (cdr x)))))

(defun simple->clist (x)
  (if (endp x) ()
    (cons (code-char (list->nat (car x)))
          (simple->clist (cdr x)))))

(defthm clist->simple-inverse
  (implies (character-listp x)
           (equal (simple->clist (clist->simple x))
                  x)))

(defthm clist->simple-simplep
  (simplep (clist->simple x)))

(defun nice-count (x)
  (cond ((null x) 0)
        ((characterp x) 0)
        ((integerp x)
         (if (>= x 0) 0 1))
        ((rationalp x)
         (+ 1
            (nice-count (numerator x))
            (nice-count (denominator x))))
        ((complex-rationalp x)
         (+ 1
            (nice-count (realpart x))
            (nice-count (imagpart x))))
        ((stringp x) 1)
        ((symbolp x) 2)
        ((consp x)
         (+ 1
            (nice-count (car x))
            (nice-count (cdr x))))
        (t 0)))

(defun natural-tag   () (nat->list 1))
(defun negative-tag  () (nat->list 2))
(defun rational-tag  () (nat->list 3))
(defun complex-tag   () (nat->list 4))
(defun character-tag () (nat->list 5))
(defun string-tag    () (nat->list 6))
(defun symbol-tag    () (nat->list 7))
(defun cons-tag      () (nat->list 8))
(defun nil-tag       () nil)
(defun t-tag         () (cons nil nil))

(defun nice->simple (x)
  (declare (xargs :measure (nice-count x)))
  (cond ((eq x nil) (nil-tag))
        ((eq x t)   (t-tag))
        ((integerp x)
         (if (>= x 0)
             (cons (natural-tag)
                   (nat->list x))
           (cons (negative-tag)
                 (nat->list (- x)))))
        ((rationalp x)
         (cons (rational-tag)
               (cons (nice->simple (numerator x))
                     (nice->simple (denominator x)))))
        ((complex-rationalp x)
         (cons (complex-tag)
               (cons (nice->simple (realpart x))
                     (nice->simple (imagpart x)))))
        ((characterp x)
         (cons (character-tag)
               (nat->list (char-code x))))
        ((stringp x)
         (cons (string-tag)
               (clist->simple (coerce x 'list))))
        ((symbolp x)
         (cons (symbol-tag)
               (cons (nice->simple (symbol-package-name x))
                     (nice->simple (symbol-name x)))))
        ((consp x)
         (cons (cons-tag)
               (cons (nice->simple (car x))
                     (nice->simple (cdr x)))))
        (t nil)))

(defun strfix (x) (if (stringp x) x ""))

(defun simple->nice (x)
  (cond ((equal x (nil-tag)) nil)
        ((equal x (t-tag)) t)
        ((equal (car x) (natural-tag))
         (list->nat (cdr x)))
        ((equal (car x) (negative-tag))
         (- (list->nat (cdr x))))
        ((equal (car x) (rational-tag))
         (/ (simple->nice (cadr x))
            (simple->nice (cddr x))))
        ((equal (car x) (complex-tag))
         (complex (simple->nice (cadr x))
                  (simple->nice (cddr x))))
        ((equal (car x) (character-tag))
         (code-char (list->nat (cdr x))))
        ((equal (car x) (string-tag))
         (coerce (simple->clist (cdr x)) 'string))
        ((equal (car x) (symbol-tag))
         (intern$ (strfix (simple->nice (cddr x)))
                  (strfix (simple->nice (cadr x)))))
        ((equal (car x) (cons-tag))
         (cons (simple->nice (cadr x))
               (simple->nice (cddr x))))
        (t nil)))

(defthm nice->simple-inverse
  (implies (nicep x)
           (equal (simple->nice (nice->simple x))
                  x)))

(defthm nice->simple-simplep
  (simplep (nice->simple x)))

(defthm simple->nice-nicep
  (nicep (simple->nice x)))

;; we now use ncons to map simple-trees into natural numbers

(defun interleave (x y)
  (declare (xargs :measure (+ (nlen x) (nlen y))))
  (if (or (not (natp x))
          (not (natp y))
          (and (= x 0) (= y 0)))
      0
    (ncons 1
           (ncons (ncar x)
                  (ncons (ncar y)
                         (interleave (ncdr x)
                                     (ncdr y)))))))

(defun extract1 (x)
  (declare (xargs :measure (nlen x)))
  (if (zp x)
      0
    (ncons (ncar (ncdr x))
           (extract1 (ncdr (ncdr (ncdr x)))))))

(defun extract2 (x)
  (declare (xargs :measure (nlen x)))
  (if (zp x)
      0
    (ncons (ncar (ncdr (ncdr x)))
           (extract2 (ncdr (ncdr (ncdr x)))))))

(defthm extract1-of-interleave
  (implies (and (natp x)
                (natp y))
           (equal (extract1 (interleave x y)) x)))

(defthm extract2-of-interleave
  (implies (and (natp x)
                (natp y))
           (equal (extract2 (interleave x y)) y)))

(defthm extract1-<=-propagate
  (<= (nlen (extract1 x)) (nlen x))
  :rule-classes :linear)

(defthm extract2-<=-propagate
  (<= (nlen (extract2 x)) (nlen x))
  :rule-classes :linear)

(defun simple->nat (x)
  (if (consp x)
      (ncons 1 (interleave (simple->nat (car x))
                           (simple->nat (cdr x))))
    0))

(defun nat->simple (x)
  (declare (xargs :measure (nlen x)))
  (if (and (not (zp x))
           (= (ncar x) 1))
      (cons (nat->simple (extract1 (ncdr x)))
            (nat->simple (extract2 (ncdr x))))
    nil))

(defthm simple->nat-inverse
  (implies (simplep x)
           (equal (nat->simple (simple->nat x))
                  x)))

(defthm simple->nat-is-natp
  (natp (simple->nat x)))

(defthm nat->simplep-is-simplep
  (simplep (nat->simple x)))

(defun nice->nat (x)
  (simple->nat (nice->simple x)))

(defun nat->nice (x)
  (simple->nice (nat->simple x)))

(defthm nice->nat-inverse
  (implies (nicep x)
           (equal (nat->nice (nice->nat x))
                  x)))

(defthm nice->nat-is-natural
  (natp (nice->nat x))
  :rule-classes (:type-prescription :rewrite))

(defthm nat->nice-is-nicep
  (nicep (nat->nice x)))

(defthm nice->simple-atom-implies-nil
  (implies (nicep x)
           (equal (atom (nice->simple x)) (not x))))

(defthm ncons-of-1-not-equal-0
  (not (equal (ncons 1 x) 0))
  :hints (("Goal" :in-theory (enable ncons))))

(defthm simple->nat-0-implies-atom
  (equal (equal (simple->nat x) 0) (atom x)))

(defthm nice->nat-0-implies-nil
  (implies (nicep x)
           (equal (equal (nice->nat x) 0) (not x)))
  :hints (("Goal" :in-theory (disable nice->simple nicep simple->nat))))

(in-theory (disable nat->nice nice->nat))

;; NOTE -- we conclude this book with a simple trick using defun-sk to get a
;; predicate recognizing the natural numbers which are in the range of
;; nice->nat and using this predicate to prove the additional property required
;; to show that nat->nice and nice->nat are bijective on this range and the
;; nice objects. We do not use the following properties in the books this book
;; supports, but others may find this useful and at least this little logic
;; trick may have other applications:

(defun-sk nice-natp (x)
  (exists y (and (nicep y) (equal (nice->nat y) x))))

(defthm nice-natp-implies-natp
  (implies (nice-natp x)
           (natp x)))

(defthm nice->nat-is-nice-natp
  (implies (nicep x)
           (nice-natp (nice->nat x)))
  :hints (("Goal" :use (:instance nice-natp-suff
                                  (y x)
                                  (x (nice->nat x)))
           :in-theory (disable nice-natp-suff))))

(defthm nat->nice-inverse
  (implies (nice-natp x)
           (equal (nice->nat (nat->nice x))
                  x))
  :hints (("Goal" :use (:instance nice->nat-inverse
                                  (x (nice-natp-witness x)))
           :in-theory (disable nice->nat-inverse))))


(defun nice-nat (x)
  (nice->nat (nat->nice x)))

(defthm nice-natp-of-nice-nat
  (nice-natp (nice-nat x)))

(in-theory (disable nice-natp))





