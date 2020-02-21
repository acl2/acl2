; Written by John Cowles
; Copyright/License: See the LICENSE file in directory ../cowles/LICENSE
; Modifications by Matt Kaufmann and Sol Swords

(in-package "ACL2")

(defthm pseudo-term-listp-cdr
  (implies (and (pseudo-termp x)
                (not (equal (car x) 'quote)))
           (pseudo-term-listp (cdr x))))

(defthm pseudo-termp-opener
  (implies (and (consp x)
                (symbolp (car x))
                (not (equal (car x) 'quote)))
           (equal (pseudo-termp x)
                  (pseudo-term-listp (cdr x)))))

(defthm pseudo-term-listp-of-atom
  (implies (not (consp x))
           (equal (pseudo-term-listp x)
                  (equal x nil)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm pseudo-term-listp-of-cons
  (equal (pseudo-term-listp (cons a x))
         (and (pseudo-termp a)
              (pseudo-term-listp x))))

(defthm pseudo-termp-list-cdr
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (cdr x))))

(defthm pseudo-termp-car
  (implies (pseudo-term-listp x)
           (pseudo-termp (car x))))

(defthm pseudo-termp-cadr-from-pseudo-term-listp
  (implies (pseudo-term-listp x)
           (pseudo-termp (cadr x))))

(defthm pseudo-term-listp-append
  (implies (and (pseudo-term-listp x)
                (pseudo-term-listp y))
           (pseudo-term-listp (append x y))))



(defund pseudo-term-substp  (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (symbolp (caar x))
         (pseudo-termp (cdar x))
         (pseudo-term-substp (cdr x)))))

(local (in-theory (enable pseudo-term-substp)))

(defthm pseudo-termp-of-lookup-in-subst
  (implies (pseudo-term-substp x)
           (pseudo-termp (cdr (assoc k x)))))

(defthm pseudo-term-substp-of-acons
  (equal (pseudo-term-substp (cons (cons k v) x))
         (and (symbolp k)
              (pseudo-termp v)
              (pseudo-term-substp x))))

(defthm pseudo-term-substp-of-atom
  (implies (not (consp x))
           (equal (pseudo-term-substp x)
                  (equal x nil)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm pseudo-term-substp-of-pairlis
  (implies (and (symbol-listp x)
                (pseudo-term-listp y))
           (pseudo-term-substp (pairlis$ x y))))

(defthm pseudo-term-substp-of-append
  (implies (and (pseudo-term-substp a)
                (pseudo-term-substp b))
           (pseudo-term-substp (append a b))))


(defund pseudo-term-val-alistp  (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (pseudo-termp (cdar x))
         (pseudo-term-val-alistp (cdr x)))))

(local (in-theory (enable pseudo-term-val-alistp)))

(defthm pseudo-termp-of-lookup-in-pseudo-term-val-alistp
  (implies (pseudo-term-val-alistp x)
           (pseudo-termp (cdr (assoc k x)))))

(defthm pseudo-term-val-alistp-of-acons
  (equal (pseudo-term-val-alistp (cons (cons k v) x))
         (and (pseudo-termp v)
              (pseudo-term-val-alistp x))))

(defthm pseudo-term-val-alistp-of-atom
  (implies (not (consp x))
           (equal (pseudo-term-val-alistp x)
                  (equal x nil)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm pseudo-term-val-alistp-of-pairlis
  (implies (pseudo-term-listp y)
           (pseudo-term-val-alistp (pairlis$ x y))))

(defthm pseudo-term-val-alistp-of-append
  (implies (and (pseudo-term-val-alistp a)
                (pseudo-term-val-alistp b))
           (pseudo-term-val-alistp (append a b))))


