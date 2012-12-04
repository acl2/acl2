#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")
(acl2::begin-book);$ACL2s-Preamble$|#


(in-package "DEFDATA")

(set-verify-guards-eagerness 2)


(defun 2+-listp (x)
  (if (atom x)
    (null x)
    (and (integerp (car x))
         (<= 2 (car x))
         (2+-listp (cdr x)))))

; already in program mode:
(DEFUN POS-LISTP (acl2::L)
   (declare (xargs :guard t))
  (COND ((ATOM acl2::L) (EQUAL acl2::L NIL))
        (T (AND (POSP (CAR acl2::L))
                (POS-LISTP (CDR acl2::L))))))


(defthm 2+-listp-forward-to-pos-listp
  (implies (2+-listp x)
           (pos-listp x))
  :rule-classes :forward-chaining)

(defun naturals-listp (x)
   (declare (xargs :guard t))
  (if (atom x)
    (null x)
    (and (natp (car x))
         (naturals-listp (cdr x)))))

(defthm pos-listp-forward-to-naturals-listp
  (implies (pos-listp x)
           (naturals-listp x))
  :rule-classes :forward-chaining)

(defthm naturals-listp-forward-to-integer-listp
  (implies (naturals-listp x)
           (integer-listp x))
  :rule-classes :forward-chaining)

#| ; redundant
(defthm integer-listp-forward-to-rational-listp
  (implies (integer-listp x)
           (rational-listp x))
  :rule-classes :forward-chaining)
|#

; The definition of acl2-number-listp that was here has been omitted 12/4/2012
; by Matt K., since it is now included in ACL2.

(defthm rational-listp-forward-to-acl2-number-listp
  (implies (rational-listp x)
           (acl2-number-listp x))
  :rule-classes :forward-chaining)

(defthm acl2-number-listp-forward-to-true-listp
  (implies (rational-listp x)
           (acl2-number-listp x))
  :rule-classes :forward-chaining)



(defun sum-list (l)
  (declare (xargs :guard (acl2-number-listp l)))
  (if (endp l)
    0
    (+ (car l) (sum-list (cdr l)))))

(defun product-list (l)
  (declare (xargs :guard (acl2-number-listp l)))
  (if (endp l)
    1
    (* (car l) (product-list (cdr l)))))

(defun max-nat-list (l)
  (declare (xargs :guard (rational-listp l)))
  (if (endp l)
    0
    (max (car l)
         (max-nat-list (cdr l)))))

(defun scale (l x)
  (declare (xargs :guard (and (acl2-number-listp l)
                              (acl2-numberp x))))
  (if (endp l)
    nil
    (cons (* (car l) x)
          (scale (cdr l) x))))

(defun shift (l x)
  (declare (xargs :guard (and (acl2-number-listp l)
                              (acl2-numberp x))))
  (if (endp l)
    nil
    (cons (+ (car l) x)
          (shift (cdr l) x))))

#|
(defun pow (l x)
  (declare (xargs :guard (and (acl2-number-listp l)
                              (natp x))))
  (if (endp l)
    nil
    (cons (expt (car l) x)
          (pow (cdr l) x))))
|#

(defun list-expt (base l)
  (declare (xargs :guard (and (acl2-numberp base)
                              (naturals-listp l))))
  (if (endp l)
    nil
    (cons (expt base (car l))
          (list-expt base (cdr l)))))

(defun <=-lists (l1 l2)
  (declare (xargs :guard (and (rational-listp l1)
                              (rational-listp l2)
                              (= (len l1) (len l2)))))
  (if (mbe :logic (or (endp l1) (endp l2))
           :exec (endp l1))
    (mbe :logic (and (endp l1) (endp l2))
         :exec t)
    (and (<= (car l1) (car l2))
         (<=-lists (cdr l1) (cdr l2)))))

(defun all-<= (l v)
  (declare (xargs :guard (and (rationalp v)
                              (rational-listp l))))
  (if (endp l)
    t
    (and (<= (car l) v)
         (all-<= (cdr l) v))))

(defun *-lists (l1 l2)
  (declare (xargs :guard (and (rational-listp l1)
                              (rational-listp l2)
                              (= (len l1) (len l2)))))
  (if (mbe :logic (or (endp l1) (endp l2))
           :exec (endp l1))
    nil
    (cons (* (car l1) (car l2))
          (*-lists (cdr l1) (cdr l2)))))

(defun +-lists (l1 l2)
  (declare (xargs :guard (and (rational-listp l1)
                              (rational-listp l2)
                              (= (len l1) (len l2)))))
  (if (mbe :logic (or (endp l1) (endp l2))
           :exec (endp l1))
    nil
    (cons (+ (car l1) (car l2))
          (+-lists (cdr l1) (cdr l2)))))

(defun make-list-logic (e size)
  (declare (xargs :guard nil))
  (if (zp size)
    nil
    (cons e
          (make-list-logic e (- size 1)))))

(defun pfix (x)
  (if (posp x) x 1))

(defun pos-list-fix (x)
  (if (atom x)
    nil
    (cons (pfix (car x))
          (pos-list-fix (cdr x)))))#|ACL2s-ToDo-Line|#

