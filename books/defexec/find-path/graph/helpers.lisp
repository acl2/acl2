; An Exercise in Graph Theory
; J Strother Moore

; This file is an ACL2 book.  To certify it, execute:
;
; (certify-book "helpers")

; For an explanation of this file, see either the paper or the supporting
; file find-path1.lisp.

; ---

(in-package "ACL2")

(defun rev (x)
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

(defthm append-right-id
  (implies (true-listp a)
           (equal (append a nil) a)))

(defthm consp-append
  (implies (consp a)
           (consp (append a b)))
  :rule-classes :type-prescription)

(defthm car-append
  (equal (car (append x y))
         (if (consp x) (car x) (car y))))

(defthm true-listp-append-rewrite
  (equal (true-listp (append a b))
         (true-listp b)))

(defthm true-listp-rev
  (true-listp (rev x)))

(defthm subsetp-cons
  (implies (subsetp x y)
           (subsetp x (cons e y))))

(defthm subsetp-x-x
  (subsetp x x))

(defthm assoc-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm last-append
  (implies (consp b)
           (equal (last (append a b))
                  (last b))))

(defthm car-last-rev
  (equal (car (last (rev x))) (car x)))

(defthm consp-rev
  (implies (consp x)
           (consp (rev x)))
  :rule-classes :type-prescription)

(defthm car-rev
  (equal (car (rev x)) (car (last x))))

(defthm member-append
  (iff (member x (append a b))
       (or (member x a)
           (member x b))))

(defthm subsetp-append-2
  (and (implies (subsetp a b)
                (subsetp a (append b c)))
       (implies (subsetp a c)
                (subsetp a (append b c)))))

(defthm subsetp-append-1
  (iff (subsetp (append a b) c)
       (and (subsetp a c)
            (subsetp b c))))

(defthm equal-append
  (equal (equal (append x y)
                (append x z))
         (equal y z)))

(defthm duplicatesp-preserved-by-append
  (implies (not (no-duplicatesp y))
           (not (no-duplicatesp (append x y)))))

(defthm no-duplicatesp-append-cons
  (equal (no-duplicatesp (append a (cons e b)))
         (and (not (member e a))
              (not (member e b))
              (no-duplicatesp (append a b)))))

(defthm member-car-last
  (iff (member (car (last x)) x)
       (consp x)))

