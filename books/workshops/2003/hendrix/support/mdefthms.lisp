;;;;; Basic theorems for low level matrix operations.  The other books are designed to
;;;;; be provable using the theorems defined here without relying on the implementation
;;;;; details.

(in-package "ACL2")

(include-book "mdefuns")

;;; If the length of an variable is zero, it is an atom.
(defthm len-atom
  (implies (equal (len x) 0)
           (atom x))
  :rule-classes :forward-chaining)

;;; We know that the length of a cons is at least one.
(defthm len-consp
  (implies (consp l)
           (< 0 (len l)))
  :rule-classes :type-prescription)

;;;; Low level theorems used in proving public theorems.
;;;; Not currently documented.
(local
 (defthm mvectorp-col-car-local
   (implies (and (vector-list-of-lenp m i)
                 (< 0 i))
            (mvectorp (col-car m)))
   :rule-classes ((:rewrite :match-free :once))))

(local
 (defthm vector-list-col-cdr
   (implies (vector-list-of-lenp m (+ 1 i))
            (vector-list-of-lenp (col-cdr m) i))))

(local
 (defthm vector-list-col-cons-nil
   (implies (mvectorp l)
            (vector-list-of-lenp (col-cons-impl l nil) 1))))

(local
 (defthm vector-list-col-cons
   (implies (and (vector-list-of-lenp m i)
                 (mvectorp l)
                 (equal (len l) (len m)))
            (vector-list-of-lenp (col-cons-impl l m) (1+ i)))))

(local
 (defthm len-car-col-cdr
   (implies (and (vector-list-of-lenp m i)
                 (< 0 i)
                 (consp m))
            (equal (len (car (col-cdr m)))
                   (1- i)))
   :rule-classes ((:rewrite :match-free :once))))

(local
 (defthm len-car-col-cons
   (implies (consp l)
            (equal (len (car (col-cons-impl l m)))
                   (1+ (len (car m)))))))

(local
 (defthm consp-col-car-local
   (implies (and (vector-list-of-lenp m i)
                 (< 0 i))
            (equal (consp (col-car m))
                   (consp m)))
   :rule-classes ((:rewrite :match-free :once))))

(local
 (defthm consp-col-cdr
   (implies (and (vector-list-of-lenp m i)
                 (< 1 i)
                 (consp m))
            (consp (col-cdr m)))
   :rule-classes ((:rewrite :match-free :once))))

(local
 (defthm consp-col-cons-impl
   (implies (consp l)
            (consp (col-cons-impl l m)))
   :rule-classes ((:rewrite :match-free :once))))

(local
 (defthm col-cons-impl-atom
   (implies (vector-list-of-lenp m 1)
            (equal (col-cons-impl (col-car m) nil)
                   m))))

(local
 (defthm col-cons-impl-elim
   (implies (and (vector-list-of-lenp m i)
                 (< 0 i))
            (equal (col-cons-impl (col-car m) (col-cdr m))
                   m))
   :rule-classes ((:rewrite :match-free :once))))

;;;;;Type rules

;;;; Type rules for row car, cdr, cons

(defthm m-empty-nil
  (implies (and (m-emptyp m)
                (matrixp m))
           (equal m nil))
  :rule-classes :forward-chaining)

(defthm car-vector-type
  (implies (and (mvectorp l)
                (consp l))
           (acl2-numberp (car l)))
  :rule-classes (:type-prescription :rewrite))

(defthm mvectorp-row-car
  (implies (matrixp m)
           (mvectorp (row-car m)))
  :rule-classes (:type-prescription :rewrite))

(defthm consp-row-car
  (implies (and (case-split (not (m-emptyp m)))
                (matrixp m))
           (consp (row-car m)))
  :rule-classes (:type-prescription :rewrite))

(defthm matrixp-row-cdr
  (implies (matrixp m)
           (matrixp (row-cdr m))))

(defthm matrixp-row-cons
  (implies (and (matrixp m)
                (mvectorp l)
                (consp l)
                (or (m-emptyp m)
                    (equal (col-count m) (len l))))
           (matrixp (row-cons l m))))

;;;; Col car, cdr, cons type rules
(defthm mvectorp-col-car
  (implies (matrixp m)
           (mvectorp (col-car m)))
  :rule-classes (:type-prescription :rewrite))

(defthm consp-col-car
  (implies (and (not (m-emptyp m))
                (matrixp m))
           (consp (col-car m)))
  :rule-classes (:type-prescription :rewrite))

(defthm matrixp-col-cdr
  (implies (matrixp m)
           (matrixp (col-cdr m))))

(defthm matrixp-col-cons
  (implies (col-cons-guard l m)
           (matrixp (col-cons l m))))


(defthm empty-row-cdr-col-cdr
  (implies (matrixp m)
           (equal (m-emptyp (row-cdr (col-cdr m)))
                  (or (m-emptyp (row-cdr m))
                      (m-emptyp (col-cdr m))))))

(local
 (defthm vector-list-1-not-consp-col-cdr
   (implies (vector-list-of-lenp m 1)
            (not (consp (col-cdr m))))))

(defthm empty-col-cdr-row-cdr
  (implies (matrixp m)
           (equal (m-emptyp (col-cdr (row-cdr m)))
                  (or (m-emptyp (col-cdr m))
                      (m-emptyp (row-cdr m))))))

;;;; Theorems necessary to admit common recursion scheme for matrix operations.

(defthm acl2-count-col-cdr
  (implies (not (m-emptyp m))
           (< (acl2-count (col-cdr m))
              (acl2-count m))))

(defthm acl2-count-row-cdr
  (implies (not (m-emptyp m))
           (< (acl2-count (row-cdr m))
              (acl2-count m))))

;;;; The row-cons or col-cons is never an m-empty
(defthm not-empty-row-cons
  (not (m-emptyp (row-cons r m))))

(defthm not-empty-col-cons
  (not (m-emptyp (col-cons c m))))

;;;;; Logical definitions are provided for the basic functions since they
;;;;; are disabled by this package.  Row-cdr, row-cons, col-cdr, and col-cons
;;;;; are not actually enabled as they are not normally needed, however they
;;;;; can be used in special circumstances.  I also added induction rules that
;;;;; can be used in induction heuristics.

;;;; Logical definitions for row-car, row-cdr, and row-cons.

(defun row-car-recursion (m)
  (declare (xargs :guard (matrixp m)))
  (if (m-emptyp m)
      nil
    (row-car-recursion (col-cdr m))))

(defthm row-car-def
  (implies (matrixp m)
           (equal (row-car m)
                  (if (m-emptyp m)
                      nil
                    (cons (car (col-car m)) (row-car (col-cdr m))))))
  :rule-classes ((:definition
                  :clique (col-car row-car col-cdr)
                  :controller-alist ((col-car t)
                                     (row-car t)
                                     (col-cdr t)))
                 (:induction :pattern (row-car m)
                             :scheme (row-car-recursion m))))

(defun row-cdr-recursion (m)
  (declare (xargs :guard (matrixp m)))
  (if (or (m-emptyp (row-cdr m))
          (m-emptyp (col-cdr m)))
      nil
    (row-cdr-recursion (col-cdr m))))

(defthmd row-cdr-def
  (implies (matrixp m)
           (equal (row-cdr m)
                  (if (endp (cdr (col-car m)))
                      nil
                    (col-cons (cdr (col-car m))
                              (row-cdr (col-cdr m))))))
  :rule-classes ((:definition
                  :clique (col-car row-cdr col-cdr col-cons)
                  :controller-alist ((col-car t)
                                     (row-cdr t)
                                     (col-cdr t)
                                     (col-cons t t)))
                 (:induction :pattern (row-cdr m)
                             :scheme (row-cdr-recursion m))))

(defun row-cons-recursion (l m)
  (declare (xargs :guard (row-cons-guard l m)))
  (cond ((endp (cdr l)) nil)
        ((m-emptyp m) (row-cons-recursion (cdr l) m))
        (t (row-cons-recursion (cdr l) (col-cdr m)))))

(defthmd row-cons-def
  (implies (row-cons-guard l m)
           (equal (row-cons l m)
                  (col-cons (cons (car l) (col-car m))
                              (if (endp (cdr l))
                                  nil
                                (row-cons (cdr l) (col-cdr m))))))
  :rule-classes ((:definition
                  :clique (col-car col-cdr row-cons col-cons)
                  :controller-alist ((col-car t)
                                     (col-cdr t)
                                     (row-cons t t)
                                     (col-cons t t)))
                 (:induction :pattern (row-cons l m)
                             :scheme (row-cons-recursion l m))))

;;;; Logical definitions for col-car, col-cdr, col-cons

(defun col-car-recursion (m)
  (declare (xargs :guard (matrixp m)))
  (if (m-emptyp m)
      nil
    (col-car-recursion (row-cdr m))))

(defthm col-car-def
  (implies (matrixp m)
           (equal (col-car m)
                  (if (m-emptyp m)
                      nil
                    (cons (car (row-car m)) (col-car (row-cdr m))))))
  :rule-classes ((:definition
                  :clique (col-car row-car row-cdr)
                  :controller-alist ((col-car t)
                                     (row-car t)
                                     (row-cdr t)))
                 (:induction :pattern (col-car m)
                             :scheme (col-car-recursion m))))

(defun col-cdr-recursion (m)
  (declare (xargs :guard (matrixp m)))
  (if (or (m-emptyp (col-cdr m))
          (m-emptyp (row-cdr m)))
      nil
    (col-cdr-recursion (row-cdr m))))

(defthmd col-cdr-def
  (implies (matrixp m)
           (equal (col-cdr m)
                  (if (endp (cdr (row-car m)))
                      nil
                    (row-cons (cdr (row-car m))
                              (col-cdr (row-cdr m))))))
  :rule-classes ((:definition
                  :clique (row-car row-cdr col-cdr row-cons)
                  :controller-alist ((row-car t)
                                     (row-cdr t)
                                     (col-cdr t)
                                     (row-cons t t)))
                 (:induction :pattern (col-cdr m)
                             :scheme (col-cdr-recursion m))))

(defun col-cons-recursion (l m)
  (declare (xargs :guard (col-cons-guard l m)))
  (cond ((endp (cdr l)) nil)
        ((m-emptyp m) (col-cons (cdr l) m))
        (t (col-cons-recursion (cdr l) (row-cdr m)))))

(defthmd col-cons-def
  (implies (col-cons-guard l m)
           (equal (col-cons l m)
                  (row-cons (cons (car l) (row-car m))
                            (if (endp (cdr l))
                                nil
                              (col-cons (cdr l) (row-cdr m))))))
  :rule-classes ((:definition
                  :clique (row-car row-cdr row-cons col-cons)
                  :controller-alist ((row-car t)
                                     (row-cdr t)
                                     (row-cons t t)
                                     (col-cons t t)))
                 (:induction :pattern (col-cons l m)
                             :scheme (col-cons-recursion l m))))


;;;;; Row and column simplification rules

;;;; Simple row operation reductions

(defthm row-car-row-cons
  (equal (row-car (row-cons l m)) l))

(defthm row-cdr-empty
  (implies (and (equal (row-count m) 1)
                (matrixp m))
           (equal (row-cdr m) nil)))

(defthm row-cdr-row-cons
  (equal (row-cdr (row-cons l m)) m))

(defthm row-cons-elim-nil
  (implies (and (m-emptyp (row-cdr m))
                (matrixp m)
                (not (m-emptyp m)))
           (equal (row-cons (row-car m) nil)
                  m)))

(defthm row-cons-elim
  (implies (not (m-emptyp m))
           (equal (row-cons (row-car m) (row-cdr m))
                  m))
  :rule-classes :rewrite)

;;;; Simple column operation reductions

(local
 (defthm col-car-col-cons-impl
   (implies (mvectorp l)
            (equal (col-car (col-cons-impl l m))
                   l))))

(defthm col-car-col-cons
  (implies (col-cons-guard l m)
           (equal (col-car (col-cons l m)) l)))

(local
 (defthm col-cdr-col-cons-impl-nil
   (equal (col-cdr (col-cons-impl l nil)) nil)))

(local
 (defthm col-cdr-col-cons-impl
   (implies (and (mvectorp l)
                 (>= (len l) (len m))
                 (and (vector-list-of-lenp m i)
                      (< 0 i)))
            (equal (col-cdr (col-cons-impl l m)) m))
   :rule-classes ((:rewrite :match-free :once))))

(defthm col-cdr-empty
  (implies (equal (col-count m) 1)
           (equal (col-cdr m) nil)))

(defthm col-cdr-col-cons
  (implies (col-cons-guard l m)
           (equal (col-cdr (col-cons l m)) m)))

(defthm col-cons-elim-nil
  (implies (and (m-emptyp (col-cdr m))
                (matrixp m)
                (not (m-emptyp m)))
           (equal (col-cons (col-car m) nil)
                  m)))

(defthm col-cons-elim
  (implies (and (matrixp m)
                (not (m-emptyp m)))
           (equal (col-cons (col-car m) (col-cdr m))
                  m)))

;;;; Joint row col reductions.

;;;; The first four are not enabled, because they should be handled
;;;; by the logical definitions of row-car and col-car.
(defthmd row-car-col-cdr
  (implies (matrixp m)
           (equal (row-car (col-cdr m))
                  (cdr (row-car m)))))

(defthmd col-car-row-cdr
  (implies (matrixp m)
           (equal (col-car (row-cdr m))
                  (cdr (col-car m)))))

(defthmd row-car-col-cons
  (implies (consp l)
           (equal (row-car (col-cons l m))
                  (cons (car l) (row-car m)))))

(defthmd col-car-row-cons
  (implies (consp l)
           (equal (col-car (row-cons l m))
                  (cons (car l) (col-car m)))))

;;;; The car of row-car equals the car of col-car.  It may be a good
;;;; idea to convert this to a single term, but for now a forward-chaining
;;;; rule is used.
(defthm car-row-car-car-col-car
  (equal (car (row-car m))
         (car (col-car m)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((car (row-car m)) (car (col-car m))))))

(local
 (defthm not-col-cdr-local
   (implies (vector-list-of-lenp m 1)
            (not (col-cdr m)))))

;;;; col-cdr row-cdr can be rotated, but it is not clear when this is
;;;; a good idea, so forward-chaining is used in lieu of rewriting.
(defthm col-cdr-row-cdr
  (implies (matrixp m)
           (equal (col-cdr (row-cdr m))
                  (row-cdr (col-cdr m))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((col-cdr (row-cdr m))
                                  (row-cdr (col-cdr m))))))

(defthm col-cdr-row-cons
  (implies (row-cons-guard l m)
           (equal (col-cdr (row-cons l m))
                  (if (equal (len l) 1)
                      nil
                    (row-cons (cdr l) (col-cdr m))))))

;;;; As a general rule, row operations are kept on the outside, so this is
;;;; not normally enabled.
(defthmd row-cdr-col-cons
  (implies (col-cons-guard l m)
           (equal (row-cdr (col-cons l m))
                  (if (equal (len l) 1)
                      nil
                    (col-cons (cdr l) (row-cdr m))))))

;;;; Theorems relating row-cons and col-cons together.

(defthm col-cons-row-cons-unit
  (implies (and (equal (len l) 1)
                (mvectorp l))
           (equal (col-cons l nil)
                  (row-cons l nil))))

(defthm col-cons-row-cons
  (implies (and (matrixp m)
                (consp k)
                (or (case-split (m-emptyp m))
                    (equal (col-count m) (len k)))
                (equal (1+ (row-count m)) (len l)))
           (equal (col-cons l (row-cons k m))
                  (if (m-emptyp m)
                      (row-cons (cons (car l) k) nil)
                    (row-cons (cons (car l) k) (col-cons (cdr l) m))))))

(defthm row-cons-col-cons-empty
  (implies (and (mvectorp k)
                (consp k)
                (mvectorp l)
                (equal (len l) 1))
           (equal (row-cons l (col-cons k nil))
                  (col-cons (cons (car l) k) nil))))

;;;; Row ops are kept on outside, so not normally enabled
(defthmd row-cons-col-cons
  (implies (and (matrixp m)
                (not (m-emptyp m))
                (mvectorp k)
                (equal (len k) (row-count m))
                (mvectorp l)
                (equal (len l) (1+ (col-count m))))
           (equal (row-cons l (col-cons k m))
                  (col-cons (cons (car l) k) (row-cons (cdr l) m)))))

;;;; Theorems for row-count

(defthm row-count-type
  (and (integerp (row-count m))
       (<= 0 (row-count m)))
  :rule-classes :type-prescription)

(defthm row-count-type-not-empty
  (implies (not (m-emptyp m))
           (< 0 (row-count m)))
  :rule-classes :type-prescription)

(defun row-count-recursion (m)
  (declare (xargs :guard (matrixp m)))
  (if (m-emptyp m)
      0
    (row-count-recursion (row-cdr m))))

;;; Row count's logical definition
(defthm row-count-def
  (equal (row-count m)
         (if (m-emptyp m)
             0
           (1+ (row-count (row-cdr m)))))
  :rule-classes :definition)

(defthm row-count-implies-empty
  (equal (equal (row-count m) 0)
         (m-emptyp m)))

(defthm row-count-implies-not-empty
  (equal (< 0 (row-count m))
         (not (m-emptyp m))))

(local
 (defthm len-col-cdr
   (implies (and (vector-list-of-lenp m i)
                 (< 1 i))
            (equal (len (col-cdr m))
                   (len m)))
   :rule-classes ((:rewrite :match-free :once))))

(defthm row-count-col-cdr
  (implies (and (case-split (not (m-emptyp (col-cdr m))))
                (matrixp m))
           (equal (row-count (col-cdr m))
                  (row-count m))))

(local
 (defthm len-col-cons
   (equal (len (col-cons-impl l m))
          (len l))))

(defthm row-count-col-cons
  (implies (consp l)
           (equal (row-count (col-cons l m))
                  (len l))))

(defthm row-count-row-cdr-col-cdr
  (implies (and (matrixp m)
                (not (m-emptyp (col-cdr m))))
           (equal (row-count (row-cdr (col-cdr m)))
                  (row-count (row-cdr m)))))

(defthm len-col-car
  (implies (matrixp m)
           (equal (len (col-car m))
                  (row-count m))))

(defthmd <=-len-col-car
  (<= (len (col-car m))
      (row-count m)))

(defthmd <=-row-count-col-cdr
  (<= (row-count (col-cdr m))
      (row-count m)))

;;;; Theorems for column count.

(defthm col-count-type
  (and (integerp (col-count m))
       (<= 0 (col-count m)))
  :rule-classes :type-prescription)

(defthm col-count-type-not-empty
  (implies (and (not (m-emptyp m))
                (matrixp m))
           (< 0 (col-count m)))
  :rule-classes :type-prescription)

(defun col-count-recursion (m)
  (declare (xargs :guard (matrixp m)))
  (if (m-emptyp m)
      0
    (col-count-recursion (col-cdr m))))

;;; Column count's logical definition.
(defthm col-count-def
  (implies (matrixp m)
           (equal (col-count m)
                  (if (m-emptyp m)
                      0
                    (1+ (col-count (col-cdr m))))))
  :rule-classes :definition)

(defthm col-count-implies-empty
  (implies (matrixp m)
           (equal (equal (col-count m) 0)
                  (m-emptyp m))))

(defthm col-count-implies-not-empty
  (implies (matrixp m)
           (equal (< 0 (col-count m))
                  (not (m-emptyp m)))))

(defthm col-count-row-cdr
  (implies (and (case-split (not (m-emptyp (row-cdr m))))
                (matrixp m))
           (equal (col-count (row-cdr m))
                  (col-count m))))

(defthm col-count-row-cons
  (equal (col-count (row-cons l m))
         (len l)))

(defthm col-count-col-cdr-row-cdr
  (implies (and (matrixp m)
                (not (m-emptyp (row-cdr m))))
           (equal (col-count (col-cdr (row-cdr m)))
                  (col-count (col-cdr m)))))

(defthm len-row-car
  (equal (len (row-car m))
         (col-count m)))

;;; Disable low level functions.
(in-theory (disable matrixp m-emptyp
                    vector-list-of-lenp
                    row-car row-cdr row-cons
                    col-car col-cdr col-cons
                    row-count col-count))
