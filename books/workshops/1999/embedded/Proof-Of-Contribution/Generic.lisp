;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Section 1: preliminary definitions and lemmas
;; (some are taken from Boyer and Moore's ``small machine''
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm constant-fold-+
  (implies (acl2::syntaxp (and (quotep x) (quotep y)))
           (equal (+ x (+ y z)) (+ (+ x y) z))))

(defthm commutativity2-of-+
  (equal (+ x y z) (+ y x z))
  :hints (("goal" :use ((:instance acl2::associativity-of-+
                                   (acl2::x y)
                                   (acl2::y x)
                                   (acl2::z z))
                        (:instance acl2::associativity-of-+
                                   (acl2::x x)
                                   (acl2::y y)
                                   (acl2::z z))
                        (:instance acl2::commutativity-of-+
                                   (acl2::x x)
                                   (acl2::y y)))
           :in-theory (disable acl2::associativity-of-+
                               acl2::commutativity-of-+))))

(defthm commutativity2-of-*
  (equal (* x y z) (* y x z))
  :hints (("goal" :use ((:instance acl2::associativity-of-*
                                   (acl2::x y)
                                   (acl2::y x)
                                   (acl2::z z))
                        (:instance acl2::associativity-of-*
                                   (acl2::x x)
                                   (acl2::y y)
                                   (acl2::z z))
                        (:instance acl2::commutativity-of-*
                                   (acl2::x x)
                                   (acl2::y y)))
           :in-theory (disable acl2::associativity-of-*
                               acl2::commutativity-of-*))))
#|
(defthm plus-right-id
  (equal (+ x 0) (acl2::fix x)))
|#

(defthm *-0 (equal (* 0 x) 0))

#|
(defthm +-cancellation1
  (equal (+ i j (* -1 i) k)
         (+ j k)))
|#


;;
;; in-range (idx l)          predicate:   true iff 0 <= idx < |l|
;; natp(n)                   predicate:   true iff n is natural number
;; firstn   (n l)            head of n elements of l
;; equal-elements (el l)     predicate: true iff   l = < el el el ... el >
;;

#|
(defun in-range (idx l)
 (and
  (integerp idx)
  (>= idx 0)
  (< idx (len l))))
|#





(defun equal-elements (el l)
 (if (endp l)
     (null l)
     (and
      (equal el (car l))
      (equal-elements el (cdr l)))))
#|
(defthm equal-elements-means-every-elements-matches
 (implies
  (and
   (in-range idx l)
   (equal-elements el l))
  (equal (nth idx l) el)))
|#

;;;
;;; Definition of a constant residue number system for the Gem2Rtm translation.
;;;

(defconst *rns* '(11 13 15 17 19))



