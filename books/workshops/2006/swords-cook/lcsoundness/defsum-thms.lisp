

;; This book should be included wherever deftypes or defsum is used.
;; It can be, and probably should be, local to the book in which the defsum
;; or deftypes is defined, since these rules can be disruptive.

(in-package "ACL2")

(include-book "arithmetic-3/bind-free/top" :dir :system)
; (set-default-hints! '((nonlinearp-default-hint stable-under-simplificationp
;                                              hist pspv)))
(set-minimal-arithmetic-theory)
;;(include-book "structure-measure")
;;(include-book "data-structures/list-theory" :dir :system)

(defthm nth-open
  (implies (not (zp n))
           (equal (nth n x)
                  (nth (1- n) (cdr x)))))

(defthm update-nth-open
  (implies (not (zp n))
           (equal (update-nth n val x)
                  (cons (car x)
                        (update-nth (1- n) val (cdr x))))))

(in-theory (disable nth-open
                    update-nth-open))

(defthm true-listp-update-nth-rewrite
  (implies (true-listp x)
           (true-listp (update-nth n v x))))


(defthm equal-len-0
  (equal (equal 0 (len x))
         (atom x)))

(defthm acl2-count-nth-measure
  (implies (consp x)
           (< (acl2-count (nth n x))
              (acl2-count x)))
  :rule-classes (:rewrite :linear))

(defthm acl2-count-consp-posp
  (implies (consp x)
           (posp (acl2-count x))))


(defthm acl2-count-0-len-0
  (implies (equal (acl2-count x) 0)
           (< (len x) 1))
  :rule-classes :linear)

(defthm acl2-count-nth-len-2
  (implies (<= 2 (len x))
           (< (+ 1 (acl2-count (nth n x)))
              (acl2-count x)))
  :hints (("Goal" :induct (nth n x))
          ("Subgoal *1/3.2"
           :use (:instance acl2-count-nth-measure
                           (x (cdr x))
                           (n (+ -1 n)))))
  :rule-classes (:rewrite :linear))