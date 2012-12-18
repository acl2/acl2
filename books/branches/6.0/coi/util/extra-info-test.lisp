#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "extra-info")
(include-book "make-event/eval" :dir :system)

; We have to disable tau for this whole file.  The reason is that the
; author is taking advantage of disable to make a defined function, e.g., 
; (defun foo (x) t), seem like a constrained function.  Note, for example, the
; must-fail below, when in fact the theorem is trivial if the definition is not
; hidden -- and tau ``sees'' the definition whether foo is enabled or not!

(in-theory (disable (:executable-counterpart tau-system)))

(defun foo (x)
  (declare (ignore x))
  t)

(in-theory (disable foo (:type-prescription foo) (foo)))

(defun zoo (x)
  (declare (ignore x))
  t)

(in-theory (disable zoo (:type-prescription zoo) (zoo)))


(defun goo (x) (foo x))
(defun hoo (x) (foo x))

(in-theory (disable goo hoo))

(defun xoo (x)
  (declare (ignore x))
  t)

(in-theory (disable xoo (:type-prescription xoo) (xoo)))

(encapsulate
    ()

  (local (in-theory (enable goo hoo zoo foo)))

  (defthm xoo-implies-goo
    (implies
     (xoo x)
     (goo x)))
  
  (defthm xoo-implies-hoo
    (implies
     (xoo x)
     (hoo x)))
  
  (defthm backchaining-rule
    (implies
     (foo x)
     (zoo x)))
  )

;; Here is a case-split generating rule whose result we
;; want to monitor ..

(defthm foo-rule
  (iff (foo x)
       (if (oddp x) (rule-info 'foo-rule `(oddp ,x) (goo x))
	 (rule-info 'foo-rule `(evenp ,x) (hoo x))))
  :hints (("Goal" :in-theory (enable goo hoo))))

;;
;; General case ..
;;

(must-fail
 (defthmd test
   (zoo x)
   :otf-flg t
   :hints (("Goal" :cases ((foo x))))))

;;
;; Backchaining test ..
;;

(defthm xoo-implies-zoo
  (implies
   (xoo x)
   (zoo x)))

(defun koo (x)
  (declare (ignore x))
  t)

(in-theory (disable koo (:type-prescription koo) (koo)))


(defthm koo-to-foo
  (implies
   (not (zoo x))
   (equal (koo x) (foo x)))
  :hints (("Goal" :in-theory (enable koo foo))))

(must-fail
 (defthmd test
   (zoo x)
   :otf-flg t
   :hints (("Goal" :cases ((koo x))))))