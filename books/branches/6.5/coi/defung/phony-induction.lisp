#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "DEFUNG")

(include-book "coi/generalize/generalize" :dir :system)

;; With phony induction it looks like we can induce ACL2 to generalize
;; and induct on the original goal without specialized hints.

(defmacro def::phony-induction (fn args)

  (let* ((phony-test           (symbol-fns::suffix fn '-phony-test))
	 (phony-induction      (symbol-fns::suffix fn '-phony-induction))
	 (phony-induction-rule (symbol-fns::suffix fn '-phony-induction-rule)))

    `(encapsulate
	 ()
       
       (defun ,phony-test (,@args) 
	 (declare (ignore ,@args)) nil)
       
       (local (in-theory (disable (:type-prescription ,phony-test))))
       
       (defun ,phony-induction (,@args)
	 (declare (xargs :measure 0))
	 (if (,phony-test ,@args) (,phony-induction ,@args) nil))
       
       (defthm ,phony-induction-rule t
	 :rule-classes ((:induction :pattern (,fn ,@args)
				    :scheme (,phony-induction ,@args))))
       
       )))


(local
 (encapsulate
     ()

   (defun goo (x)
     (if (zp x) 0
       (goo (1- x))))
   
   (in-theory (disable (:type-prescription goo)))
   
   (defun hoo (x) 
     (declare (ignore x)) 0)
   
   (defthm hoo-is-goo
     (equal (hoo x) (goo (gensym::generalize x)))
     :otf-flg t
     :hints (("Goal" :expand (:free (x) (gensym::generalize x)))))
   
   (in-theory (disable (:type-prescription hoo) hoo))
   
   (def::phony-induction hoo (x))
   
   (defstub arg () nil)

   (acl2::add-generalization-pattern (arg))

   (defthm bar
     (integerp (hoo (arg)))
     :hints (("Goal" :induct (hoo (arg)))))

   ))

   
