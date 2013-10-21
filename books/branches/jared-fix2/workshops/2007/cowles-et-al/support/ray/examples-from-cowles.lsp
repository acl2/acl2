(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Include Sandip's generic solution book
;; (local
;;  (include-book "generic-ray"
;; 	       :uncertified-okp nil
;; 	       :defaxioms-okp nil    
;; 	       :skip-proofs-okp nil))

;; Start with some of Bill's defs

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Bill Young's challenge 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate 
 ()

 (defun op (stmt)
   (first stmt))
 
 (defun arg1 (stmt)
   (second stmt))

 (defun arg2 (stmt)
   (third stmt))
 
 (defun arg3 (stmt)
   (fourth stmt))
 
 (defmacro val (key alist)
   `(cdr (assoc-equal ,key ,alist)))
 
 (defmacro tlistp (x n)
   `(and (true-listp ,x)
         (equal (len ,x) ,n)))
 
 (defun  definedp (x alist)
   (if (endp alist)
       nil
     (if (equal x (caar alist))
         t
       (definedp x (cdr alist)))))
 
 (defun varp (x alist)
   (and (symbolp x)
        (definedp x alist)))
 
 (defun exprp (x alist)
   (or (integerp x)
       (varp x alist)))
 
 (defun eval-expr (expr alist)
   (if (integerp expr)
       expr
     (val expr alist)))
 
 ;; An assignment statement has form: (assign var expr)
 
 (defun run-assignment (stmt alist)
   (let* ((v (arg1 stmt))
          (e (arg2 stmt))
          (val (eval-expr e alist)))
     (put-assoc-equal v val alist)))
 
 
 (defun test1-eg (stmt mem)  ;; No recursion when true
   (case (op stmt)
     (skip      t)
     (assign    t)
     (sequence  nil)
     (if        nil)
     (while     (zerop (eval-expr (arg1 stmt) mem)))
     (otherwise t)))
 
 (defun test2-eg (stmt mem)  ;; Only tail recursion when true
   (declare (ignore mem))
   (case (op stmt)
     (skip      nil)
     (assign    nil)
     (sequence  nil)
     (if        t)
     (while     nil)
     (otherwise nil)))
 
 (defun
   finish-eg (stmt mem)  ;; Non-recursive base steps
   (case (op stmt)
     (skip      mem)
     (assign    (run-assignment stmt mem))
     (sequence  mem)   
     (if        mem)
     (while     mem)
     (otherwise mem)))
 
 (defun dst1-eg (stmt mem) 
   ;; Modify non-recursive parameter(stmt) in tail or inner call
   (case (op stmt)
     (skip      stmt)
     (assign    stmt)
     (sequence  (arg1 stmt))
     (if        (if (zerop (eval-expr (arg1 stmt) mem))
                    (arg3 stmt)
                  (arg2 stmt)))
     (while     (arg2 stmt))
     (otherwise stmt)))
 
 (defun dst2-eg (stmt mem1 mem2) 
   ;; Modify non-recursive parameter(stmt) in outer call
   (declare (ignore mem1 mem2))
   (case (op stmt)
     (skip      stmt)
     (assign    stmt)
     (sequence  (arg2 stmt))
     (if        stmt)
     (while     stmt)
     (otherwise stmt)))
 
 (defun stp-eg (stmt mem)    
   ;; Modify recursive parameter(mem) in tail or inner call
   (case (op stmt)
     (skip      mem)
     (assign    mem)
     (sequence  mem)
     (if        mem)
     (while     mem)
     (otherwise mem)))
 
 (defun run-eg-clk (x st clk)
   (declare (xargs :measure (nfix clk)))
   (cond ((zp clk) nil)
         ((equal st nil) st)
         ((test1-eg x st) (finish-eg x st))
         ((test2-eg x st) (run-eg-clk (dst1-eg x st) (stp-eg x st) (1- clk)))
         (t (let ((st2 (run-eg-clk (dst1-eg x st) (stp-eg x st) (1- clk))))
              (if (equal st2 nil)
                  nil
                (run-eg-clk (dst2-eg x st st2) st2 (1- clk)))))))
 
 (defun-sk exists-enough-eg (x st)
   (exists clk 
           (and (natp clk)
                (not (equal (run-eg-clk x st clk) nil)))))
 
 (defun run-eg (x st)
   (if (exists-enough-eg x st)
       (run-eg-clk x st (exists-enough-eg-witness x st))
     nil))
 
 (local (include-book "reflexive"))
 
 (defthm Run-eg-satisfies-specification
   (equal (run-eg stmt mem)
          (if (null mem)
              nil
            (case (op stmt)
              (skip      mem)
              (assign    (run-assignment stmt mem))
              (sequence  (run-eg (arg2 stmt)(run-eg (arg1 stmt) mem)))
              (if        (if (zerop (eval-expr (arg1 stmt) mem))
                             (run-eg (arg3 stmt) mem)
                           (run-eg (arg2 stmt) mem)))
              (while     (if (zerop (eval-expr (arg1 stmt) mem))
                             mem
                           (run-eg stmt (run-eg (arg2 stmt) mem))))
              (otherwise mem))))
   :rule-classes nil
   :hints (("Goal"
            :use (:instance
                  (:functional-instance
                   |definition of run|
                   (run run-eg)
                   (run-clk run-eg-clk)
                   (exists-enough exists-enough-eg)
                   (exists-enough-witness exists-enough-eg-witness)
                   (BTM (lambda () nil))
                   (test1 test1-eg)
                   (test2 test2-eg)
                   (finish finish-eg)
                   (dst1 dst1-eg)
                   (dst2 dst2-eg)
                   (stp stp-eg))
                  (x stmt)
                  (st mem))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: Ackermann's function
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ()

 (defun Test1-A (x y)     ;; No recursion when true
   (cond ((= x 0) t)
         ((= y 0) nil)
         (t       nil)))
 
 (defun test2-A (x y)     ;; Only tail recursion when true
   (cond ((= x 0) nil)
         ((= y 0) t)
         (t       nil)))
 
 (defun finish-A (x y)    ;; Non-recursive base step
   (cond ((= x 0) (+ 1 y))
         ((= y 0) y)
         (t       y)))
 
 (defun dst1-A (x y)   
   ;; Modify non-recursive parameter(x) in tail or inner call
   (cond ((= x 0) x)
         ((= y 0) (+ -1 x))
	(t       x)))

 (defun dst2-A (x y1 y2)  ;; Modify non-recursive parameter(x) in outer call
   (declare (ignore y2))
   (cond ((= x 0)  x)
         ((= y1 0) x)
         (t        (+ -1 x))))
 
 (defun stp-A (x y)
   ;; Modify recursive parameter(y) in tail or inner call
   (cond ((= x 0) y)
	((= y 0) 1)
	(t       (+ -1 y))))

 (defun A-clk (x st clk)
   (declare (xargs :measure (nfix clk)))
   (cond ((zp clk) nil)
         ((equal st nil) st)
         ((test1-A x st) (finish-A x st))
         ((test2-A x st) (A-clk (dst1-A x st) (stp-A x st) (1- clk)))
         (t (let ((st2 (A-clk (dst1-A x st) (stp-A x st) (1- clk))))
              (if (equal st2 nil)
                  nil
                (A-clk (dst2-A x st st2) st2 (1- clk)))))))
 
 (defun-sk exists-enough-A (x st)
   (exists clk 
           (and (natp clk)
                (not (equal (A-clk x st clk) nil)))))
 
 (defun A (x st)
   (if (exists-enough-A x st)
       (A-clk x st (exists-enough-A-witness x st))
     nil))
 
 (local (include-book "reflexive"))
 
 (defthm
   A-satisfies-specification
   (equal (A x y)
          (if (equal y nil)
              nil
            (cond ((= x 0)
                   (+ 1 y))
                  ((= y 0)
                   (A (+ -1 x) 1))
                  (t (A (+ -1 x) (A x (+ -1 y)))))))
   :rule-classes nil
   :hints (("Goal"
            :use (:instance
                  (:functional-instance
                   |definition of run|
                   (run A)
                   (run-clk A-clk)
                   (exists-enough exists-enough-A)
                   (exists-enough-witness exists-enough-A-witness)
                   (BTM (lambda () nil))
                   (test1 test1-A)
                   (test2 test2-A)
                   (finish finish-A)
                   (dst1 dst1-A)
                   (dst2 dst2-A)
                   (stp stp-A))
                  (st y))))))
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: More than two inputs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ()

 (defun Test1-A1-temp (x1 z)     ;; No recursion when true
   (let ((x (car x1))
         (y (cadr x1)))
     (declare (ignore y))
     (cond ((= x 0)       t)
           ((and (<= x 2)
                 (= z 0)) t)
           ((and (> x 2)
                 (= z 0)) t)
           (t             nil))))
 
 (defun test2-A1-temp (x1 z)     ;; Only tail recursion when true
   (let ((x (car x1))
         (y (cadr x1)))
     (declare (ignore y))
     (cond ((= x 0)       nil)
           ((and (<= x 2)
                 (= z 0)) nil)
           ((and (> x 2)
                 (= z 0)) nil)
           (t             nil))))
 
 (defun finish-A1-temp (x1 z)    ;; Non-recursive base step
  (let ((x (car x1))
	(y (cadr x1)))
    (cond ((= x 0)       (+ y z))
	  ((and (<= x 2)
		(= z 0)) (+ -1 x))
	  ((and (> x 2)
		(= z 0)) (fix y))
          ;; (fix y) ensures nil is returned only when z is nil
	  (t             z))))
 
 (defun dst1-A1-temp (x1 z)   
   ;; Modify non-recursive parameter(x1) in tail or inner call
   (let ((x (car x1))
         (y (cadr x1)))
     (cond ((= x 0)       x1)
	  ((and (<= x 2)
		(= z 0)) x1)
	  ((and (> x 2)
		(= z 0)) x1)
	  (t             (list x y)))))
 
 (defun dst2-A1-temp (x1 z1 z2)  
   ;; Modify non-recursive parameter(x1) in outer call
   (declare (ignore z2))
   (let ((x (car x1))
         (y (cadr x1)))
     (cond ((= x 0)        x1)
           ((and (<= x 2)
                 (= z1 0)) x1)
           ((and (> x 2)
                 (= z1 0)) x1)
           (t              (list (+ -1 x) y)))))
 
 (defun stp-A1-temp (x1 z)
   ;; Modify recursive parameter(z) in tail or inner call
   (let ((x (car x1))
         (y (cadr x1)))
     (declare (ignore y))
     (cond ((= x 0)        z)
           ((and (<= x 2)
                 (= z 0))  z)
           ((and (> x 2)
                 (= z 0))  z)
           (t              (+ -1 z)))))
 
 (defun A1-temp-clk (x st clk)
   (declare (xargs :measure (nfix clk)))
   (cond ((zp clk) nil)
         ((equal st nil) st)
         ((test1-A1-temp x st) (finish-A1-temp x st))
         ((test2-A1-temp x st) (A1-temp-clk (dst1-A1-temp x st)
                                            (stp-A1-temp x st)
                                            (1- clk)))
         (t (let ((st2 (A1-temp-clk (dst1-A1-temp x st)
                                    (stp-A1-temp x st)
                                    (1- clk))))
              (if (equal st2 nil)
                  nil
                (A1-temp-clk (dst2-A1-temp x st st2) st2 (1- clk)))))))
 
 (defun-sk exists-enough-A1-temp (x st)
   (exists clk 
           (and (natp clk)
                (not (equal (A1-temp-clk x st clk) nil)))))
 
 (defun A1-temp (x st)
   (if (exists-enough-A1-temp x st)
       (A1-temp-clk x st (exists-enough-A1-temp-witness x st))
     nil))
 
 (defun A1-temp (x st)
   (if (exists-enough-A1-temp x st)
       (A1-temp-clk x st (exists-enough-A1-temp-witness x st))
     nil))
 
 (defun A1 (x y z)
   (A1-temp (list x y) z))
 
 (local (include-book "reflexive"))

 (defthm A1-satisfies-specification
  (equal (A1 x y z)
	 (if (equal z nil)
	     nil
           (cond ((= x 0)
                  (+ y z))
                 ((and (<= x 2)
                       (= z 0))
                  (+ -1 x))
                 ((and (> x 2)
                       (= z 0))
                  (fix y))
                 (t (A1 (+ -1 x) y (A1 x y (+ -1 z)))))))
  :rule-classes nil
  :otf-flg t
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  |definition of run|
		  (run A1-temp)
		  (run-clk A1-temp-clk)
		  (exists-enough exists-enough-A1-temp)
		  (exists-enough-witness exists-enough-A1-temp-witness)
		  (BTM (lambda () nil))
		  (test1 test1-A1-temp)
		  (test2 test2-A1-temp)
		  (finish finish-A1-temp)
		  (dst1 dst1-A1-temp)
		  (dst2 dst2-A1-temp)
		  (stp stp-A1-temp))
		 (x (list x y))
		 (st z))))))
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 4: Less than two inputs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate 
 ()
 (defstub test1-1 (st) t)    ;; No recursion when true
 (defstub test2-1 (st) t)    ;; Only tail recursion when true
 (defstub stp-1 (st) t)      ;; Modify parameter(st) in tail or inner call
 
 (encapsulate 
  (((btm-1) => *)
   ((finish-1 *) => *))      ;; Non-recursive base step
  
  (local (defun btm-1 () nil))
  (local (defun finish-1 (st) st))
  
  (defthm finish-1-is-not-btm-1
    (implies (not (equal st (btm-1)))
             (not (equal (finish-1 st) (btm-1))))))
 
 (defun Test1-1-temp (x st)     
   ;; No recursion when true
   (declare (ignore x))
   (cond ((test1-1 st) t)
         ((test2-1 st) nil) 
         (t            nil)))
 
 (defun test2-1-temp (x st)     
   ;; Only tail recursion when true
   (declare (ignore x))
   (cond ((test1-1 st) nil)
         ((test2-1 st) t) 
         (t            nil)))
 
 (defun finish-1-temp (x st)    ;; Non-recursive base step
   (declare (ignore x))
   (cond ((test1-1 st) (finish-1 st))
         ((test2-1 st) st) 
         (t            st)))
 
 (defun dst1-1-temp (x st)      
   ;; Modify non-recursive parameter(x) in tail or inner call
   (declare (ignore st))
   x)
 
 (defun dst2-1-temp (x st1 st2)  
   ;; Modify non-recursive parameter(x) in outer call
   (declare (ignore st1 st2))
   x)
 
 (defun stp-1-temp (x st)
   ;; Modify recursive parameter(st) in tail or inner call
   (declare (ignore x))
   (cond ((test1-1 st) st)
         ((test2-1 st) (stp-1 st))
         (t            (stp-1 st))))
 
 (defun generic-run-1-temp-clk (x st clk)
   (declare (xargs :measure (nfix clk)))
   (cond ((zp clk) (BTM-1))
         ((equal st (BTM-1)) st)
         ((test1-1-temp x st) (finish-1-temp x st))
         ((test2-1-temp x st) (generic-run-1-temp-clk (dst1-1-temp x st)
                                                      (stp-1-temp x st)
                                                      (1- clk)))
         (t (let ((st2 (generic-run-1-temp-clk (dst1-1-temp x st) 
                                               (stp-1-temp x st)
                                               (1- clk))))
              (if (equal st2 (BTM-1))
                  (BTM-1)
                (generic-run-1-temp-clk (dst2-1-temp x st st2) 
                                        st2 
                                        (1- clk)))))))
 
 (defun-sk exists-enough-generic-run-1-temp (x st)
   (exists clk 
           (and (natp clk)
                (not (equal (generic-run-1-temp-clk x st clk) (BTM-1))))))

 (defun generic-run-1-temp (x st)
   (if (exists-enough-generic-run-1-temp x st)
       (generic-run-1-temp-clk x st 
                               (exists-enough-generic-run-1-temp-witness x st))
     (BTM-1)))

 (defun generic-run-1 (st)
   (generic-run-1-temp 0 st))

(defthm |Definition of generic-run-1|
  (equal (generic-run-1 st)
         (cond ((equal st (btm-1)) (btm-1))
               ((test1-1 st) (finish-1 st))
               ((test2-1 st) (generic-run-1 (stp-1 st)))
               (t (let ((st2 (generic-run-1 (stp-1 st))))
                    (generic-run-1 st2)))))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  |definition of run|
		  (run generic-run-1-temp)
		  (run-clk generic-run-1-temp-clk)
		  (exists-enough exists-enough-generic-run-1-temp)
		  (exists-enough-witness 
                   exists-enough-generic-run-1-temp-witness)
		  (BTM BTM-1)
		  (test1 test1-1-temp)
		  (test2 test2-1-temp)
		  (finish finish-1-temp)
		  (dst1 dst1-1-temp)
		  (dst2 dst2-1-temp)
		  (stp stp-1-temp))
		 (x 0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5: Using single arity to introduce ackermann
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ()

 (defun test1-1-m91 (x)     ;; No recursion when true
   (> x 100))

 (defun test2-1-m91 (x)     ;; Only tail recursion when true
   (declare (ignore x))
   nil)

 (defun finish-1-m91 (x)    ;; Non-recursive base step
   (+ -10 x))
 
 (defun stp-1-m91 (x)
   ;; Modify parameter(x) in tail or inner call
   (+ 11 x))

 (defun Test1-1-m91-temp (x st)     
   ;; No recursion when true
   (declare (ignore x))
   (cond ((test1-1-m91 st) t)
         ((test2-1-m91 st) nil) 
         (t                nil)))

 (defun  test2-1-m91-temp (x st)     ;; Only tail recursion when true
   (declare (ignore x))
   (cond ((test1-1-m91 st) nil)
         ((test2-1-m91 st) t) 
         (t                nil)))

 (defun finish-1-m91-temp (x st)    
   ;; Non-recursive base step
   (declare (ignore x))
   (cond ((test1-1-m91 st) (finish-1-m91 st))
         ((test2-1-m91 st) st) 
         (t                st)))

 (defun stp-1-m91-temp (x st)
   ;; Modify recursive parameter(st) in tail or inner call
   (declare (ignore x))
   (cond ((test1-1-m91 st) st)
         ((test2-1-m91 st) (stp-1-m91 st))
         (t                (stp-1-m91 st))))

 (defun m91-temp-clk (x st clk)
   (declare (xargs :measure (nfix clk)))
   (cond ((zp clk) nil)
         ((equal st nil) st)
         ((test1-1-m91-temp x st) (finish-1-m91-temp x st))
         ((test2-1-m91-temp x st) (m91-temp-clk (dst1-1-temp x st)
                                                (stp-1-m91-temp x st)
                                                (1- clk)))
         (t (let ((st2 (m91-temp-clk (dst1-1-temp x st) 
                                     (stp-1-m91-temp x st)
                                     (1- clk))))
              (if (equal st2 nil)
                  nil
                (m91-temp-clk (dst2-1-temp x st st2)
                              st2
                              (1- clk)))))))
 
 (defun-sk exists-enough-m91-temp (x st)
   (exists clk 
           (and (natp clk)
                (not (equal (m91-temp-clk x st clk) nil)))))

 (defun m91-temp (x st)
   (if (exists-enough-m91-temp x st)
       (m91-temp-clk x st (exists-enough-m91-temp-witness x st))
     nil))

(defun M91 (st)
  (m91-temp 0 st))

(defthm M91-satisfies-specification
  (equal (M91 x)
	 (if (equal x nil)
	     nil
           (if (> x 100)
               (+ -10 x)
             (M91 (M91 (+ 11 x))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  |Definition of generic-run-1|
		  (generic-run-1 m91)
		  (generic-run-1-temp m91-temp)
		  (exists-enough-generic-run-1-temp
		   exists-enough-m91-temp)
		  (exists-enough-generic-run-1-temp-witness
		   exists-enough-m91-temp-witness)
		  (generic-run-1-temp-clk m91-temp-clk)
		  (BTM-1 (lambda () nil))
		  (test1-1-temp test1-1-m91-temp)
		  (test2-1-temp test2-1-m91-temp)
		  (finish-1-temp finish-1-m91-temp)
		  (stp-1-temp stp-1-m91-temp)
		  (test1-1 test1-1-m91)
		  (test2-1 test2-1-m91)
		  (finish-1 finish-1-m91)
		  (stp-1 stp-1-m91))
		 (st x)))))


;; Now we introduce a function k with more than 3 depths of recursion
;; and one input parameter.

(defun test1-g-temp (p x)        ;; No recursion when true
  (let ((flg (car p))
	(n (cadr p)))
    (cond (flg
	   (if (> x 100)
	       t
             nil))
	  (t (if (zp n)
		 t
	         nil)))))

(defun test2-g-temp (p x)     ;; Only tail recursion when true
  (let ((flg (car p))
	(n (cadr p)))
    (cond (flg
	   (if (> x 100)
	       nil
	       t))
	  (t (if (zp n)
		 nil
	         nil)))))

(defun finish-g-temp (p x)    ;; Non-recursive base step
  (let ((flg (car p))
	(n (cadr p)))
    (cond (flg
	   (if (> x 100)
	       (+ -5 x)
	       x))
	  (t (if (zp n)
		 x
	         x)))))

(defun  dst1-g-temp (p x)   
  ;; Modify non-recursive parameter(p) in tail or inner call
  (let ((flg (car p))
	(n (cadr p)))
    (cond (flg
	   (if (> x 100)
	       p
	       (list nil 3)))
	  (t (if (zp n)
		 p
	         (list t 0))))))

(defun dst2-g-temp (p x1 x2)  
  ;; Modify non-recursive parameter(p) in outer call
  (declare (ignore x2))
  (let ((flg (car p))
	(n (cadr p)))
    (cond (flg
	   (if (> x1 100)
	       p
	       p))
	  (t (if (zp n)
		 p
	         (list nil (+ -1 n)))))))

(defun stp-g-temp (p x)
  ;; Modify recursive parameter(x) in tail or inner call
  (let ((flg (car p))
	(n (cadr p)))
    (cond (flg
	   (if (> x 100)
	       x
	       (+ 11 x)))
	  (t (if (zp n)
		 x
	         x)))))

(defun g-temp-clk (x st clk)
  (declare (xargs :measure (nfix clk)))
  (cond ((zp clk) nil)
        ((equal st nil) st)
        ((test1-g-temp x st) (finish-g-temp x st))
        ((test2-g-temp x st) (g-temp-clk (dst1-g-temp x st)
					 (stp-g-temp x st)
					 (1- clk)))
        (t (let ((st2 (g-temp-clk (dst1-g-temp x st)
				  (stp-g-temp x st)
				  (1- clk))))
             (if (equal st2 nil)
                 nil
                 (g-temp-clk (dst2-g-temp x st st2) st2 (1- clk)))))))

(defun-sk exists-enough-g-temp (x st)
  (exists clk 
          (and (natp clk)
               (not (equal (g-temp-clk x st clk) nil)))))

(defun g-temp (x st)
  (if (exists-enough-g-temp x st)
      (g-temp-clk x st (exists-enough-g-temp-witness x st))
    nil))

(defun g (flg n x)
  (g-temp (list flg n) x))

(defthm g-satisfies-specification
  (equal (g flg n x)
	 (cond ((null x)
		nil)
	       (flg
		(if (> x 100)
		    (+ -5 x)
		    (g nil 3 (+ 11 x))))
	       (t (if (zp n)           ;; iterate (g t 0 x)
		      x
		      (g nil 
			 (+ -1 n)
			 (g t 0 x))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  |definition of run|
		  (run g-temp)
		  (run-clk g-temp-clk)
		  (exists-enough exists-enough-g-temp)
		  (exists-enough-witness exists-enough-g-temp-witness)
		  (BTM (lambda () nil))
		  (test1 test1-g-temp)
		  (test2 test2-g-temp)
		  (finish finish-g-temp)
		  (dst1 dst1-g-temp)
		  (dst2 dst2-g-temp)
		  (stp stp-g-temp))
		 (x (list flg n))
		 (st x)))))

(defun
  K (x)
  (g t 0 x))

(defthm K-satisfies-specification
  (equal (K x)
	 (cond ((null x)
		nil)
	       ((> x 100)
		(+ -5 x))
	       (t (K (K (K (+ 11 x)))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition g))
	   :use ((:instance
		  g-satisfies-specification
		  (flg t)
		  (n 0)
		  (x nil))
		 (:instance
		  g-satisfies-specification
		  (flg t)
		  (n 0))
		 (:instance
		  g-satisfies-specification
		  (flg nil)
		  (n 3)
		  (x (+ 11 x)))
		 (:instance
		  g-satisfies-specification
		  (flg nil)
		  (n 2)
		  (x (g t 0 (+ 11 x))))
		 (:instance
		  g-satisfies-specification
		  (flg nil)
		  (n 1)
		  (x (g t 0 (g t 0 (+ 11 x)))))
		 (:instance
		  g-satisfies-specification
		  (flg nil)
		  (n 0)
		  (x (g t 0 (g t 0 (g t 0 (+ 11 x))))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Use Sandip's Generic solution to show, via functional instantiation,
;; that the existence of functions satisfying the following is
;; consistent with the ACL2 logic.
;; -------------------------------------
;; Partial function based on iterating 3 times, a function of x,y,& z.

;; (equal (g flg n x y z)
;;        (cond ((null z)
;;               nil)
;;              (flg
;;               (cond ((zp x)
;;                      (+ y z))
;;                     ((zp y)
;;                      (g t 0 (+ -1 x) 1 z))
;;                     ((zp z)
;;                      (g t 0 x (+ -1 y) 1))
;;                     (t (g nil 3 x y (+ -1 z)))))
;;               (t (if (zp n)
;;                      z
;;                      (let* ((lst (i-g-lst nil n x y z))
;;                             (flga (first lst))
;;                             (na (second lst))
;;                             (xa (third lst))
;;                             (ya (fourth lst)))
;;                        (g nil (+ -1 n) x y (g flga
;;                                               na
;;                                               xa
;;                                               ya
;;                                               z)))))))

;; Here
;; (i-g-lst flg n x y z) returns a list of non-recursive 
;; parameters(flg n x y) used during iteration.

;; For example, if i-g-lst is defined by

;; (defun
;;   i-g-lst (flg n x y z)
;;   (declare (ignore z))
;;   (if flg
;;       (list flg n x y)
;;       (cond ((equal n 3)
;;              (list t 0 x y))
;;             ((equal n 2)
;;              (list t 0 x (+ -1 y)))
;;             ((equal n 1)
;;              (list t 0 (+ -1 x) y))
;;             (t (list flg n x y))))),

;; then
;; (g nil 3 x y (+ 1 z)) = (g nil 2 x y (g t 0 x y (+ -1 z)))
;;                       = (g nil 1 x y (g t 0 x (+ -1 y)(g t 0 x y (+ -1 z))))
;;                       = (g nil 0 x y (g t 
;;                                         0
;;                                         (+ -1 x)
;;                                         y
;;                                         (g t 0 x (+ -1 y)(g t 0 x y (+ -1 z)))))
;;                       = (g t 0 (+ -1 x) y (g t 0 x (+ -1 y)(g t 0 x y (+ -1 z))))

;; Then, using this particular i-g-lst,

;; (g t 0 x y z) = (cond ((null z)
;;                        nil)
;;                       ((zp x)
;;                        (+ y z))
;;                       ((zp y)
;;                        (g t 0 (+ -1 x) 1 z))
;;                       ((zp z)
;;                        (g t 0 x (+ -1 y) 1))
;;                       (t (g t 0 (+ -1 x) y
;;                             (g t 0 x (+ -1 y)
;;                               (g t 0 x y (+ -1 z))))))
;; --------------------------------------
;; The above result shows that there is a function A that satisfies
;; a generalization of Ackermann's function.

;; (equal (A x y z)
;;        (if (null z)
;;            nil
;;          (cond ((zp x)
;;                 (+ y z))
;;                ((zp y)
;;                 (A (+ -1 x) 1 z))
;;                ((zp z)
;;                 (A x (+ -1 y) 1))
;;                (t (A (+ -1 x) y (A x (+ -1 y)(A x y (+ -1 z)))))))



(encapsulate
 (((i-g-lst * * * * *) => *))

 (local
  (defun 
    i-g-lst (flg n x y z)
    (declare (ignore flg n x y z))
    (list 1 2 3 4)))

 (defthm
   List-parts-=-i-g-lst
   (equal (list (car (i-g-lst flg n x y z))
		(cadr (i-g-lst flg n x y z))
		(caddr (i-g-lst flg n x y z))
		(cadddr (i-g-lst flg n x y z)))
	  (i-g-lst flg n x y z)))
 ) ;; end encapsulate

(defun
  test1-g-temp (x1 z)        ;; No recursion when true
  (let ((flg (car x1))
	(n (cadr x1))
	(x (caddr x1))
	(y (cadddr x1)))
    (cond (flg
	   (cond ((zp x)
		  t)
		 ((zp y)
		  nil)
		 ((zp z)
		  nil)
		 (t nil)))
	  (t (if (zp n)
		 t
	         nil)))))

(defun  
  test2-g-temp (x1 z)       ;; Only tail recursion when true
  (let ((flg (car x1))
	(n (cadr x1))
	(x (caddr x1))
	(y (cadddr x1)))
    (cond (flg
	   (cond ((zp x)
		  nil)
		 ((zp y)
		  t)
		 ((zp z)
		  t)
		 (t t)))
	  (t (if (zp n)
		 nil
	         nil)))))

(defun  finish-g-temp (x1 z)    ;; Non-recursive base step
  (let ((flg (car x1))
	(n (cadr x1))
	(x (caddr x1))
	(y (cadddr x1)))
    (cond (flg
	   (cond ((zp x)
		  (+ y z))
		 ((zp y)
		  z)
		 ((zp z)
		  z)
		 (t z)))
	  (t (if (zp n)
		 z
	         z)))))

(defun  dst1-g-temp (x1 z)   ;; Modify non-recursive parameter(x1) in tail or inner call
  (let ((flg (car x1))
	(n (cadr x1))
	(x (caddr x1))
	(y (cadddr x1)))
    (cond (flg
	   (cond ((zp x)
		  x1)
		 ((zp y)
		  (list t 0 (+ -1 x) 1))
		 ((zp z)
		  (list t 0 x (+ -1 y)))
		 (t (list nil 3 x y))))
	  (t (if (zp n)
		 x1
	         (i-g-lst flg n x y z))))))

(defun
  dst2-g-temp (x1 z1 z2)  ;; Modify non-recursive parameter(x1) in outer call
  (declare (ignore z2))
  (let ((flg (car x1))
	(n (cadr x1))
	(x (caddr x1))
	(y (cadddr x1)))
    (cond (flg
	   (cond ((zp x)
		  x1)
		 ((zp y)
		  x1)
		 ((zp z1)
		  x1)
		 (t x1)))
	  (t (if (zp n)
		 x1
	         (list nil (+ -1 n) x y))))))

(defun              ;; Modify recursive parameter(z) in tail or inner call
  stp-g-temp (x1 z)
  (let ((flg (car x1))
	(n (cadr x1))
	(x (caddr x1))
	(y (cadddr x1)))
    (cond (flg
	   (cond ((zp x)
		  z)
		 ((zp y)
		  z)
		 ((zp z)
		  1)
		 (t (+ -1 z))))
	  (t (if (zp n)
		 z
	         z)))))

(defun g-temp-clk (x st clk)
  (declare (xargs :measure (nfix clk)))
  (cond ((zp clk) nil)
        ((equal st nil) st)
        ((test1-g-temp x st) (finish-g-temp x st))
        ((test2-g-temp x st) (g-temp-clk (dst1-g-temp x st)
					 (stp-g-temp x st)
					 (1- clk)))
        (t (let ((st2 (g-temp-clk (dst1-g-temp x st)
				  (stp-g-temp x st)
				  (1- clk))))
             (if (equal st2 nil)
                 nil
                 (g-temp-clk (dst2-g-temp x st st2) st2 (1- clk)))))))

(defun-sk exists-enough-g-temp (x st)
  (exists clk 
          (and (natp clk)
               (not (equal (g-temp-clk x st clk) nil)))))

(defun g-temp (x st)
  (if (exists-enough-g-temp x st)
      (g-temp-clk x st (exists-enough-g-temp-witness x st))
    nil))

(defun
  g (flg n x y z)
  (g-temp (list flg n x y) z))

(defthm
  g-satisfies-specification
  (equal (g flg n x y z)
	 (cond ((null z)
		nil)
	       (flg
		(cond ((zp x)
		       (+ y z))
		      ((zp y)
		       (g t 0 (+ -1 x) 1 z))
		      ((zp z)
		       (g t 0 x (+ -1 y) 1))
		      (t (g nil 3 x y (+ -1 z)))))
	       (t (if (zp n)
		      z
		      (let* ((lst (i-g-lst nil n x y z))
			     (flga (first lst))
			     (na (second lst))
			     (xa (third lst))
			     (ya (fourth lst)))
			(g nil (+ -1 n) x y (g flga
					       na
					       xa
					       ya
					       z)))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  |definition of run|
		  (run g-temp)
		  (run-clk g-temp-clk)
		  (exists-enough exists-enough-g-temp)
		  (exists-enough-witness exists-enough-g-temp-witness)
		  (BTM (lambda () nil))
		  (test1 test1-g-temp)
		  (test2 test2-g-temp)
		  (finish finish-g-temp)
		  (dst1 dst1-g-temp)
		  (dst2 dst2-g-temp)
		  (stp stp-g-temp))
		 (x (list flg n x y))
		 (st z)))))

;; Above result uses an axiomatized (encapsuated) version of i-g-lst.
;; Redo the result with a special version of i-g-lst needed for the
;; definition of A.  Much of the work done above can be reused.

(defun
  i-gA-lst (flg n x y z)
  (declare (ignore z))
  (if flg
      (list flg n x y)
      (cond ((equal n 3)
             (list t 0 x y))
            ((equal n 2)
             (list t 0 x (+ -1 y)))
            ((equal n 1)
             (list t 0 (+ -1 x) y))
            (t (list flg n x y)))))

(defun
  dst1-gA-temp (x1 z)   ;; Modify non-recursive parameter(x1) in tail or inner call
  (let ((flg (car x1))
	(n (cadr x1))
	(x (caddr x1))
	(y (cadddr x1)))
    (cond (flg
	   (cond ((zp x)
		  x1)
		 ((zp y)
		  (list t 0 (+ -1 x) 1))
		 ((zp z)
		  (list t 0 x (+ -1 y)))
		 (t (list nil 3 x y))))
	  (t (if (zp n)
		 x1
	         (i-gA-lst flg n x y z))))))

(defun gA-temp-clk (x st clk)
  (declare (xargs :measure (nfix clk)))
  (cond ((zp clk) nil)
        ((equal st nil) st)
        ((test1-g-temp x st) (finish-g-temp x st))
        ((test2-g-temp x st) (gA-temp-clk (dst1-gA-temp x st)
					  (stp-g-temp x st)
					  (1- clk)))
        (t (let ((st2 (gA-temp-clk (dst1-gA-temp x st)
				   (stp-g-temp x st)
				   (1- clk))))
             (if (equal st2 nil)
                 nil
                 (gA-temp-clk (dst2-g-temp x st st2) st2 (1- clk)))))))

(defun-sk exists-enough-gA-temp (x st)
  (exists clk 
          (and (natp clk)
               (not (equal (gA-temp-clk x st clk) nil)))))

(defun gA-temp (x st)
  (if (exists-enough-gA-temp x st)
      (gA-temp-clk x st (exists-enough-gA-temp-witness x st))
    nil))

(defun
  gA (flg n x y z)
  (gA-temp (list flg n x y) z))

(defthm
  gA-satisfies-specification
  (equal (gA flg n x y z)
	 (cond ((null z)
		nil)
	       (flg
		(cond ((zp x)
		       (+ y z))
		      ((zp y)
		       (gA t 0 (+ -1 x) 1 z))
		      ((zp z)
		       (gA t 0 x (+ -1 y) 1))
		      (t (gA nil 3 x y (+ -1 z)))))
	       (t (if (zp n)
		      z
		      (let* ((lst (i-gA-lst nil n x y z))
			     (flga (first lst))
			     (na (second lst))
			     (xa (third lst))
			     (ya (fourth lst)))
			(gA nil (+ -1 n) x y (gA flga
						 na
						 xa
						 ya
						 z)))))))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:functional-instance
		  |definition of run|
		  (run gA-temp)
		  (run-clk gA-temp-clk)
		  (exists-enough exists-enough-gA-temp)
		  (exists-enough-witness exists-enough-gA-temp-witness)
		  (BTM (lambda () nil))
		  (test1 test1-g-temp)
		  (test2 test2-g-temp)
		  (finish finish-g-temp)
		  (dst1 dst1-gA-temp)
		  (dst2 dst2-g-temp)
		  (stp stp-g-temp))
		 (x (list flg n x y))
		 (st z)))
	  ("Subgoal 4"
	   :in-theory (disable (:definition test1-g-temp)))))

(defun
  A (x y z)
  (gA t 0 x y z))

(defthm
  A-satisfies-specification
  (equal (A x y z)
	 (if (null z)
	     nil
	   (cond ((zp x)
		  (+ y z))
		 ((zp y)
		  (A (+ -1 x) 1 z))
		 ((zp z)
		  (A x (+ -1 y) 1))
		 (t (A (+ -1 x) y (A x (+ -1 y)(A x y (+ -1 z))))))))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable (:definition gA))
	   :use ((:instance
		  gA-satisfies-specification
		  (flg t)
		  (n 0)
		  (x (+ -1 x))
		  (z nil)) 
		 (:instance
		  gA-satisfies-specification
		  (flg t)
		  (n 0)
		  (y (+ -1 y))
		  (z nil)) 
		 (:instance
		  gA-satisfies-specification
		  (flg t)
		  (n 0)) 	      
		 (:instance
		  gA-satisfies-specification
		  (flg nil)
		  (n 3)
		  (z (+ -1 z))) 
		 (:instance
		  gA-satisfies-specification
		  (flg nil)
		  (n 2)
		  (z (gA t 0 x y (+ -1 z))))
		 (:instance
		  gA-satisfies-specification
		  (flg nil)
		  (n 1)
		  (z (gA t 0 x (+ -1 y)(gA t 0 x y (+ -1 z)))))
		 (:instance
		  gA-satisfies-specification
		  (flg nil)
		  (n 0)
		  (z (gA t 0 (+ -1 x) y
			 (gA t 0 x (+ -1 y)
			     (gA t 0 x y (+ -1 z))))))))))


