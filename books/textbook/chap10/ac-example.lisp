; Section 10.2 Associative and Commutative Functions

(in-package "ACL2")

(encapsulate
 ((ac-fun (x y) t))
 (local (defun ac-fun (x y) (declare (ignore x y))
          nil))

 (defthm associativity-of-ac-fun
   (equal (ac-fun (ac-fun x y) z)
          (ac-fun x (ac-fun y z))))

 (defthm commutativity-of-ac-fun
   (equal (ac-fun x y)
          (ac-fun y x))))

(defthm commutativity-2-of-ac-fun
  (equal (ac-fun y (ac-fun x z))
         (ac-fun x (ac-fun y z)))
  :hints (("Goal"
           :in-theory (disable associativity-of-ac-fun)
           :use ((:instance associativity-of-ac-fun)
                 (:instance associativity-of-ac-fun
                            (x y) (y x))))))

(defthm commutativity-2-of-*
  (equal (* y (* x z))
         (* x (* y z)))
  :hints (("Goal"
           :by (:functional-instance
                commutativity-2-of-ac-fun
                (ac-fun binary-*)))))

(defthm commutativity-2-of-*
  (equal (* y (* x z))
         (* x (* y z)))
  :hints (("Goal"
           :by (:functional-instance
                commutativity-2-of-ac-fun
                (ac-fun (lambda (x y) (* x y)))))))


(defun make-name (prefix name)
; Returns the symbol prefix-name
  (declare (xargs :guard (and (symbolp prefix) (symbolp name))))
  (intern-in-package-of-symbol
   (concatenate 'string
                (symbol-name prefix)
                "-"
                (symbol-name name))
   prefix))

(defmacro commutativity-2 (op)
  `(defthm ,(make-name 'commutativity-2-of op)
     (equal (,op y (,op x z))
            (,op x (,op y z)))
     :hints (("Goal"
              :by (:functional-instance
                   commutativity-2-of-ac-fun
                   (ac-fun (lambda (x y) (,op x y))))))))

(commutativity-2 *)
