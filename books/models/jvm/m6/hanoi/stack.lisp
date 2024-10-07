(in-package "HANOI")
(acl2::set-verify-guards-eagerness 2)

(defund new-stack ()
  nil)

(defund stackp (stk)
  (true-listp stk))

(defund has-morep (stk)
  (declare (xargs :guard (stackp stk)))
  (consp stk))


(defund push (v stk) 
  (declare (xargs :guard (stackp stk)))
  (cons v stk))

(local (in-theory (enable stackp has-morep)))

(defund pop (stk) 
  (declare (xargs :guard (and (stackp stk)
                              (has-morep stk))))
  (cdr stk))


(defund top (stk)
  (declare (xargs :guard (and (stackp stk)
                              (has-morep stk))))
  (car stk))

;----------------------------------------------------------------------

(defthm push-stackp
  (implies (stackp stk)
           (stackp (push v stk)))
  :hints (("Goal" :in-theory (enable stackp push))))


(defthm pop-stackp
  (implies (and (stackp stk)
                (has-morep stk))
           (stackp (pop stk)))
  :hints (("Goal" :in-theory (enable stackp pop))))

(defthm new-stack-stackp
  (stackp (new-stack))
  :hints (("Goal" :in-theory (enable stackp new-stack))))


(defthm new-stack-empty
  (not (has-morep (new-stack)))
  :hints (("Goal" :in-theory (enable stackp has-morep new-stack))))