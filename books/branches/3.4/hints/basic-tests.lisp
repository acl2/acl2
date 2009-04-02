(in-package "ACL2")

(include-book "make-event/eval" :dir :system)

(defstub property (x) t)

(defstub constrp (x) t)

(encapsulate ((fff (x) t))
             (local (defun fff (x) x))
             (skip-proofs (defthm constrp-fff (constrp (fff x)))))

(skip-proofs (defthm property-fff (property (fff x))))

(encapsulate ((ggg (x) t))
             (local (defun ggg (x) x))
             (skip-proofs (defthm constrp-ggg (constrp (ggg x))
                            :rule-classes nil)))

(defstub ppp (x) t)

(not-thm?
 (property (ggg aaa))

; This proof will fail but you will see 5 cases: 4 from the
; :cases and a constraint.

 :hints
 (("Goal" :use (:instance (:functional-instance property-fff (fff ggg))
                          (x bbb))
   :cases ((ppp 1) (ppp 2) (ppp 3))))
 :otf-flg t)

(thm?
 (property (ggg aaa))

; This proof will succeed.

 :hints
 (("Goal" :use ((:instance (:functional-instance property-fff (fff ggg))
                           (x aaa))
                (:instance constrp-ggg (x x)))
   :cases ((ppp 1) (ppp 2) (ppp 3)))
  ("Goal'" :use ((:instance constrp-ggg (x x))))))


; These examples test :or

(defstub property (x) t)

(defaxiom bar
  (implies (property (fff x)) (property x))
  :rule-classes nil)

(defaxiom mum
  (implies (property (ggg x)) (property x))
  :rule-classes nil)

(defaxiom aaa (property (fff x)))
(defaxiom bbb (property (ggg x)))
(in-theory (disable aaa bbb))

; This is just to see the the io.  The proof will fail.

(not-thm?
 (property ccc)

;;;   ------------ this will fail ---------------

 :hints
 (("Goal"
   :OR
   ((:use (:instance bar (x disj-case-1)) :do-not '(generalize))
    (:use (:instance bar (x disj-case-2)) :do-not '(fertilize)))))
 :otf-flg t)

(not-thm?
 (property ccc)

;;;   ------------ this will fail ---------------


 :hints
 (("Goal"
   :OR
   ((:use (:instance bar (x disj-case-1)) :do-not '(generalize))
    (:use (:instance bar (x disj-case-2)) :do-not '(fertilize)))))
 :otf-flg nil)


(thm?
 (property ccc)

;;; ------------ this will succeed on the first branch ---------

 :hints
 (("Goal"
   :OR
   ((:in-theory (enable aaa) :use (:instance bar (x ccc)))
    (:in-theory (enable bbb) :use (:instance mum (x ddd)))))))

(thm?
 (property ccc)

;;; ------------ this will succeed on the second branch ---------

 :hints
 (("Goal"
   :OR
   ((:in-theory (enable aaa) :use (:instance bar (x ddd)))
    (:in-theory (enable bbb) :use (:instance mum (x ccc)))))))

(not-thm?
 (property ccc)

;;; ------------ this will fail ---------

 :hints
 (("Goal"
   :OR
   ((:in-theory (enable aaa) :use (:instance bar (x ddd)))
    (:in-theory (enable bbb) :use (:instance mum (x ddd)))))))

(thm?
 (property ccc)

;;; ------------ this will succeed ---------

 :hints
 (("Goal"
   :OR
   ((                      :use (:instance bar (x ccc)))
    (:in-theory (enable bbb) :use (:instance mum (x ddd)))))))

(not-thm?
 (property ccc)

;;; ------------ this will fail ---------

 :hints
 (("Goal"
   :OR
   ((:induct (append ccc x))
    (:in-theory (enable bbb) :use (:instance mum (x ddd)))))))

; These examples test custom keyword hints:

(add-custom-keyword-hint :syn-use
                         (pprogn
                          (fms "~%Expanding :syn-use generator~%"
                               nil *standard-co* state nil)
                          (value
                           (splice-keyword-alist
                            :syn-use
                            (list :use val)
                            keyword-alist))))

(not-thm?
 (equal x y)

; This hint will expand at pre-process time.  You will be able to
; tell because it will print a message every time it is run.
; You will see one expansion message.  The proof will fail.

 :hints (("Goal" :in-theory (disable car-cons)
          :syn-use car-cons
          :do-not '(generalize))
         ("Goal'" :in-theory (enable car-cons))))

(not-thm?
 (equal x y)

; This will cause an error because of an ill-formed common hint mixed
; with syn-use.

 :hints (("Goal" :in-theory (disable car-cons)
          :syn-use car-cons
          :do-not '(generalized)) ; error!
         ("Goal'" :in-theory (enable car-cons))))

(remove-custom-keyword-hint :syn-use) ; Added by Matt K.

(add-custom-keyword-hint :syn-use
                         (pprogn
                          (fms "~%Expanding :syn-use generator~%"
                               nil *standard-co* state nil)
                          (value
                           (splice-keyword-alist
                            :syn-use
                            (list :use val)
                            keyword-alist)))
                         :checker
                         (pprogn
                          (fms "~%Expanding :syn-use checker~%"
                               nil *standard-co* state nil)
                          (cond ((eq val 'cdr-cons)
                                 (er soft ctx
                                     "Syn-use doesn't allow you to use ~
                                      ~x0!"
                                     val))
                                (t (value t)))))

(not-thm?
 (equal x y)

; This hint will expand at pre-process time.  You will see the checker
; and then the generator.  The proof will fail.

 :hints (("Goal" :in-theory (disable car-cons)
          :syn-use car-cons
          :do-not '(generalize))
         ("Goal'" :in-theory (enable car-cons))))

(not-thm?
 (equal x y)

; This will cause an error because of the syn-use checker will fail.

 :hints (("Goal" :in-theory (disable car-cons)
          :syn-use cdr-cons
          :do-not '(generalized)) ; error!
         ("Goal'" :in-theory (enable car-cons))))

(add-custom-keyword-hint :eror
                         (value
                          (splice-keyword-alist
                           :eror
                           `(:ERROR ,(msg "The value ~x0 is illegal!" val))
                           keyword-alist)))

(not-thm?
 (equal (append (append a b) c)
        (append a (append b c)))

; This will throw an error on translation.

 :hints (("Subgoal *1/1'" :eror (a b c))))
              
(remove-custom-keyword-hint :eror) ; added by Matt K.

(add-custom-keyword-hint :eror
                         (value
                          (if (equal clause clause)
                              (splice-keyword-alist
                               :eror
                               `(:ERROR ,(msg "The value ~x0 is illegal!" val))
                               keyword-alist)
                            nil)))

(not-thm?
 (equal (append (append a b) c)
        (append a (append b c)))

; This will throw an error when Subgoal 1.1' arises

 :hints (("Subgoal *1/1'" :eror (a b c))))

(remove-custom-keyword-hint :syn-use) ; added by Matt K.

(add-custom-keyword-hint :syn-use
                         (pprogn
                          (fms "~%Expanding :syn-use generator~%"
                               nil *standard-co* state nil)
                          (value
                           (if (equal clause clause)
                               (splice-keyword-alist
                                :syn-use
                                (list :use val)
                                keyword-alist)
                             nil)))
                         :checker
                         (pprogn
                          (fms "~%Expanding :syn-use checker~%"
                               nil *standard-co* state nil)
                          (cond ((eq val 'cdr-cons)
                                 (er soft ctx
                                     "Syn-use doesn't allow you to use ~
                                      ~x0!"
                                     val))
                                (t (value t)))))

(thm?
 (equal (append (append a b) c)
        (append a (append b c)))

; You will see the checker expanded TWICE in pre-processing.  The
; first expansion is when we are trying to eagerly eliminate the
; :syn-use hint.  That fails.  So then we just run the all the
; checkers and we see it again.  Then the checker and the generator
; are run again in Subgoal *1/1'.

 :hints (("Subgoal *1/1'" :in-theory (disable car-cons)
          :syn-use car-cons
          :do-not '(generalize))))

(add-custom-keyword-hint :count-down
                         (value
                          (if (zp val)
                              (splice-keyword-alist
                               :count-down
                               '(:NO-OP t)
                               keyword-alist)
                            (splice-keyword-alist
                             :count-down
                             `(:count-down ,(- val 1))
                             keyword-alist))))

(thm?
 (equal (append (append a b) c)
        (append a (append b c)))
 :hints (("Subgoal *1/1'" :count-down 7)))

(thm?
 (equal (append (append a b) c)
        (append a (append b c)))

; Proof succeeds after a no-op hint is added

 :hints (("Subgoal *1/1'" :count-down 2)))

(remove-custom-keyword-hint :count-down)

(not-thm?
 (equal (append (append a b) c)
        (append a (append b c)))

; Error: illegal keyword

 :hints (("Subgoal *1/1'" :count-down 2)))

(add-custom-keyword-hint :count-down
                         (value
                         (if (and (equal clause clause)
                                  (zp val))
                             (splice-keyword-alist
                              :count-down
                              '(:NO-OP t)
                              keyword-alist)
                           (splice-keyword-alist
                            :count-down
                            `(:count-down ,(- val 1))
                            keyword-alist)))
                         :checker
                         (if (natp val)
                             (value t)
                           (er soft ctx
                               ":count-down wants a nat and ~x0 ain't one."
                               val)))


(not-thm?
 (equal (append (append a b) c)
        (append a (append b c)))

; Error at pre-process

 :hints (("Subgoal *1/1'" :count-down t)))

(thm?
 (equal (append (append a b) c)
        (append a (append b c)))
 :hints (("Subgoal *1/1'" :count-down 7)))

(thm?
 (equal (append (append a b) c)
        (append a (append b c)))
; Success

 :hints (("Subgoal *1/1'" :count-down 2)))

(add-custom-keyword-hint :recurse
                         (er-progn
                          (value (cw "--- Here goes ---"))
                          (defthm append-right-id
                            (implies (true-listp x)
                                     (equal (append x nil) x)))
                          (value (cw "--- Done ---"))
                          (value (if (equal clause clause)
                                     (splice-keyword-alist
                                      :recurse
                                      '(:NO-OP t)
                                      keyword-alist)
                                   nil))))

(thm?
 (equal (append (append a b) c)
        (append a (append b c)))

; Scary Success.  This was designed to test the ens tracking and we didn't find
; anything amiss.

; This was labeled as "scary" above because it seemed conceivable that we would
; be able to provoke a slow array warning.

 :hints (("Subgoal *1/2" :in-theory (disable cdr-cons
                                             CONS-CAR-CDR
                                             car-cdr-elim))
         ("Subgoal *1/2'" :no-op t
          :recurse t
          )
         ("Subgoal *1/2''" :in-theory (disable cdr-cons cons-car-cdr))
         ("Subgoal *1/2'4'" :in-theory (enable cdr-cons))))
