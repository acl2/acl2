; Banach-Tarski theorem
;
; A free group of reduced words of rank 2.
;
;
; Copyright (C) 2021 University of Wyoming
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Main Authors: Jagadish Bapanapally (jagadishb285@gmail.com)
;
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(include-book "std/typed-lists/character-listp" :dir :system)
(include-book "std/lists/top" :dir :system)

(defun wa()
  #\a
  )

(defun wa-inv()
  #\b
  )

(defun wb()
  #\c
  )

(defun wb-inv()
  #\d
  )

(defthmd abcd-chars
  (and (characterp (wa))
       (characterp (wa-inv))
       (characterp (wb))
       (characterp (wb-inv)))
  )

(defun weak-wordp (w)
  (cond ((atom w) (equal w nil))
	(t (and (or (equal (car w) (wa))
		    (equal (car w) (wa-inv))
		    (equal (car w) (wb))
		    (equal (car w) (wb-inv)))
		(weak-wordp (cdr w))))))

(defun wordp(w letter)
  (cond ((atom w) (equal w nil))
	((equal letter (wa)) (let ((firstw (car w)) (restw (cdr w)))
			       (and (or (equal firstw (wa))
					(equal firstw (wb))
					(equal firstw (wb-inv)))
				    (wordp restw firstw))))
	((equal letter (wa-inv)) (let ((firstw (car w)) (restw (cdr w)))
				   (and (or (equal firstw (wa-inv))
					    (equal firstw (wb))
					    (equal firstw (wb-inv)))
					(wordp restw firstw))))

	((equal letter (wb)) (let ((firstw (car w)) (restw (cdr w)))
			       (and (or (equal firstw (wa))
					(equal firstw (wa-inv))
					(equal firstw (wb)))
				    (wordp restw firstw))))
	((equal letter (wb-inv)) (let ((firstw (car w)) (restw (cdr w)))
				   (and (or (equal firstw (wa))
					    (equal firstw (wa-inv))
					    (equal firstw (wb-inv)))
					(wordp restw firstw))))))

(defun a-wordp(w)
  (and (equal (car w) (wa))
       (wordp (cdr w) (wa))))

(defun b-wordp(w)
  (and (equal (car w) (wb))
       (wordp (cdr w) (wb))))

(defun a-inv-wordp(w)
  (and (equal (car w) (wa-inv))
       (wordp (cdr w) (wa-inv))))

(defun b-inv-wordp(w)
  (and (equal (car w) (wb-inv))
       (wordp (cdr w) (wb-inv))))

(defthmd a-wordp-equivalent
  (implies (a-wordp a)
	   (and (not (a-inv-wordp a))
		(not (b-wordp a))
		(not (b-inv-wordp a))
		(not (equal a '())))))

(defthmd b-wordp-equivalent
  (implies (b-wordp b)
	   (and (not (a-inv-wordp b))
		(not (a-wordp b))
		(not (b-inv-wordp b))
		(not (equal b '())))))

(defthmd a-inv-wordp-equivalent
  (implies (a-inv-wordp a-inv)
	   (and (not (a-wordp a-inv))
		(not (b-wordp a-inv))
		(not (b-inv-wordp a-inv))
		(not (equal a-inv '())))))

(defthmd b-inv-wordp-equivalent
  (implies (b-inv-wordp b-inv)
	   (and (not (b-wordp b-inv))
		(not (a-wordp b-inv))
		(not (a-inv-wordp b-inv))
		(not (equal b-inv '())))))

(defun word-fix (w)
  (if (atom w)
      nil
    (let ((fixword (word-fix (cdr w))))
      (let ((w (cons (car w) fixword)))
	(cond ((equal fixword nil)
	       (list (car w)))
	      ((equal (car (cdr w)) (wa))
	       (if (equal (car w) (wa-inv))
		   (cdr (cdr w))
		 w))
	      ((equal (car (cdr w)) (wa-inv))
	       (if (equal (car w) (wa))
		   (cdr (cdr w))
		 w))
	      ((equal (car (cdr w)) (wb))
	       (if (equal (car w) (wb-inv))
		   (cdr (cdr w))
		 w))
	      ((equal (car (cdr w)) (wb-inv))
	       (if (equal (car w) (wb))
		   (cdr (cdr w))
		 w)))))))

(defun compose (x y)
  (word-fix (append x y)))

(defun reducedwordp (x)
  (or (a-wordp x)
      (a-inv-wordp x)
      (b-wordp x)
      (b-inv-wordp x)
      (equal x '())))

(defthmd weak-wordp-equivalent
  (implies (weak-wordp x)
	   (reducedwordp (word-fix x))))

(encapsulate
  ()

  (local
   (defthm lemma
     (implies (or (a-wordp x)
                  (a-inv-wordp x)
                  (b-wordp x)
                  (b-inv-wordp x)
                  (equal x '()))
              (weak-wordp x))))

  (defthmd a-wordp=>weak-wordp
    (implies (a-wordp x)
             (weak-wordp x)))

  (defthmd b-wordp=>weak-wordp
    (implies (b-wordp x)
             (weak-wordp x)))

  (defthmd b-inv-wordp=>weak-wordp
    (implies (b-inv-wordp x)
             (weak-wordp x)))

  (defthmd a-inv-wordp=>weak-wordp
    (implies (a-inv-wordp x)
             (weak-wordp x)))

  (defthmd reducedwordp=>weak-wordp
    (implies (reducedwordp x)
             (weak-wordp x))))

(encapsulate
  ()

  (local
   (defthm lemma
     (implies (or (a-wordp x)
                  (a-inv-wordp x)
                  (b-wordp x)
                  (b-inv-wordp x)
                  (equal x '()))
              (equal (word-fix x) x))))

  (defthmd word-fix=a-wordp
    (implies (a-wordp x)
             (equal (word-fix x) x)))

  (defthmd word-fix=a-inv-wordp
    (implies (a-inv-wordp x)
             (equal (word-fix x) x)))

  (defthmd word-fix=b-wordp
    (implies (b-wordp x)
             (equal (word-fix x) x)))

  (defthmd word-fix=b-inv-wordp
    (implies (b-inv-wordp x)
             (equal (word-fix x) x)))

  (defthmd word-fix=reducedwordp
    (implies (reducedwordp x)
             (equal (word-fix x) x)))

  (defthmd word-fix=reducedwordp-1
    (implies (and (weak-wordp x)
                  (equal (word-fix x) x))
             (reducedwordp x))
    :hints (("goal"
             :use (:instance weak-wordp-equivalent (x x))
             )))
  )


(defthmd weak-word-cdr
  (implies (weak-wordp x)
	   (weak-wordp (cdr x))))

(defthmd character-listp-word
  (implies (or (reducedwordp x)
	       (weak-wordp x))
	   (character-listp x)))

(defthmd reduced-cdr
  (implies (reducedwordp x)
	   (reducedwordp (cdr x)))
  )

(defthmd reducedwordp-car
  (implies (reducedwordp w)
           (or (equal (car w) #\a)
               (equal (car w) #\b)
               (equal (car w) #\c)
               (equal (car w) #\d)
               (equal w '()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;closure property;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd closure-weak-word
  (implies (and (weak-wordp x)
		(weak-wordp y))
	   (weak-wordp (append x y)))
  )

(defthmd closure-lemma
  (implies (and (reducedwordp x)
		(reducedwordp y))
	   (weak-wordp (append x y)))
  :hints (("goal"
	   :use ((:instance a-wordp=>weak-wordp (x x))
		 (:instance b-wordp=>weak-wordp (x x))
		 (:instance a-inv-wordp=>weak-wordp (x x))
		 (:instance b-inv-wordp=>weak-wordp (x x))
		 (:instance a-wordp=>weak-wordp (x y))
		 (:instance b-wordp=>weak-wordp (x y))
		 (:instance a-inv-wordp=>weak-wordp (x y))
		 (:instance b-inv-wordp=>weak-wordp (x y))
		 (:instance closure-weak-word)
		 )
	   ))
  )

(defthmd closure-prop
  (implies (and (reducedwordp x)
		(reducedwordp y))
	   (reducedwordp (compose x y))
	   )
  :hints (("goal"
	   :use ((:instance closure-lemma (x x) (y y))
		 (:instance weak-wordp-equivalent (x (append x y)))
		 )
	   ))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;associative property;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()

  (local
   (defthm weak-wordp-equivalent-assoc
     (implies (weak-wordp x)
              (reducedwordp (word-fix x))))
   )

  (local
   (defthm reducedwordp=>weak-wordp-assoc
     (implies (reducedwordp x)
              (weak-wordp x)))
   )

  (local
   (defthm word-fix=reducedwordp-assoc
     (implies (reducedwordp x)
              (equal (word-fix x) x))
     )
   )

  (local
   (defthm word-fix=reducedwordp-1-assoc
     (implies (and (weak-wordp x)
                   (equal (word-fix x) x))
              (reducedwordp x))
     :hints (("goal"
              :use (:instance weak-wordp-equivalent (x x))
              ))
     )
   )

  (local
   (defthm weak-word-cdr-assoc
     (implies (weak-wordp x)
              (weak-wordp (cdr x)))
     )
   )

  (local
   (defthm character-listp-word-assoc
     (implies (or (reducedwordp x)
                  (weak-wordp x))
              (character-listp x))
     )
   )

  (local
   (defthm reduced-cdr-assoc
     (implies (reducedwordp x)
              (reducedwordp (cdr x)))
     )
   )

  (local
   (defthm closure-weak-word-assoc
     (implies (and (weak-wordp x)
                   (weak-wordp y))
              (weak-wordp (append x y)))
     )
   )

  (local
   (defthm closure-lemma-assoc
     (implies (and (reducedwordp x)
                   (reducedwordp y))
              (weak-wordp (append x y)))
     :hints (("goal"
              :use ((:instance a-wordp=>weak-wordp (x x))
                    (:instance b-wordp=>weak-wordp (x x))
                    (:instance a-inv-wordp=>weak-wordp (x x))
                    (:instance b-inv-wordp=>weak-wordp (x x))
                    (:instance a-wordp=>weak-wordp (x y))
                    (:instance b-wordp=>weak-wordp (x y))
                    (:instance a-inv-wordp=>weak-wordp (x y))
                    (:instance b-inv-wordp=>weak-wordp (x y))
                    (:instance closure-weak-word)
                    )
              ))
     )
   )

  (local
   (defthm closure-prop-assoc
     (implies (and (reducedwordp x)
                   (reducedwordp y))
              (reducedwordp (compose x y))
              )
     :hints (("goal"
              :use ((:instance closure-lemma (x x) (y y))
                    (:instance weak-wordp-equivalent (x (append x y)))
                    )
              ))
     ))

  (local
   (defthm wordfix-wordfix
     (implies (weak-wordp x)
              (equal (word-fix (word-fix x)) (word-fix x)))
     ))

  (local
   (defthm append-nil-assoc
     (implies (character-listp x)
              (equal (append x nil) x))
     :rule-classes ((:rewrite
                     :backchain-limit-lst (3)
                     :match-free :all)))
   )

  (local
   (defthm append-lemma
     (implies (and (reducedwordp x)
                   (reducedwordp y)
                   (reducedwordp z))
              (equal (append x (append y z)) (append x y z))
              )
     :rule-classes nil
     )
   )

  (local
   (defthm weak-word-=
     (implies (weak-wordp x)
              (or (equal x '())
                  (and (equal (car x) (wa)) (weak-wordp (cdr x)))
                  (and (equal (car x) (wa-inv)) (weak-wordp (cdr x)))
                  (and (equal (car x) (wb)) (weak-wordp (cdr x)))
                  (and (equal (car x) (wb-inv)) (weak-wordp (cdr x)))
                  ))
     )
   )

  (local
   (defthm weak-wordp-rev
     (implies (weak-wordp x)
              (weak-wordp (rev x)))
     )
   )

  (local
   (defthm compose-assoc-lemma
     (implies (and (weak-wordp x)
                   (weak-wordp y))
              (equal (word-fix (append x (word-fix y))) (word-fix (append x y)))
              )
     :hints (("goal"
              :use ((:instance weak-wordp-equivalent-assoc (x x))
                    (:instance weak-wordp-equivalent-assoc (x y))
                    (:instance reducedwordp=>weak-wordp-assoc (x (word-fix x)))
                    (:instance reducedwordp=>weak-wordp-assoc (x (word-fix y)))
                    (:instance word-fix (w (append x (word-fix y))))
                    (:instance word-fix (w (word-fix (append x y))))
                    )
              :in-theory (enable word-fix append)
              ))
     )
   )

  (local
   (defthm compose-assoc-lemma1
     (implies (and (weak-wordp x)
                   (weak-wordp y)
                   (weak-wordp z))
              (equal (word-fix (append x (word-fix (append y z)))) (word-fix (append x y z)))
              )
     :hints (("goal"
              :use ((:instance compose-assoc-lemma (x (append y z)))
                    (:instance closure-weak-word-assoc (x y) (y z))
                    )
              :in-theory (enable word-fix append)
              ))
     )
   )

  (defthmd compose-assoc-lemma-export
    (implies (and (weak-wordp x)
                  (weak-wordp y))
             (equal (word-fix (append x (word-fix y))) (word-fix (append x y)))
             )
    :hints (("goal"
             :use ((:instance compose-assoc-lemma (x x) (y y)))
             :in-theory (enable word-fix append)
             ))
    )

  (encapsulate
    ()

    (local
     (defthmd lemma1
       (implies (character-listp x)
                (equal (append (rev (cdr (rev x))) (last x))
                       x))
       :hints (("goal"
                :in-theory (enable rev)
                ))
       )
     )

    (local
     (defthmd lemma2
       (implies (and (listp x)
                     (listp y)
                     (listp z))
                (equal (append x y z)
                       (append (append x y) z))
                )
       )
     )

    (defthmd lemma3
      (implies (and (character-listp x)
                    x)
               (and (equal (list (car (last x))) (last x))
                    (equal (append (list (car x)) (cdr x)) x)
                    (listp (rev (cdr (rev x))))
                    (listp (list (car (last x))))
                    (listp (last x))
                    (character-listp (list (car x)))))
      :hints (("goal"
               :in-theory (enable last car character-listp rev append)
               ))
      )

    (local
     (defthmd lemma4
       (implies (and (weak-wordp x)
                     x)
                (weak-wordp (last x)))
       )
     )

    (local
     (defthmd word-fix-rev-lemma1
       (implies (and (weak-wordp x)
                     (reducedwordp (append x (list y)))
                     (characterp z)
                     (weak-wordp (list z)))
                (equal (word-fix (append x (list y) (list z)))
                       (append x (word-fix (append (list y) (list z))))))
       )
     )

    (local
     (defthmd word-fix-rev-lemma2
       (implies (and (reducedwordp x)
                     (characterp y)
                     (weak-wordp (list y)))
                (equal (word-fix (append x (list y)))
                       (append (rev (cdr (rev x))) (word-fix (append (last x) (list y))))))
       :hints (("goal"
                :cases ((not x)
                        x)
                :do-not-induct t
                )

               ("subgoal 1"
                :use (
                      (:instance character-listp-word-assoc (x x))
                      (:instance reducedwordp=>weak-wordp (x x))
                      (:instance weak-wordp-rev (x x))
                      (:instance weak-word-cdr (x (rev x)))
                      (:instance weak-wordp-rev (x (cdr (rev x))))
                      (:instance character-listp-word-assoc (x (rev (cdr (rev x)))))
                      (:instance lemma3 (x x))
                      (:instance word-fix-rev-lemma1
                                 (x (rev (cdr (rev x))))
                                 (y (car (last x)))
                                 (z y))
                      (:instance lemma1 (x x))
                      (:instance lemma2
                                 (x (rev (cdr (rev x))))
                                 (y (last x))
                                 (z (list y)))
                      )
                :do-not-induct t
                :in-theory nil
                )
               )
       )
     )

    (defthmd lemma11
      (implies (weak-wordp x)
               (if x (and (weak-wordp (list (car x)))
                          (weak-wordp (last x)))
                 (weak-wordp (last x)))
               )
      )

    (defthmd word-fix-rev-lemma3-12
      (implies (and (characterp x)
                    (weak-wordp (list x))
                    y
                    (reducedwordp y))
               (equal (word-fix (append (list x) y))
                      (append (word-fix (append (list x) (list (car y)))) (cdr y))))
      )

    (local
     (defthmd lemma8
       (implies (and (weak-wordp x)
                     (<= (len x) 1))
                (or (equal x nil)
                    (equal x '(#\a))
                    (equal x '(#\b))
                    (equal x '(#\c))
                    (equal x '(#\d))))
       )
     )

    (local
     (defthmd word-fix-rev-lemma3-1
       (implies (and (characterp x)
                     (weak-wordp (list x))
                     (reducedwordp y)
                     (characterp z)
                     (weak-wordp (list z)))
                (equal (word-fix (append (list x) y (list z)))
                       (word-fix (append (word-fix (append (list x) y)) (list z)))))
       :hints (("goal"
                :cases ((<= (len y) 1)
                        (> (len y) 1))
                :do-not-induct t
                )
               ("subgoal 2"
                :use ((:instance reducedwordp=>weak-wordp-assoc (x y))
                      (:instance lemma8 (x (list x)))
                      (:instance lemma8 (x y))
                      (:instance lemma8 (x (list z))))
                )
               ("subgoal 1"
                :use (
                      (:instance compose-assoc-lemma1
                                 (x (list x))
                                 (y y)
                                 (z (list z)))

                      (:instance word-fix-rev-lemma2 (x y) (y z))

                      (:instance lemma11 (x y))
                      (:instance reducedwordp=>weak-wordp-assoc (x y))
                      (:instance closure-weak-word-assoc (x y) (y (list z)))
                      (:instance weak-wordp-equivalent-assoc (x (append y (list z))))
                      (:instance word-fix-rev-lemma3-12
                                 (x x)
                                 (y (append (rev (cdr (rev y))) (word-fix (append (last y) (list z)))))
                                 )
                      (:instance word-fix-rev-lemma3-12 (x x) (y y))
                      (:instance closure-weak-word-assoc
                                 (x (list x))
                                 (y y))
                      (:instance weak-wordp-equivalent-assoc (x (word-fix (append (list x) y))))
                      (:instance word-fix-rev-lemma2
                                 (x (append (word-fix (append (list x) (list (car y)))) (cdr y)))
                                 (y z))
                      )
                ))
       )
     )

    (local
     (defthmd lemma-13
       (implies (and (character-listp x)
                     x
                     (characterp y))
                (and (equal (append x (list y))
                            (append (list (car x)) (cdr x) (list y)))
                     (characterp (car x))
                     (consp (append x (list y)))))
       :hints (("goal"
                :in-theory (enable append)
                ))
       )
     )

    (local
     (defthmd word-fix-rev-lemma3-induct
       (implies (and (not (atom x))
                     (implies (and (weak-wordp (cdr x))
                                   (characterp y)
                                   (weak-wordp (list y)))
                              (equal (word-fix (append (cdr x) (list y)))
                                     (word-fix (append (word-fix (cdr x)) (list y))))))
                (implies (and (weak-wordp x)
                              (characterp y)
                              (weak-wordp (list y)))
                         (equal (word-fix (append x (list y)))
                                (word-fix (append (word-fix x) (list y)))))
                )
       :hints (("goal"
                :cases ((not x)
                        x)
                )
               ("subgoal 1"
                :use (
                      (:instance lemma-13 (x x))
                      (:instance character-listp-word-assoc (x x))
                      (:instance lemma11 (x x))
                      (:instance weak-word-cdr (x x))
                      (:instance compose-assoc-lemma1
                                 (x (list (car x)))
                                 (y (cdr x))
                                 (z (list y)))
                      (:instance weak-wordp-equivalent-assoc (x (cdr x)))
                      (:instance reducedwordp=>weak-wordp-assoc (x (word-fix (cdr x))))
                      (:instance closure-weak-word-assoc (x (word-fix (cdr x))) (y (list y)))
                      (:instance compose-assoc-lemma
                                 (x (list (car x)))
                                 (y (append (word-fix (cdr x)) (list y))))

                      (:instance weak-wordp-equivalent-assoc (x (cdr x)))
                      (:instance word-fix-rev-lemma3-1
                                 (x (car x))
                                 (y (word-fix (cdr x)))
                                 (z y))
                      (:instance compose-assoc-lemma
                                 (x (list (car x)))
                                 (y (cdr x)))
                      (:instance lemma3 (x x))
                      )
                :in-theory nil
                :do-not-induct t
                ))
       )
     )

    (local
     (defthmd word-fix-rev-lemma3
       (implies (and (weak-wordp x)
                     (characterp y)
                     (weak-wordp (list y)))
                (equal (word-fix (append x (list y)))
                       (word-fix (append (word-fix x) (list y)))))

       :hints (("goal"
                :cases ((not x)
                        x)
                )
               ("subgoal *1/11"
                :use ((:instance lemma-13 (x x))
                      (:instance character-listp-word-assoc (x x))
                      (:instance compose-assoc-lemma1
                                 (x (list (car x)))
                                 (y (cdr x))
                                 (z (list y)))
                      (:instance compose-assoc-lemma
                                 (x (list (car x)))
                                 (y (append (word-fix (cdr x)) (list y))))
                      (:instance weak-word-cdr (x x))
                      (:instance weak-wordp-equivalent-assoc (x (cdr x)))
                      (:instance word-fix-rev-lemma3-1
                                 (x (car x))
                                 (y (word-fix (cdr x)))
                                 (z y))
                      )
                )
               ("subgoal *1/9"
                :use ((:instance word-fix-rev-lemma3-induct (x x)))
                )
               ("subgoal *1/8"
                :use ((:instance word-fix-rev-lemma3-induct (x x)))
                )
               ("subgoal *1/7"
                :use ((:instance word-fix-rev-lemma3-induct (x x)))
                )
               ("subgoal *1/6"
                :use ((:instance word-fix-rev-lemma3-induct (x x)))
                )
               ("subgoal *1/5"
                :use ((:instance word-fix-rev-lemma3-induct (x x)))
                )
               ("subgoal *1/4"
                :use ((:instance word-fix-rev-lemma3-induct (x x)))
                )
               ("subgoal *1/3"
                :use ((:instance word-fix-rev-lemma3-induct (x x)))
                )
               ("subgoal *1/2"
                :use ((:instance word-fix-rev-lemma3-induct (x x)))
                )
               )
       )
     )

    (local
     (defthmd word-fix-rev-lemma4
       (implies (weak-wordp x)
                (equal (word-fix x)
                       (append (rev (cdr (rev (word-fix (rev (cdr (rev x)))))))
                               (word-fix (append (last (word-fix (rev (cdr (rev x)))))
                                                 (last x))))))
       :hints (("goal"
                :cases ((not x)
                        x)
                :do-not-induct t
                )
               ("subgoal 1"
                :use ((:instance lemma1 (x x))
                      (:instance character-listp-word-assoc (x x))
                      (:instance weak-wordp-rev (x x))
                      (:instance weak-word-cdr (x (rev x)))
                      (:instance weak-wordp-rev (x (cdr (rev x))))
                      (:instance lemma3 (x x))
                      (:instance word-fix-rev-lemma3 (x (rev (cdr (rev x)))) (y (car (last x))))
                      (:instance weak-wordp-equivalent-assoc (x (rev (cdr (rev x)))))
                      (:instance word-fix-rev-lemma2
                                 (x (word-fix (rev (cdr (rev x)))))
                                 (y (car (last x))))
                      (:instance word-fix (w (append (rev (cdr (rev x))) (last x))))
                      (:instance lemma4 (x x))
                      )
                )
               )
       )
     )

    (local
     (defthmd lemma5
       (implies (character-listp x)
                (equal (rev (rev x)) x))
       )
     )

    (local
     (defthmd lemma6
       (implies (and (character-listp x)
                     x)
                (equal (last (rev x)) (list (car x))))
       :hints (("goal"
                :in-theory (enable rev)
                ))
       )
     )

    (local
     (defthmd lemma7
       (implies (and (character-listp x)
                     (character-listp y))
                (equal (rev (append x y))
                       (append (rev y) (rev x))))
       )
     )

    (local
     (defthmd lemma9
       (implies (and
                 (weak-wordp x)
                 (weak-wordp y)
                 (<= (len x) 1)
                 (<= (len y) 1))
                (equal (rev (word-fix (append x y)))
                       (word-fix (append y x))))
       :hints (("goal"

                :use ((:instance lemma8 (x x))
                      (:instance lemma8 (x y)))

                :cases (
                        (and (atom x) (atom y))
                        (and (equal x '(#\a)) (equal y '(#\a)))
                        (and (equal x '(#\a)) (equal y '(#\b)))
                        (and (equal x '(#\a)) (equal y '(#\c)))
                        (and (equal x '(#\a)) (equal y '(#\d)))
                        (and (equal x '(#\b)) (equal y '(#\a)))
                        (and (equal x '(#\b)) (equal y '(#\b)))
                        (and (equal x '(#\b)) (equal y '(#\c)))
                        (and (equal x '(#\b)) (equal y '(#\d)))
                        (and (equal x '(#\c)) (equal y '(#\a)))
                        (and (equal x '(#\c)) (equal y '(#\b)))
                        (and (equal x '(#\c)) (equal y '(#\c)))
                        (and (equal x '(#\c)) (equal y '(#\d)))
                        (and (equal x '(#\d)) (equal y '(#\a)))
                        (and (equal x '(#\d)) (equal y '(#\b)))
                        (and (equal x '(#\d)) (equal y '(#\c)))
                        (and (equal x '(#\d)) (equal y '(#\d)))
                        (and (atom x) (equal y '(#\a)))
                        (and (atom x) (equal y '(#\b)))
                        (and (atom x) (equal y '(#\c)))
                        (and (atom x) (equal y '(#\d)))
                        (and (equal x '(#\d)) (atom y))
                        (and (equal x '(#\d)) (atom y))
                        (and (equal x '(#\d)) (atom y))
                        (and (equal x '(#\d)) (atom y))
                        )
                :in-theory (enable append rev)
                )
               )
       )
     )

    (local
     (defthmd lemma10
       (implies (and (characterp x)
                     (weak-wordp (list x))
                     (reducedwordp y)
                     (not (atom y)))
                (equal (word-fix (append (list x) y))
                       (append (word-fix (append (list x) (list (car y)))) (cdr y)))
                )
       :hints (("goal"
                :use ((:instance reduced-cdr-assoc (x y))
                      (:instance word-fix=reducedwordp-assoc (x (cdr x)))
                      )
                ))
       )
     )

    (local
     (defthm lemma12
       (implies (and (weak-wordp x)
                     (word-fix (cdr x))
                     x)
                (equal (word-fix x)
                       (append (word-fix (append (list (car x)) (list (car (word-fix (cdr x))))))
                               (cdr (word-fix (cdr x))))))
       :hints (("goal"
                :use ((:instance compose-assoc-lemma (x (list (car x))) (y (cdr x)))
                      (:instance lemma10 (x (car x)) (y (word-fix (cdr x))))
                      (:instance weak-word-cdr (x x))
                      (:instance lemma11 (x x))
                      (:instance weak-wordp-equivalent-assoc (x (word-fix (cdr x)))))
                :do-not-induct t
                ))
       )
     )

    (local
     (defthmd word-fix-lemma2
       (implies (and (weak-wordp x)
                     (not (atom x))
                     (equal (word-fix (rev (cdr x)))
                            (rev (word-fix (cdr x))))
                     )
                (equal (word-fix (rev x))
                       (append (rev (cdr (word-fix (cdr x))))
                               (word-fix (append (last (rev (word-fix (cdr x))))
                                                 (list (car x)))))))
       :hints (("goal"
                :cases ((not x)
                        x))
               ("subgoal 1"
                :use ((:instance weak-wordp-rev (x x))
                      (:instance word-fix-rev-lemma4 (x (rev x)))
                      (:instance lemma5 (x x))
                      (:instance weak-word-cdr (x x))
                      (:instance weak-wordp-equivalent-assoc (x x))
                      (:instance weak-wordp-equivalent-assoc (x (cdr x)))
                      (:instance character-listp-word-assoc (x x))
                      (:instance character-listp-word-assoc (x (word-fix (cdr x))))
                      (:instance lemma5 (x (word-fix (cdr x))))
                      (:instance lemma6 (x x))
                      )
                :in-theory nil
                :do-not-induct t
                ))
       )
     )

    (local
     (defthmd word-fix-lemma1
       (implies (and (weak-wordp x)
                     (not (atom x))
                     (equal (word-fix (rev (cdr x)))
                            (rev (word-fix (cdr x))))
                     )
                (equal (word-fix (rev x)) (rev (word-fix x))))
       :hints (("goal"
                :cases ((not x)
                        x)
                :do-not-induct t
                )
               ("subgoal 1"
                :cases ((not (word-fix (cdr x)))
                        (word-fix (cdr x)))
                :use (
                      (:instance lemma5 (x (word-fix (append (last (rev (word-fix (cdr x))))
                                                             (list (car x))))))
                      (:instance word-fix-lemma2 (x x))
                      (:instance lemma7
                                 (x (rev (word-fix (append (last (rev (word-fix (cdr x))))
                                                           (list (car x))))))
                                 (y (cdr (fix (cdr x)))))
                      (:instance lemma9
                                 (x (last (rev (word-fix (cdr x)))))
                                 (y (list (car x))))
                      (:instance lemma12 (x x))
                      (:instance lemma11 (x x))
                      (:instance weak-word-cdr (x x))
                      (:instance weak-wordp-equivalent-assoc (x (cdr x)))
                      (:instance reducedwordp=>weak-wordp-assoc (x (cdr x)))
                      (:instance weak-wordp-rev (x (word-fix (cdr x))))
                      (:instance character-listp-word-assoc (x x))
                      (:instance lemma11 (x (rev (word-fix (cdr x)))))
                      (:instance closure-weak-word-assoc
                                 (x (last (rev (word-fix (cdr x)))))
                                 (y (list (car x))))
                      (:instance weak-wordp-equivalent-assoc
                                 (x (append (last (rev (word-fix (cdr x))))
                                            (list (car x)))))
                      (:instance character-listp-word-assoc
                                 (x (word-fix (append (last (rev (word-fix (cdr x))))
                                                      (list (car x))))))
                      )
                :in-theory (enable append)
                )
               )
       )
     )

    (defthmd word-fix-rev-lemma
      (implies (weak-wordp x)
               (equal (word-fix (rev x)) (rev (word-fix x))))

      :hints (
              ("subgoal *1/21"
               :use (:instance word-fix-lemma1 (x x))
               )
              ("subgoal *1/20"
               :use (:instance word-fix-lemma1 (x x))
               )
              ("subgoal *1/19"
               :use (:instance word-fix-lemma1 (x x))
               )
              ("subgoal *1/18"
               :use (:instance word-fix-lemma1 (x x))
               )
              ("subgoal *1/17"
               :use (:instance word-fix-lemma1 (x x))
               )
              ("subgoal *1/16"
               :use (:instance word-fix-lemma1 (x x))
               )
              ("subgoal *1/15"
               :use (:instance word-fix-lemma1 (x x))
               )
              ("subgoal *1/14"
               :use (:instance word-fix-lemma1 (x x))
               )
              ("subgoal *1/13"
               :use (:instance word-fix-lemma1 (x x))
               )
              ("subgoal *1/12"
               :use (:instance word-fix-lemma1 (x x))
               )
              ("subgoal *1/11"
               :use (:instance word-fix-lemma1 (x x))
               )

              ("subgoal *1/10"
               :use (:instance word-fix-lemma1 (x x))
               )

              ("subgoal *1/9"
               :use (:instance word-fix-lemma1 (x x))
               )

              ("subgoal *1/8"
               :use (:instance word-fix-lemma1 (x x))
               )

              ("subgoal *1/7"
               :use (:instance word-fix-lemma1 (x x))
               )

              ("subgoal *1/6"
               :use (:instance word-fix-lemma1 (x x))
               )

              ("subgoal *1/5"
               :use (:instance word-fix-lemma1 (x x))
               )

              ("subgoal *1/4"
               :use (:instance word-fix-lemma1 (x x))
               )

              ("subgoal *1/3"
               :use (:instance word-fix-lemma1 (x x))
               )

              ("subgoal *1/2"
               :use (:instance word-fix-lemma1 (x x))
               )
              )
      )
    )

  (defthmd assoc-prop
    (implies (and (reducedwordp x)
                  (reducedwordp y)
                  (reducedwordp z))
             (equal (compose (compose x y) z) (compose x (compose y z))))

    :hints (("goal"
             :use ((:instance rev-of-rev (x (word-fix (append (word-fix (append x y)) z))))
                   (:instance word-fix-rev-lemma (x (append (word-fix (append x y)) z)))
                   (:instance word-fix-rev-lemma (x (append x y)))
                   (:instance compose-assoc-lemma1 (x (rev z)) (y (rev y)) (z (rev x)))
                   (:instance word-fix-rev-lemma (x (append (rev z) (rev y) (rev x)))))
             :do-not-induct t
             ))
    )
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;inverse exists;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd basecase
  (implies (atom x)
	   (implies (and (weak-wordp x)
			 (equal (word-fix x) x))
		    (equal (word-fix (rev x))
			   (rev x))))
  )

(encapsulate
  ()
  (local
   (defthm weak-word-cdr
     (implies (weak-wordp x)
              (weak-wordp (cdr x)))
     )
   )

  (local
   (defthm reducedword-cdr
     (implies (reducedwordp x)
              (reducedwordp (cdr x)))
     )
   )

  (local
   (defthm word-fix-cdr
     (implies (and (weak-wordp x)
                   (equal (word-fix x) x))
              (equal (word-fix (cdr x)) (cdr x)))
     :hints (("goal"
              :use ((:instance word-fix=reducedwordp-1 (x x))
                    (:instance reducedword-cdr (x x))
                    (:instance word-fix=reducedwordp (x (cdr x))))

              ))
     )
   )

  (local
   (defthm weak-wordp-rev
     (implies (weak-wordp x)
              (weak-wordp (rev x)))
     )
   )

  (local
   (defthm word-fix-lemma1
     (implies (and
               (reducedwordp x)
               (not (equal x '()))
               (characterp y)
               (weak-wordp (list y))
               (cond ((equal (nth (- (len x) 1) x) (wa)) (not (equal y (wa-inv))))
                     ((equal (nth (- (len x) 1) x) (wb)) (not (equal y (wb-inv))))
                     ((equal (nth (- (len x) 1) x) (wb-inv)) (not (equal y (wb))))
                     ((equal (nth (- (len x) 1) x) (wa-inv)) (not (equal y (wa))))
                     )
               )
              (reducedwordp (append x (list y))))
     )
   )

  (local
   (defthm word-fix-lemma2
     (implies (and (weak-wordp x)
                   (equal (word-fix x) x)
                   (not (equal x '()))
                   (characterp y)
                   (weak-wordp (list y))
                   (cond ((equal (nth (- (len x) 1) x) (wa)) (not (equal y (wa-inv))))
                         ((equal (nth (- (len x) 1) x) (wb)) (not (equal y (wb-inv))))
                         ((equal (nth (- (len x) 1) x) (wb-inv)) (not (equal y (wb))))
                         ((equal (nth (- (len x) 1) x) (wa-inv)) (not (equal y (wa))))
                         )
                   )
              (equal (word-fix (append x (list y))) (append x (list y))))
     :hints (("goal"
              :use ((:instance word-fix-lemma1 (x x))
                    (:instance word-fix=reducedwordp-1 (x x))
                    (:instance word-fix=reducedwordp (x (append x (list y)))))
              ))
     )
   )

  (local
   (defthm character-listp-word
     (implies (or (reducedwordp x)
                  (weak-wordp x))
              (character-listp x))
     )
   )

  (local
   (defthm word-fix-lemma3
     (implies (and (weak-wordp x)
                   (not (atom x)))
              (equal (append (rev (cdr x)) (list (car x))) (rev x)))
     :hints (("goal"
              :use (:instance character-listp-word (x x))
              :in-theory (enable rev)

              ))
     )
   )

  (local
   (defthm word-fix-lemma5
     (implies (and (not (atom x))
                   (word-fix (cdr x)))
              (and (cdr x)
                   (not (equal (rev (cdr x)) nil))
                   (not (atom (rev (cdr x))))))
     )
   )

  (local
   (defthm word-fix-lemma6
     (implies (and (not (atom x))
                   (weak-wordp x))
              (and (characterp (car x))
                   (weak-wordp (list (car x)))))
     )
   )

  (local
   (defthm word-fix-lemma7
     (implies (and (not (atom x))
                   (not (atom (rev (cdr x))))
                   (reducedwordp x))
              (cond ((equal (nth (- (len (rev (cdr x))) 1) (rev (cdr x))) (wa)) (not (equal (car x) (wa-inv))))
                    ((equal (nth (- (len (rev (cdr x))) 1) (rev (cdr x))) (wb)) (not (equal (car x) (wb-inv))))
                    ((equal (nth (- (len (rev (cdr x))) 1) (rev (cdr x))) (wb-inv)) (not (equal (car x) (wb))))
                    ((equal (nth (- (len (rev (cdr x))) 1) (rev (cdr x))) (wa-inv)) (not (equal (car x) (wa))))
                    )
              )
     )
   )

  (defthmd word-fix-lemma
    (implies (and (not (atom x))
                  (word-fix (cdr x))
;(cdr x)
                  (implies (and (weak-wordp (cdr x))
                                (equal (word-fix (cdr x)) (cdr x)))
                           (equal (word-fix (rev (cdr x)))
                                  (rev (cdr x)))))
             (implies (and (weak-wordp x)
                           (equal (word-fix x) x))
                      (equal (word-fix (rev x))
                             (rev x))))
    :hints (("goal"
             :use ((:instance weak-word-cdr (x x))
                   (:instance word-fix-cdr (x x))
                   (:instance weak-wordp-rev (x (cdr x)))
                   (:instance word-fix-lemma2 (x (rev (cdr x))) (y (car x)))
                   (:instance word-fix-lemma3 (x x))
                   (:instance word-fix-lemma5 (x x))
                   (:instance word-fix-lemma6 (x x))
                   (:instance word-fix=reducedwordp-1 (x x))
                   (:instance word-fix=reducedwordp-1 (x (cdr x)))
                   (:instance word-fix-lemma7 (x x)))
             :in-theory nil
             :do-not-induct t
             ))
    )
  )

(defthmd word-fix-lemma-1
  (implies (and (weak-wordp x)
		(equal (word-fix x) x))
	   (equal (word-fix (rev x)) (rev x)))
  :hints (("subgoal *1/10"
	   :use ((:instance word-fix-lemma))
	   )
	  ("subgoal *1/9"
	   :use ((:instance word-fix-lemma))
	   )
	  ("subgoal *1/8"
	   :use ((:instance word-fix-lemma))
	   )
	  ("subgoal *1/7"
	   :use ((:instance word-fix-lemma))
	   )
	  ("subgoal *1/6"
	   :use ((:instance word-fix-lemma))
	   )
	  ("subgoal *1/5"
	   :use ((:instance word-fix-lemma))
	   )
	  ("subgoal *1/4"
	   :use ((:instance word-fix-lemma))
	   )
	  ("subgoal *1/3"
	   :use ((:instance word-fix-lemma))
	   )
	  ))

(defthmd weak-wordp-rev
  (implies (weak-wordp x)
	   (weak-wordp (rev x)))
  )

(defthmd rev-word-inv-reduced
  (implies (reducedwordp x)
	   (reducedwordp (rev x)))
  :hints (("goal"
	   :use ((:instance reducedwordp=>weak-wordp)
		 (:instance word-fix=reducedwordp)
		 (:instance weak-wordp-rev)
		 (:instance word-fix-lemma-1)
		 (:instance word-fix=reducedwordp-1 (x x))
		 (:instance word-fix=reducedwordp-1 (x (rev x))))
	   :in-theory nil

	   ))
  )

(defun word-flip (x)
  (cond ((atom x) nil)
	((equal (car x) (wa)) (cons (wa-inv) (word-flip (cdr x))))
        ((equal (car x) (wa-inv)) (cons (wa) (word-flip (cdr x))))
        ((equal (car x) (wb)) (cons (wb-inv) (word-flip (cdr x))))
        ((equal (car x) (wb-inv)) (cons (wb) (word-flip (cdr x)))))
  )

(defun word-inverse (x)
  (rev (word-flip x))
  )

(defthmd weak-wordp-flip
  (implies (or (a-wordp x)
	       (b-wordp x)
	       (a-inv-wordp x)
	       (b-inv-wordp x)
	       (equal x '()))
	   (weak-wordp (word-flip x)))
  )

(defthmd weak-wordp-flip-1
  (implies (weak-wordp x)
	   (weak-wordp (word-flip x)))
  )

(defthmd weak-wordp-inverse
  (implies (weak-wordp x)
	   (weak-wordp (word-inverse x)))
  :hints (("goal"
	   :use (:instance weak-wordp-flip-1)
	   ))
  )

(defthmd reduced-wordp-flip-1
  (implies (or (a-wordp x)
	       (b-wordp x)
	       (a-inv-wordp x)
	       (b-inv-wordp x))
	   (reducedwordp (word-flip x)))
  :hints (("goal"
	   :use (:instance weak-wordp-inverse)
	   ))
  )

(defthmd reduced-wordp-flip-2
  (implies (equal x '())
	   (reducedwordp (word-flip x)))
  )


(defthmd reduced-wordp-flip
  (implies (reducedwordp x)
	   (reducedwordp (word-flip x)))
  :hints (("goal"
	   :use ((:instance reduced-wordp-flip-1)
		 (:instance reduced-wordp-flip-2))
	   ))
  )

(defthmd reducedwordp-word-inverse
  (implies (reducedwordp x)
	   (reducedwordp (word-inverse x)))
  :hints (("goal"
	   :use (
		 (:instance reduced-wordp-flip (x x))
		 (:instance rev-word-inv-reduced (x (word-flip x)))
		 )
	   ))
  )

(defthmd reduced-inverse-induct-lemma1
  (implies (and (reducedwordp x)
		(not (atom x)))
	   (equal (append (rev (word-flip (cdr x))) (word-flip (list (car x)))) (rev (word-flip x)))
	   )
  )

(defthmd reduced-inverse-induct-lemma2
  (implies (and (character-listp x)
		(not (atom x))
		(character-listp y))
	   (equal (cdr (append x y)) (append (cdr x) y)))
  :hints (("goal"
	   :in-theory (enable append)
	   ))
  )

(defthmd reduced-inverse-induct-lemma3
  (implies (and (reducedwordp x)
		(not (atom x)))
	   (not (atom (rev (word-flip x)))))
  )

(defthmd reduced-inverse-induct-lemma4
  (implies (and (reducedwordp x)
		(not (atom x)))
	   (reducedwordp (word-flip (list (car x)))))
  )

(defthmd reduced-inverse-induct-lemma5
  (implies (and (reducedwordp x)
		(not (atom x)))
	   (equal (compose (list (car x)) (word-flip (list (car x)))) '())))

(defthmd reduced-inverse-induct-lemma6
  (implies (and (reducedwordp x)
		(not (atom x)))
	   (equal
	    (compose (cdr x) (compose (rev (word-flip (cdr x))) (word-flip (list (car x)))))
	    (word-fix (cdr (append x (rev (word-flip x)))))))
  :hints (("goal"
	   :use ((:instance reduced-wordp-flip (x x))
		 (:instance word-fix=reducedwordp (x (rev (word-flip x))))
		 (:instance reduced-inverse-induct-lemma1 (x x))
		 (:instance rev-word-inv-reduced (x (word-flip x)))
		 )
	   :in-theory (enable compose)
	   ))
  )

(defthmd reduced-inverse-induct
  (implies (and (not (atom x))
		(implies (reducedwordp (cdr x))
			 (equal (compose (cdr x)
					 (rev (word-flip (cdr x))))
				nil)))
	   (implies (reducedwordp x)
		    (equal (compose x (rev (word-flip x)))
			   nil)))
  :hints (("goal"
	   :use ((:instance reduced-cdr (x x))
		 (:instance reduced-wordp-flip (x (cdr x)))
		 (:instance rev-word-inv-reduced (x (word-flip (cdr x))))
		 (:instance reduced-wordp-flip (x x))
		 (:instance rev-word-inv-reduced (x (word-flip x)))
		 (:instance assoc-prop (x (cdr x)) (y (rev (word-flip (cdr x)))) (z (word-flip (list (car x)))))
		 (:instance reduced-inverse-induct-lemma1 (x x))
		 (:instance reduced-inverse-induct-lemma2 (x x) (y (rev (word-flip x))))
		 (:instance character-listp-word (x x))
		 (:instance character-listp-word (x (rev (word-flip x))))
		 (:instance reduced-inverse-induct-lemma3 (x x))
		 (:instance reduced-inverse-induct-lemma4 (x x))
		 (:instance word-fix=reducedwordp (x (rev (word-flip x))))
		 (:instance compose (x nil) (y (word-flip (list (car x)))))
		 (:instance compose (x (rev (word-flip (cdr x)))) (y (word-flip (list (car x)))))
		 (:instance reduced-inverse-induct-lemma5 (x x))
		 (:instance compose (x x) (y (rev (word-flip x))))
		 (:instance word-fix (w (append x (rev (word-flip x)))))
		 (:instance reduced-inverse-induct-lemma6 (x x))
		 )
	   :in-theory (enable compose)
	   :do-not-induct t
	   )
	  )
  )

(defthmd reduced-inverse-lemma
  (implies (reducedwordp x)
	   (equal (compose x (rev (word-flip x))) '()))
  :hints (
	  ("subgoal *1/5"
	   :use ((:instance reduced-inverse-induct))
	   )
	  ("subgoal *1/4"
	   :use ((:instance reduced-inverse-induct))
	   )
	  ("subgoal *1/3"
	   :use ((:instance reduced-inverse-induct))
	   )
	  ("subgoal *1/2"
	   :use ((:instance reduced-inverse-induct))
	   )
	  )
  )

(encapsulate
  ()

  (local
   (defthmd rev-word-inv-lemma1
     (implies (weak-wordp x)
              (equal (nth n x)
                     (if (< (nfix n) (len x))
                         (cond ((equal (nth n (word-flip x)) (wb)) (wb-inv))
                               ((equal (nth n (word-flip x)) (wa)) (wa-inv))
                               ((equal (nth n (word-flip x)) (wb-inv)) (wb))
                               ((equal (nth n (word-flip x)) (wa-inv)) (wa))
                               ((equal x '()) nil))
                       nil
                       )
                     )
              )
     :hints (("goal"
              :in-theory (enable nth)
              ))
     )
   )

  (local
   (defthmd rev-word-inv-lemma2
     (implies (weak-wordp x)
              (equal (nth n (word-flip x))
                     (if (< (nfix n) (len x))
                         (cond ((equal (nth n x) (wb)) (wb-inv))
                               ((equal (nth n x) (wa)) (wa-inv))
                               ((equal (nth n x) (wb-inv)) (wb))
                               ((equal (nth n x) (wa-inv)) (wa))
                               ((equal x '()) nil))
                       nil
                       )
                     )
              )
     :hints (("goal"
              :in-theory (enable nth)
              ))
     )
   )

  (local
   (defthmd len-lemma-1
     (implies (weak-wordp x)
              (and (equal (len x) (len (rev x)))
                   (equal (len x) (len (word-flip x)))
                   (equal (len x) (len (rev (word-flip x))))
                   (equal (len x) (len (word-inverse x))))
              )
     )
   )

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd rev-word-inv-lemma3
    (implies (weak-wordp x)
             (equal (nth n x)
                    (if (< (nfix n) (len x))
                        (cond ((equal (nth (- (len x) (+ 1 (nfix n))) (word-inverse x)) (wb)) (wb-inv))
                              ((equal (nth (- (len x) (+ 1 (nfix n))) (word-inverse x)) (wa)) (wa-inv))
                              ((equal (nth (- (len x) (+ 1 (nfix n))) (word-inverse x)) (wb-inv)) (wb))
                              ((equal (nth (- (len x) (+ 1 (nfix n))) (word-inverse x)) (wa-inv)) (wa))
                              ((equal x '()) nil))
                      nil
                      )
                    )
             )
    :hints (("goal"
             :use ((:instance rev-word-inv-lemma1)
                   (:instance rev-word-inv-lemma2)
                   (:instance len-lemma-1))
             :in-theory (enable nth rev)
             :do-not-induct t
             ))
    )

  (defthmd len-x=len-inv-x
    (implies (weak-wordp x)
             (equal (len x) (len (word-inverse x)))
             )
    )

  (defthmd inv-inv-x=x-1
    (implies (and (weak-wordp x)
                  (integerp n)
                  (<= 0 n)
                  (< n
                     (len (word-inverse (word-inverse x)))))
             (equal (nth n (word-inverse (word-inverse x)))
                    (nth n x)))
    :hints (("goal"
             :use ((:instance weak-wordp-inverse (x (word-inverse x)))
                   (:instance len-x=len-inv-x (x x))
                   (:instance len-x=len-inv-x (x (word-inverse x)))
                   (:instance rev-word-inv-lemma3 (x x) (n n))
                   (:instance rev-word-inv-lemma3 (x (word-inverse x)) (n (- (len x) (+ 1 (nfix n)))))
                   (:instance weak-wordp-inverse (x x)))
             :in-theory (e/d (nth) (word-inverse))
             :do-not-induct t
             ))
    )

  (defthmd inv-inv-x=x
    (implies (weak-wordp x)
             (equal (word-inverse (word-inverse x)) x))
    :hints (("goal"
             :do-not-induct t
             :in-theory (disable word-inverse)
             :use ((:functional-instance
                    equal-by-nths
                    (equal-by-nths-hyp (lambda () (weak-wordp x)))
                    (equal-by-nths-lhs (lambda () (word-inverse (word-inverse x))))
                    (equal-by-nths-rhs (lambda () (list-fix x)))))
             )
            ("subgoal 2.1"
             :use ((:instance len-x=len-inv-x (x x))
                   (:instance len-x=len-inv-x (x (word-inverse x)))
                   (:instance weak-wordp-inverse (x x)))
             )
            ("subgoal 1"
             :use ((:instance inv-inv-x=x-1 (x x)))
             )
            )
    )
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd compose-aa-not-nil-1-2
    (implies (and (oddp x)
                  (integerp x))
             (integerp (/ (- x 1) 2))))

  (defthmd compose-aa-not-nil-2-2
    (implies (and (evenp x)
                  (integerp x))
             (and (integerp (/ x 2)))))
  )

(defthmd compose-aa-not-nil-1-1
  (implies (and (equal a b)
                (natp n))
           (equal (nth n a)
                  (nth n b))))

(defthmd compose-aa-not-nil-1-3
  (implies (and (weak-wordp a)
                a
                (natp n)
                (< n (len a)))
           (or (equal (nth n a) (wa))
               (equal (nth n a) (wa-inv))
               (equal (nth n a) (wb))
               (equal (nth n a) (wb-inv)))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd compose-aa-not-nil-1
    (implies (and (weak-wordp a)
                  a
                  (oddp (len a)))
             (not (equal (word-inverse a)
                         a)))
    :hints (("goal"
             :do-not-induct t
             :use ((:instance rev-word-inv-lemma3 (x a)
                              (n (/ (- (len a) 1) 2)))
                   (:instance compose-aa-not-nil-1-1
                              (b a)
                              (a (word-inverse a))
                              (n (/ (- (len a) 1) 2)))
                   (:instance compose-aa-not-nil-1-2 (x (len a)))
                   (:instance compose-aa-not-nil-1-3 (a a) (n (/ (- (len a) 1) 2))))
             :in-theory (disable word-inverse)

             )))
  )

(defthmd compose-aa-not-nil-2-3
  (implies (and (reducedwordp a)
                a
                (natp n)
                (< n (len a))
                (< (+ n 1) (len a))
                (equal (nth n a) (wb-inv)))
           (not (equal (nth (+ n 1) a) (wb)))))

(defthmd compose-aa-not-nil-2-4
  (implies (and (reducedwordp a)
                a
                (natp n)
                (< n (len a))
                (< (+ n 1) (len a))
                (equal (nth n a) (wb)))
           (not (equal (nth (+ n 1) a) (wb-inv)))))

(defthmd compose-aa-not-nil-2-5
  (implies (and (reducedwordp a)
                a
                (natp n)
                (< n (len a))
                (< (+ n 1) (len a))
                (equal (nth n a) (wa-inv)))
           (not (equal (nth (+ n 1) a) (wa)))))

(defthmd compose-aa-not-nil-2-6
  (implies (and (reducedwordp a)
                a
                (natp n)
                (< n (len a))
                (< (+ n 1) (len a))
                (equal (nth n a) (wa)))
           (not (equal (nth (+ n 1) a) (wa-inv)))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd compose-aa-not-nil-2
    (implies (and (weak-wordp a)
                  a
                  (evenp (len a))
                  (equal a (word-inverse a)))
             (not (reducedwordp a)))
    :hints (("goal"
             :do-not-induct t
             :use ((:instance rev-word-inv-lemma3 (x a)
                              (n (- (/ (len a) 2) 1)))
                   (:instance compose-aa-not-nil-1-1
                              (b a)
                              (a (word-inverse a))
                              (n (- (/ (len a) 2) 1)))
                   (:instance compose-aa-not-nil-2-2 (x (len a)))
                   (:instance compose-aa-not-nil-1-3 (a a) (n (- (/ (len a) 2) 1)))
                   (:instance compose-aa-not-nil-2-3 (n (+ -1 (* 1/2 (len a)))) (a a))
                   (:instance compose-aa-not-nil-2-5 (n (+ -1 (* 1/2 (len a)))) (a a))
                   (:instance compose-aa-not-nil-2-6 (n (+ -1 (* 1/2 (len a)))) (a a))
                   (:instance compose-aa-not-nil-2-4 (n (+ -1 (* 1/2 (len a)))) (a a)))
             :in-theory (disable word-inverse reducedwordp)
             )))
  )

(defthmd reduced-inverse
  (implies (reducedwordp x)
	   (equal (compose x (word-inverse x)) '()))
  :hints (("goal"
	   :use (:instance reduced-inverse-lemma)
	   ))
  )

(defun-sk a-inv*w-a-p (w)
  (exists word-a
          (and (a-wordp word-a)
               (equal (compose (list (wa-inv)) word-a) w))))

(defun not-wa-inv-p (w)
  (or (equal w nil)
      (a-wordp w)
      (b-wordp w)
      (b-inv-wordp w)))

(defthmd a-inv*w-a-p-equiv-1
  (implies (a-inv*w-a-p w)
           (and (a-wordp (a-inv*w-a-p-witness w))
                (equal (compose (list (wa-inv)) (a-inv*w-a-p-witness w)) w)))
  :hints (("goal"
           :in-theory (disable a-wordp compose)
           )))

(defthmd a-inv*w-a-p-equiv-2
  (implies (a-wordp w1)
           (not-wa-inv-p (compose (list (wa-inv)) w1)))
  :hints (("goal"
           :use ((:instance word-fix-rev-lemma3-12 (x (wa-inv))
                            (y w1)))
           :cases ((equal (car (cdr y)) nil)
                   (equal (car (cdr y)) (wa))
                   (equal (car (cdr y)) (wb))
                   (equal (car (cdr y)) (wb-inv)))
           )))

(defthmd a-inv*w-a-p-equiv-3
  (implies (a-inv*w-a-p w)
           (not-wa-inv-p w))
  :hints (("goal"
           :use ((:instance a-inv*w-a-p-equiv-1 (w w))
                 (:instance a-inv*w-a-p-equiv-2 (w1 (a-inv*w-a-p-witness w))))
           )))

(defthmd a-inv*w-a-p-equiv-4
  (implies (not-wa-inv-p w)
           (a-inv*w-a-p w))
  :hints (("goal"
           :cases ((equal w nil)
                   (a-wordp w)
                   (b-wordp w)
                   (b-inv-wordp w))
           :in-theory nil)
          ("subgoal 5"
           :use (:instance not-wa-inv-p (w w))
           )
          ("subgoal 4"
           :use (:instance a-inv*w-a-p-suff (word-a (list (wa))) (w w))
           :in-theory (enable a-wordp))
          ("subgoal 3"
           :use ((:instance a-inv*w-a-p-suff (word-a (append (list (wa)) w)) (w w))
                 (:instance word-fix-rev-lemma3-12 (x (wa-inv)) (y (append (list (wa)) w))))
           :in-theory (enable a-wordp)
           )
          ("subgoal 2"
           :use ((:instance a-inv*w-a-p-suff (word-a (append (list (wa)) w)) (w w))
                 (:instance word-fix-rev-lemma3-12 (x (wa-inv)) (y (append (list (wa)) w))))
           :in-theory (enable compose append)
           )
          ("subgoal 1"
           :use ((:instance a-inv*w-a-p-suff (word-a (append (list (wa)) w)) (w w))
                 (:instance word-fix-rev-lemma3-12 (x (wa-inv)) (y (append (list (wa)) w))))
           :in-theory (enable compose append)
           )

          ))

(defthmd a-inv*w-a-p-equiv
  (iff (a-inv*w-a-p w)
       (not-wa-inv-p w))
  :hints (("goal"
           :use ((:instance a-inv*w-a-p-equiv-3 (w w))
                 (:instance a-inv*w-a-p-equiv-4 (w w)))
           )))

(defun-sk b-inv*w-b-p (w)
  (exists word-b
          (and (b-wordp word-b)
               (equal (compose (list (wb-inv)) word-b) w))))

(defun not-wb-inv-p (w)
  (or (equal w nil)
      (a-wordp w)
      (b-wordp w)
      (a-inv-wordp w)))

(defthmd b-inv*w-b-p-equiv-1
  (implies (b-inv*w-b-p w)
           (and (b-wordp (b-inv*w-b-p-witness w))
                (equal (compose (list (wb-inv)) (b-inv*w-b-p-witness w)) w)))
  :hints (("goal"
           :in-theory (disable b-wordp compose)
           )))

(defthmd b-inv*w-b-p-equiv-2
  (implies (b-wordp w1)
           (not-wb-inv-p (compose (list (wb-inv)) w1)))
  :hints (("goal"
           :use ((:instance word-fix-rev-lemma3-12 (x (wb-inv))
                            (y w1)))
           :cases ((equal (car (cdr y)) nil)
                   (equal (car (cdr y)) (wa))
                   (equal (car (cdr y)) (wb))
                   (equal (car (cdr y)) (wa-inv)))
           )))

(defthmd b-inv*w-b-p-equiv-3
  (implies (b-inv*w-b-p w)
           (not-wb-inv-p w))
  :hints (("goal"
           :use ((:instance b-inv*w-b-p-equiv-1 (w w))
                 (:instance b-inv*w-b-p-equiv-2 (w1 (b-inv*w-b-p-witness w))))
           )))

(defthmd b-inv*w-b-p-equiv-4
  (implies (not-wb-inv-p w)
           (b-inv*w-b-p w))
  :hints (("goal"
           :cases ((equal w nil)
                   (a-wordp w)
                   (b-wordp w)
                   (a-inv-wordp w))
           :in-theory nil)
          ("subgoal 5"
           :use (:instance not-wb-inv-p (w w))
           )
          ("subgoal 4"
           :use (:instance b-inv*w-b-p-suff (word-b (list (wb))) (w w))
           :in-theory (enable b-wordp))
          ("subgoal 3"
           :use ((:instance b-inv*w-b-p-suff (word-b (append (list (wb)) w)) (w w))
                 (:instance word-fix-rev-lemma3-12 (x (wb-inv)) (y (append (list (wb)) w))))
           :in-theory (enable b-wordp)
           )
          ("subgoal 2"
           :use ((:instance b-inv*w-b-p-suff (word-b (append (list (wb)) w)) (w w))
                 (:instance word-fix-rev-lemma3-12 (x (wb-inv)) (y (append (list (wb)) w))))
           :in-theory (enable compose append)
           )
          ("subgoal 1"
           :use ((:instance b-inv*w-b-p-suff (word-b (append (list (wb)) w)) (w w))
                 (:instance word-fix-rev-lemma3-12 (x (wb-inv)) (y (append (list (wb)) w))))
           :in-theory (enable compose append)
           )))

(defthmd b-inv*w-b-p-equiv
  (iff (b-inv*w-b-p w)
       (not-wb-inv-p w))
  :hints (("goal"
           :use ((:instance b-inv*w-b-p-equiv-3 (w w))
                 (:instance b-inv*w-b-p-equiv-4 (w w)))
           )))

(defthmd reducedword-equiv-1
  (iff (reducedwordp w)
       (or (not-wb-inv-p w)
           (b-inv-wordp w))))

(defthmd reducedword-equiv-2
  (iff (reducedwordp w)
       (or (b-inv*w-b-p w)
           (b-inv-wordp w)))
  :hints (("goal"
           :use ((:instance reducedword-equiv-1)
                 (:instance b-inv*w-b-p-equiv))
           )))

(defthmd reducedword-equiv-3
  (iff (reducedwordp w)
       (or (not-wa-inv-p w)
           (a-inv-wordp w))))

(defthmd reducedword-equiv-4
  (iff (reducedwordp w)
       (or (a-inv*w-a-p w)
           (a-inv-wordp w)))
  :hints (("goal"
           :use ((:instance reducedword-equiv-3)
                 (:instance a-inv*w-a-p-equiv))
           )))
