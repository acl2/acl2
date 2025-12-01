;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

;; Note: If you modify each must-fail call below as follows, then you can LD
;; this file without error using ACL2 Version 8.6.
;; - If (must-fail <form>) is preceded by a comment, "Full script for former
;;   soundness bug", then replace it by <form>.
;; - Remove (or comment out) every other must-fail call.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :System)
(include-book "std/stobjs/absstobjs" :dir :system)

;; Constrain some predicate p.
(defstub p (x) nil)

;; Evaluator for use in clause processors later
(defevaluator my-ev my-ev-lst
  ((not x)
   (if x y z)
   (p x)))

;; ---------------------------------------------------------------------
;; Original variant of the soundness bug: stobj recognizer depends on P.
;; ---------------------------------------------------------------------

;; Creating a stobj whose recognizer depends on P after attaching to P should fail
(must-fail
 (progn
   (defattach p integerp)
   (defstobj st
     (fld :type (or null (satisfies p)) :initially nil)))
 :with-output-off nil)

;; Creating a stobj whose recognizer depends on P then attaching to P should fail
(must-fail
 (progn
   (defstobj st
     (fld :type (or null (satisfies p)) :initially nil))
   (defattach p integerp))
 :with-output-off nil)

;; Full script for former soundness bug
(must-fail
 (progn

   ;; Attach something to P, introduce ST, then update ST such that its
   ;; invariant holds for this particular attachment of P, but not in general.
   (defattach p integerp)

   (defstobj st
     (fld :type (or null (satisfies p)) :initially nil))

   ;; This doesn't work directly because it checks the guard for update-fld without attachments enabled,
   ;; but we just need to define a function that will do it.
   ;; (update-fld -1 st)

   (defun set-st (x st)
     (declare (xargs :stobjs st))
     (if (p x)
         (update-fld x st)
       st))

   ;; this just does (set-st -1 st) but wrapped in an event
   (make-event
    (let* ((st (set-st -1 st)))
      (mv nil '(value-triple :ok) state st)))

   ;; We already have a bad problem at this point -- st's recognizer is now only
   ;; true in the defattach world, not the logical world. In particular, note that
   ;; the function below should always produce something satisfying (or (not val)
   ;; (p val)), but if we attach p to (e.g.) natp, we can show computations
   ;; violating that fact:

   (defun get-st (st)
     (declare (xargs :stobjs st))
     (mbe :logic (if (p (fld st))
                     (fld st)
                   nil)
          :exec (fld st)))

   (defthm p-of-get-st
     (implies (get-st st)
              (p (get-st st))))

   (encapsulate nil
     (local (defattach p natp))
     (assert-event (not (implies (get-st st)
                                 (p (get-st st))))))


   (defun my-cp (clause hint st)
     (declare (Xargs :stobjs st
                     :guard t)
              (ignore hint))
     (mv nil
         (let ((val (get-st st)))
           (if val
               (list (cons `(not (p (quote ,val))) clause))
             (list clause)))
         st))


   ;; needed to satisfy the clause processor/defattach restrictions since p is ancestral in my-cp
   (defattach p nil)

   (defthm my-cp-correct
     (implies (and (pseudo-term-listp clause)
                   (alistp a)
                   (my-ev (conjoin-clauses (clauses-result (my-cp clause hint st))) a))
              (my-ev (disjoin clause) a))
     :rule-classes :clause-processor)

   (defthm p-of-neg1
     (p -1)
     :hints (("goal" :clause-processor (my-cp clause nil st))))


   (defthm bad
     nil
     :hints (("goal" :use ((:functional-instance p-of-neg1
                            (p natp)))))
     :rule-classes nil))
 :with-output-off nil)

;; Full script for former soundness bug
;; (This is a variant of the one just, where this time, p is not ancestral in
;; the evaluator.)
(must-fail
 (progn

   ;; Attach something to P, introduce ST, then update ST such that its
   ;; invariant holds for this particular attachment of P, but not in general.
   (defattach p integerp)

   (defstobj st
     (fld :type (or null (satisfies p)) :initially nil))

   ;; This doesn't work directly because it checks the guard for update-fld without attachments enabled,
   ;; but we just need to define a function that will do it.
   ;; (update-fld -1 st)

   (defun set-st (x st)
     (declare (xargs :stobjs st))
     (if (p x)
         (update-fld x st)
       st))

   ;; this just does (set-st -1 st) but wrapped in an event
   (make-event
    (let* ((st (set-st -1 st)))
      (mv nil '(value-triple :ok) state st)))

   (defun check-st (st)
     (declare (xargs :stobjs st))
     (mbe :logic t
          :exec (and (or (not (fld st))
                         (p (fld st)))
                     t)))
 
   (defevaluator my-ev2 my-ev2-lst
     ((not x)
      (if x y z)))
 
   (defun my-cp (clause hint st)
     (declare (Xargs :stobjs st
                     :guard t)
              (ignore hint))
     (mv nil
         (let ((val (check-st st)))
           (if val
               (list clause)
             (list (cons ''t clause))))
         st))
 
   (defthm my-cp-correct
     (implies (and (pseudo-term-listp clause)
                   (alistp a)
                   (my-ev2 (conjoin-clauses (clauses-result (my-cp clause hint st))) a))
              (my-ev2 (disjoin clause) a))
     :rule-classes :clause-processor)
 
   (defattach p natp)

   (defthm bad
     nil
     :hints (("goal" :clause-processor (my-cp clause nil st)))
     :rule-classes nil))
 :with-output-off nil)


;; ---------------------------------------------------------------------
;; Second variant of the soundness bug: abstract stobj where neither
;; the recognizer nor foundation stobj recognizer depend on p, but the
;; corr-fn does (as well as an exported updater and accessor).
;; ---------------------------------------------------------------------

;; No dependency on P
(defstobj st1$c
  (fld1$c :initially nil))

;; Restricted form of updater: only update if val satisfies
;; (or (not val) (p val)).
(defun update-fld1-restr$c (val st1$c)
  (declare (xargs :stobjs st1$c))
  (if (or (not val) (p val))
      (update-fld1$c val st1$c)
    st1$c))

;; Logic form of same updater -- st1$a represents just fld by itself
(defun update-fld1$a (val st1$a)
  (declare (xargs :guard t))
  (if (or (not val) (p val))
      val
    st1$a))

;; Logic form of accessor: always returns a value satisfying (or (p val) (not val))
(defun fld1$a (st1$a)
  (declare (xargs :guard t))
  (if (p st1$a) st1$a nil))

;; Correlation: the logic version equals the fld1 of the exec version,
;; and that satisfiers (or (not x) (p x)).
(defun corr1 (st1$c x)
  (declare (xargs :Stobjs st1$c))
  (and (or (not x) (p x))
       (equal x (fld1$c st1$c))))

;; Trivial recognizer
(defun st1$ap (x)
  (declare (xargs :guard t)
           (ignore x))
  t)

(defun create-st1$a ()
  (declare (xargs :guard t))
  nil)


(local (in-theory (disable (fld1$a))))

;; Creating an abstract stobj whose corr-fn depends on P after attaching to P should fail
(must-fail
 (progn
   (defattach p integerp)
   (stobjs::defabsstobj-events st1
     :foundation st1$c
     :recognizer (st1p :logic st1$ap :exec st1$cp)
     :creator (create-st1 :logic create-st1$a :exec create-st1$c)
     :corr-fn corr1
     :exports ((fld1 :logic fld1$a :exec fld1$c)
               (update-fld1 :logic update-fld1$a :exec update-fld1-restr$c))))
 :with-output-off nil)

;; Creating an abstract stobj whose corr-fn depends on P and then attaching to P should fail
(must-fail
 (progn
   (stobjs::defabsstobj-events st1
     :foundation st1$c
     :recognizer (st1p :logic st1$ap :exec st1$cp)
     :creator (create-st1 :logic create-st1$a :exec create-st1$c)
     :corr-fn corr1
     :exports ((fld1 :logic fld1$a :exec fld1$c)
               (update-fld1 :logic update-fld1$a :exec update-fld1-restr$c)))
   (defattach p integerp))
 :with-output-off nil)


;; Full script for former soundness bug
(must-fail
 (progn
   (stobjs::defabsstobj-events st1
     :foundation st1$c
     :recognizer (st1p :logic st1$ap :exec st1$cp)
     :creator (create-st1 :logic create-st1$a :exec create-st1$c)
     :corr-fn corr1
     :exports ((fld1 :logic fld1$a :exec fld1$c)
               (update-fld1 :logic update-fld1$a :exec update-fld1-restr$c)))
   (defattach p integerp)

   ;; Update the abstract stobj -- note that the value depends on the attachment of p.
   (make-event
    (let* ((st1 (update-fld1 -1 st1)))
      (mv nil '(value-triple :ok) state st1)))

   ;; Again, an invariant for st1 (whose invariance depends on the correlation function)
   ;; now is only true in the defattach world, not the logical world. In
   ;; particular, fld1 should logically always return something satisfying (or (not val) (p val)),
   ;; and if we change the attachment for p it will not:
   (defthm p-of-fld1
     (implies (fld1 st)
              (p (fld1 st))))

   (encapsulate nil
     (local (defattach p natp))
     (assert-event (not (implies (fld1 st1)
                                 (p (fld1 st1))))))

   (defun my-cp1 (clause hint st1)
     (declare (xargs :stobjs st1
                     :guard t)
              (ignore hint))
     (mv nil
         (let ((val (fld1 st1)))
           (if val
               (list (cons `(not (p (quote ,val))) clause))
             (list clause)))
         st1))

   ;; satisfy clause processor ancestor restrictions
   (defattach p nil)
   
   (defthm my-cp1-correct
     (implies (and (pseudo-term-listp clause)
                   (alistp a)
                   (my-ev (conjoin-clauses (clauses-result (my-cp1 clause hint st1))) a))
              (my-ev (disjoin clause) a))
     :rule-classes :clause-processor)

   (defthm p-of-neg1
     (p -1)
     :hints (("goal" :clause-processor (my-cp1 clause nil st1))))


   (defthm bad
     nil
     :hints (("goal" :use ((:functional-instance p-of-neg1
                            (p natp)))))
     :rule-classes nil))
 :with-output-off nil)


;; ---------------------------------------------------------------------
;; Third variant: abstract stobj where the recognizer depends on P but not
;; the corr-fn.
;; ---------------------------------------------------------------------

;; No dependency on P
(defstobj st2$c
  (fld2$c :initially nil))

;; Restricted form of updater: only update if val satisfies
;; (or (not val) (p val)).
(defun update-fld2-restr$c (val st2$c)
  (declare (xargs :stobjs st2$c))
  (if (or (not val) (p val))
      (update-fld2$c val st2$c)
    st2$c))

;; Logic form of same updater -- st2$a represents just fld by itself
(defun update-fld2$a (val st2$a)
  (declare (xargs :guard t))
  (if (or (not val) (p val))
      val
    st2$a))

;; Recognizer depends on P
(defun st2$ap (x)
  (declare (xargs :guard t))
  (and (or (not x) (p x)) t))

;; Logic form of accessor: always returns a value satisfying (or (p val) (not
;; val)).  Since the recognizer is allowed to be in the guard "for free" and
;; the guard is assumed when proving the correlation theorem, this correlates
;; to fld2$c even though fld2$c doesn't check the type.
(defun fld2$a (st2$a)
  (declare (xargs :guard (st2$ap st2$a)))
  (if (or (not st2$a) (p st2$a)) st2$a nil))

;; Correlation: the logic version equals the fld2 of the exec version,
;; and that satisfiers (or (not x) (p x)).
(defun corr2 (st2$c x)
  (declare (xargs :Stobjs st2$c))
  (equal x (fld2$c st2$c)))

(defun create-st2$a ()
  (declare (xargs :guard t))
  nil)


(local (in-theory (disable (fld2$a))))


;; Creating an abstract stobj whose corr-fn depends on P after attaching to P should fail
(must-fail
 (progn
   (defattach p integerp)
   (stobjs::defabsstobj-events st2
     :foundation st2$c
     :recognizer (st2p :logic st2$ap :exec st2$cp)
     :creator (create-st2 :logic create-st2$a :exec create-st2$c)
     :corr-fn corr2
     :exports ((fld2 :logic fld2$a :exec fld2$c)
               (update-fld2 :logic update-fld2$a :exec update-fld2-restr$c))))
 :with-output-off nil)

;; Creating an abstract stobj whose corr-fn depends on P and then attaching to P should fail
(must-fail
 (progn
   (stobjs::defabsstobj-events st2
     :foundation st2$c
     :recognizer (st2p :logic st2$ap :exec st2$cp)
     :creator (create-st2 :logic create-st2$a :exec create-st2$c)
     :corr-fn corr2
     :exports ((fld2 :logic fld2$a :exec fld2$c)
               (update-fld2 :logic update-fld2$a :exec update-fld2-restr$c)))
   (defattach p integerp))
 :with-output-off nil)


;; Full script for former soundness bug
(must-fail
 (progn
   (stobjs::defabsstobj-events st2
     :foundation st2$c
     :recognizer (st2p :logic st2$ap :exec st2$cp)
     :creator (create-st2 :logic create-st2$a :exec create-st2$c)
     :corr-fn corr2
     :exports ((fld2 :logic fld2$a :exec fld2$c)
               (update-fld2 :logic update-fld2$a :exec update-fld2-restr$c)))
   (defattach p integerp)
   ;; Update the abstract stobj -- note that the value depends on the attachment of p.
   (make-event
    (let* ((st2 (update-fld2 -1 st2)))
      (mv nil '(value-triple :ok) state st2)))

   ;; Again, the invariant for st2 (implicitly including the correlation function)
   ;; now is only true in the defattach world, not the logical world. In
   ;; particular, fld2 should logically always return something satisfying (or (not val) (p val)),
   ;; and if we change the attachment for p it will not:
   (defthm p-of-fld2
     (implies (fld2 st)
              (p (fld2 st))))

   (encapsulate nil
     (local (defattach p natp))
     (assert-event (not (implies (fld2 st2)
                                 (p (fld2 st2))))))



   (defun my-cp2 (clause hint st2)
     (declare (xargs :stobjs st2
                     :guard t)
              (ignore hint))
     (mv nil
         (let ((val (fld2 st2)))
           (if val
               (list (cons `(not (p (quote ,val))) clause))
             (list clause)))
         st2))

   ;; satisfy clause processor ancestor restrictions
   (defattach p nil)

   (defthm my-cp2-correct
     (implies (and (pseudo-term-listp clause)
                   (alistp a)
                   (my-ev (conjoin-clauses (clauses-result (my-cp2 clause hint st2))) a))
              (my-ev (disjoin clause) a))
     :rule-classes :clause-processor)

   (defthm p-of-neg1
     (p -1)
     :hints (("goal" :clause-processor (my-cp2 clause nil st2))))


   (defthm bad
     nil
     :hints (("goal" :use ((:functional-instance p-of-neg1
                            (p natp)))))
     :rule-classes nil)))






;; ---------------------------------------------------------------------
;; Fourth variant of the soundness bug: same as the second variant
;; (the corr-fn depends on the attachment), but this time we specify
;; :corr-fn-exists nil to make sure that works (fails)
;; ---------------------------------------------------------------------

;; No dependency on P
(defstobj st3$c
  (fld3$c :initially nil))

;; Restricted form of updater: only update if val satisfies
;; (or (not val) (p val)).
(defun update-fld3-restr$c (val st3$c)
  (declare (xargs :stobjs st3$c))
  (if (or (not val) (p val))
      (update-fld3$c val st3$c)
    st3$c))

;; Logic form of same updater -- st3$a represents just fld by itself
(defun update-fld3$a (val st3$a)
  (declare (xargs :guard t))
  (if (or (not val) (p val))
      val
    st3$a))

;; Logic form of accessor: always returns a value satisfying (or (p val) (not val))
(defun fld3$a (st3$a)
  (declare (xargs :guard t))
  (if (p st3$a) st3$a nil))

;; Correlation: the logic version equals the fld3 of the exec version,
;; and that satisfies (or (not x) (p x)).
(defun corr3 (st3$c x)
  (declare (xargs :Stobjs st3$c))
  (and (or (not x) (p x))
       (equal x (fld3$c st3$c))))

;; Trivial recognizer
(defun st3$ap (x)
  (declare (xargs :guard t)
           (ignore x))
  t)

(defun create-st3$a ()
  (declare (xargs :guard t))
  nil)


(local (in-theory (disable (fld3$a))))

;; Creating an abstract stobj whose corr-fn depends on P after attaching to P should fail
(must-fail
 (progn
   (defattach p integerp)
   (stobjs::defabsstobj-events st3
     :foundation st3$c
     :recognizer (st3p :logic st3$ap :exec st3$cp)
     :creator (create-st3 :logic create-st3$a :exec create-st3$c)
     :corr-fn corr3 :corr-fn-exists nil
     :exports ((fld3 :logic fld3$a :exec fld3$c)
               (update-fld3 :logic update-fld3$a :exec update-fld3-restr$c))))
 :with-output-off nil)

;; Creating an abstract stobj whose corr-fn depends on P and then attaching to P should fail
(must-fail
 (progn
   (stobjs::defabsstobj-events st3
     :foundation st3$c
     :recognizer (st3p :logic st3$ap :exec st3$cp)
     :creator (create-st3 :logic create-st3$a :exec create-st3$c)
     :corr-fn corr3 :corr-fn-exists nil
     :exports ((fld3 :logic fld3$a :exec fld3$c)
               (update-fld3 :logic update-fld3$a :exec update-fld3-restr$c)))
   (defattach p integerp))
 :with-output-off nil)



;; ---------------------------------------------------------------------
;; Fifth variant of the soundness bug: here the correlation function
;; depends on the attachment, but the logical sides of the exports don't --
;; but we can still get an unsoundness from the executable parts depending on
;; the attachment.
;; ---------------------------------------------------------------------

(defstobj st4$c
  (fld4$c :initially nil))

;; Restricted form of updater: only update if val satisfies
;; (or (not val) (p val)).
(defun update-fld4-restr$c (val st4$c)
  (declare (xargs :stobjs st4$c))
  (if (or (not val) (p val))
      (update-fld4$c val st4$c)
    st4$c))

;; This is what we'll show the conflict on -- the abstract version of this will
;; always return T since what we're checking here is supposed to be an
;; invariant.
(defun fld4-check$c (st4$c)
  (declare (xargs :stobjs st4$c))
  (let ((val (fld4$c st4$c)))
    (and (or (not val) (p val)) t)))

;; For the abstract version of this, we'll just always return T from the
;; fld4-check function, and the stobj will always be nil (but irrelevant).
(defun create-st4$a ()
  (declare (xargs :guard t))
  nil)
(defun st4$ap (st4$a)
  (declare (xargs :guard t)
           (ignore st4$a))
  t)
(defun update-fld4$a (val st4$a)
  (declare (ignore val st4$a)
           (xargs :guard t))
  nil)
(defun fld4-check$a (st4$a)
  (declare (xargs :guard t)
           (ignore st4$a))
  t)

(defun corr4 (st4$c st4$a)
  (declare (xargs :stobjs st4$c)
           (ignore st4$a))
  (fld4-check$c st4$c))


(must-fail
 (progn
   (defattach p integerp)
   (stobjs::defabsstobj-events st4
     :foundation st4$c
     :recognizer (st4p :logic st4$ap :exec st4$cp)
     :creator (create-st4 :logic create-st4$a :exec create-st4$c)
     :corr-fn corr4 :corr-fn-exists nil
     :exports ((fld4-check :logic fld4-check$a :exec fld4-check$c)
               (update-fld4 :logic update-fld4$a :exec update-fld4-restr$c)))))

(must-fail
 (progn
   (stobjs::defabsstobj-events st4
     :foundation st4$c
     :recognizer (st4p :logic st4$ap :exec st4$cp)
     :creator (create-st4 :logic create-st4$a :exec create-st4$c)
     :corr-fn corr4 :corr-fn-exists nil
     :exports ((fld4-check :logic fld4-check$a :exec fld4-check$c)
               (update-fld4 :logic update-fld4$a :exec update-fld4-restr$c)))
   (defattach p integerp)))


;; Full script for former soundness bug
(must-fail
 (progn
   (stobjs::defabsstobj-events st4
     :foundation st4$c
     :recognizer (st4p :logic st4$ap :exec st4$cp)
     :creator (create-st4 :logic create-st4$a :exec create-st4$c)
     :corr-fn corr4 ;; :corr-fn-exists nil
     :exports ((fld4-check :logic fld4-check$a :exec fld4-check$c)
               (update-fld4 :logic update-fld4$a :exec update-fld4-restr$c)))
   (defattach p integerp)
   (make-event
    (let* ((st4 (update-fld4 -1 st4)))
      (mv nil '(value-triple :ok) state st4)))

   (defattach p natp)

   (assert-event (not (fld4-check st4)))

   ;; Evaluator for use in the following clause proc
   (defevaluator my-ev4 my-ev4-lst
     ((not x)
      (if x y z)))

   (defun my-cp4 (clause hint st4)
     (declare (xargs :stobjs st4)
              (ignore hint))
     (mv nil
         (if (fld4-check st4)
             (list clause)
           nil)
         st4))

   (defthm my-cp4-correct
     (implies (and (pseudo-term-listp clause)
                   (alistp a)
                   (my-ev4 (conjoin-clauses (clauses-result (my-cp4 clause hint st4))) a))
              (my-ev4 (disjoin clause) a))
     :rule-classes :clause-processor)

   (defthm bad4
     nil
     :hints (("goal" :clause-processor (my-cp4 clause nil st4)))
     :rule-classes nil)))
