; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(include-book "checkpoints")

(defmacro print-and-run (form &optional (print 't))
  `(let ((chan (standard-co state))) ; capturable by ,form, but no big deal
     (pprogn (fms "----------~|~x0:~|"
                  (list (cons #\0 ',form))
                  chan state nil)
             ,(if print
                  `(fms "~x0~|----------~|~%"
                        (list (cons #\0 ,form))
                        chan state nil)
                `(pprogn ,form
                         (princ$ "----------" chan state)
                         (newline chan state)
                         (newline chan state))))))

(defmacro checkpoint-tests ()
  '(pprogn (print-and-run (checkpoint-list t state))
           (print-and-run (checkpoint-list nil state))
           (print-and-run (checkpoint-list-pretty t state))
           (print-and-run (checkpoint-list-pretty nil state))
           (print-and-run (checkpoint-info-list t state))
           (print-and-run (checkpoint-info-list nil state))
           (print-and-run (show-checkpoint-list) nil)
           (print-and-run (show-checkpoint-list t) nil)))

;;;;;;;;;;
;;; The following test shows <GOAL> and also an "Abort?" cause.
;;; Also, it demonstrates that when aborting ("abandoning") work done in favor
;;; of proving the original goal by induction, checkpoint-list and related
;;; tools consider only the part of the proof attempt after that.  Also note
;;; that unlike the checkpoint display at the end of a proof attempt, all
;;; checkpoints aren't included rather than limiting to the default of 3.
;;;;;;;;;;

(defthm foo (equal (append (append (if a x z) y) x) (append x y x)))

(checkpoint-tests)

;;;;;;;;;;
;;; This is just a random test along the way to the next one.
;;;;;;;;;;

(defund h (x y)
  (list x y))

(defthm null-cddr-h
  (implies (force (equal (append x y) (append y x)))
           (equal (cddr (h x y)) nil)))

(checkpoint-tests)

;;;;;;;;;;
;;; The next test shows handling of a failed forcing round.  Also, we check
;;; here that THM works.  (Technical note: It didn't before 12/27/2021 because
;;; *protected-system-state-globals* didn't exclude gag-state-saved.)
;;;;;;;;;;

(defthm null-cddr-h
  (implies (force (equal (append x y) (append y x)))
           (equal (cddr (h x y)) nil))
  :hints (("Goal" :in-theory (enable h))))

(thm (null (cddr (h x y))))
; Note that "Forced goals?" in the following says "No", because there are no
; forced goals during the forcing round.
(checkpoint-tests)

;;;;;;;;;;
;;; The next test is similar to the one just above, but this time the proof
;;; fails before going into a forcing round, so "Forced goals?" says "Yes".
;;; It also shows an empty list of non-top-level checkpoints.  And finally, it
;;; shows the need for :otf-flg in order to avoid just seeing the result of the
;;; failed attempt to prove the original goal by induction after aborting the
;;; initial proof attempt.
;;;;;;;;;;

(thm (and (null (cddr (h x y))) (equal (car x) x)))
(checkpoint-tests)
(thm (and (null (cddr (h x y))) (equal (car x) x))
     :otf-flg t)
(checkpoint-tests)

;;;;;;;;;;
;;; Check the :UNAVAILABLE case.
;;;;;;;;;;

(thm (equal x x))
(checkpoint-tests)

;;;;;;;;;;
;;; Revisit a couple of earlier tests, this time using prove$.
;;;;;;;;;;

(include-book "tools/prove-dollar" :dir :system)
(prove$ '(equal (append (append (if a x z) y) x) (append x y x)))
(checkpoint-tests)
(prove$ '(null (cddr (h x y))))
(checkpoint-tests)

;;;;;;;;;;
;;; Test saving into the ld-history.
;;;;;;;;;;

(defun checkpoint-list-both (state)
  (declare (xargs :stobjs state
                  :guard (checkpoint-list-guard :both state)))
  (let ((lst (checkpoint-list t state)))
    (if (eq lst :unavailable)
        nil
      (list lst
            (checkpoint-list nil state)))))

(defun my-set-ld-history-entry-user-data (input error-flg stobjs-out/value
                                                state)
  (declare (ignore input error-flg stobjs-out/value)
           (xargs :stobjs state
                  :guard t))
  (if (checkpoint-list-guard :both state)
      (checkpoint-list-both state)
    (er hard? 'my-set-ld-history-entry-user-data
        "Unexpected violation of ~x0."
        '(checkpoint-list-guard :both state))))

(defattach (set-ld-history-entry-user-data my-set-ld-history-entry-user-data)
  :system-ok t)

(thm (equal x x)) ; clear checkpoint info
(thm (and (null (cddr (h x y))) (equal (car x) x))
     :otf-flg t)
(assert-event
 (equal (ld-history-entry-user-data (car (ld-history state)))
        (list '(((EQUAL (CAR X) X))) ; one clause, which is a singleton
              NIL                    ; no non-top-level clauses
              )))
