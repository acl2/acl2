;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(skip-proofs
 (defthm skip-proof-hint
   nil
   :rule-classes nil)
 )

(defun sub-seq (spec id)
  (if (and (not (consp spec)) (not (consp id))) nil
    (if (not (consp id)) t
      (if (not (consp spec)) nil
        (and (equal (car spec) (car id))
             (sub-seq (cdr spec) (cdr id)))))))

(set-state-ok t)

(defun except-fn (spec print clause stable id state)
  (declare (ignorable stable clause state)
           (xargs :mode :program))
  (let ((id (cadr id)))
    (if (equal spec id) (and print (cw "~x0~%" (prettyify-clause clause nil (w state))))
      (and id
           (if (sub-seq id spec) nil ;; (cw "~x0~%" (prettyify-clause clause nil (w state)))
             (and
              (not (sub-seq spec id))
              '(:use skip-proof-hint)))))))

(defmacro except (subgoal &key (print 't))
  (let ((spec (cadr (parse-clause-id subgoal))))
    `(except-fn ',spec ,print clause stable-under-simplificationp id state)))

;; (include-book "except" :skip-proofs-okp t)

(defun goal-fn (spec clause stable id state)
  (declare (ignore clause stable state))
  (let ((id (cadr id)))
    (equal spec id)))

(defmacro Goal (subgoal)
  (let ((spec (cadr (parse-clause-id subgoal))))
    `(goal-fn ',spec clause stable-under-simplificationp id state)))
