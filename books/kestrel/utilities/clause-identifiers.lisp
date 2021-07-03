; Utilities related to clause-identifiers
;
; Copyright (C) 2017 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Utilities related to clause-identifiers (see :doc clause-identifier).  These
;; are useful in writing computed hints.

;recognize Subgoal 1, Subgoal 2, Subgoal 3, etc.
;; Should look like ((0) (1) . 0), etc.
(defun top-level-subgoalp (id)
  (and (eql 2 (len id))
       (eql 0 (cddr id))
       (equal '(0) (car id))
       (eql 1 (len (cadr id)))
       (posp (car (cadr id)))))

;; test: (top-level-subgoalp '((0) (1) . 0))

;recognize Subgoal *1/1, Subgoal *1/2, Subgoal *1/3, etc.
;Should look like: ((0 1) (<number>) . 0), etc.
(defun top-subgoal-of-inductionp (id)
;  (declare (xargs :guard t))
  (and (eql 2 (len id))
       (eql 0 (cddr id))
       (equal '(0 1) (car id))
       (eql 1 (len (cadr id)))
       (posp (car (cadr id)))))

;; todo: Get parse-clause-id into logic mode (first add measure to
;; parse-natural1).  Then we could just call it here.

;; From (PARSE-CLAUSE-ID "Goal'").
(defun goal-primep (id)
  (declare (xargs :guard t))
  (equal id '((0) nil . 1)))

(defun direct-descendant-of-goalp (id)
  (or (top-level-subgoalp id) ; in case the goal was split
      (goal-primep id) ;in case the "split" produced only 1 subgoal
      ))
