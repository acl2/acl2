
(include-book "../graphs")

:q

(load "~/quicklisp/setup.lisp")
(ql:quickload :lisp-z3)


(defpackage :attack
  (:use :cl :z3))

(in-package :attack)

(solver-init)

;; NODE VARS
(defun get-node-var (s i)
  (intern (concatenate 'string s (write-to-string i))))

;; EDGE VARS
(defun get-edge-var (s i j)
  (intern (concatenate 'string s (write-to-string i) (write-to-string j))))

(defun bool-var-specs (vs)
  (cond
    ((equal vs '()) '())
    (t (cons (car vs)
             (cons :bool
                   (bool-var-specs (cdr vs)))))))

(defun int-var-specs (vs)
  (cond
    ((endp vs) '())
    (t (cons (car vs)
             (cons :int
                   (bool-var-specs (cdr vs)))))))

(defun pqx (vs)
  (cond
   ((endp vs) '())
   (t (ACL2S::b* ((i (car vs))
                  (pe (get-node-var "P" i))
                  (qi (get-node-var "Q" i))
                  (xi (get-node-var "X" i)))
                 (append `((or (not ,pe) (not ,qi))
                           (or (not ,pe) (not ,xi))
                           (or (not ,qi) (not ,xi))
                           (or ,pe ,qi ,xi)) 
                         (pqx (cdr vs)))))))
                            
(defun pqx-constraints (vs)
  (cons 'AND (pqx vs)))

;;(pqx-constraints '(V1 V2 V3))


(defun partitioned-edge (g acc)
  (cond
   ((endp g) (cons 'AND acc))
   (t (ACL2S::b* ((i (caar g))
                  (j (cdar g))
                  (pe (get-node-var "P" i))
                  (qi (get-node-var "Q" i))
                  (xi (get-node-var "X" i))
                  (pj (get-node-var "P" j))
                  (qj (get-node-var "Q" j))
                  (xj (get-node-var "X" j)))
                 (partitioned-edge (cdr g) (append `((or (not ,pe) (not ,qj))
                                                     (or (not ,pj) (not
                                                                    ,qi)))
                                                   acc))))))
                                                        

(assert (equal '(AND (OR (NOT PV1) (NOT QV2)) (OR (NOT PV2) (NOT QV1)))
               (partitioned-edge '((V1 . V2)) nil)))


(defun limit-partition (vs k s)
  (let ((qn s))
    `(AND
      (<=
       ,(cons '+
              (mapcar (lambda (i) `(if ,(get-node-var "X" i) 1 0)) vs))
       ,k)
    
      (<= ,qn
          ,(cons '+
                 (mapcar (lambda (i) `(if ,(get-node-var "P" i) 1 0)) vs)))
      
      (<= ,qn
          ,(cons '+
                 (mapcar (lambda (i) `(if ,(get-node-var "Q" i) 1 0)) vs)))
      )))
    
  
(limit-partition '(V1 V2 V3) 3)

(defun query (g k s)
  (ACL2S::b*
   ((vs (remove-duplicates
         (append (mapcar #'car g) (mapcar #'cdr g))
         :test #'equal))
    (decls
     (bool-var-specs (append (mapcar (lambda (i) (get-node-var "X" i)) vs)
                             (mapcar (lambda (i) (get-node-var "P" i)) vs)
                             (mapcar (lambda (i) (get-node-var "Q" i)) vs))))
    (constr (cons 'AND `(,(pqx-constraints vs)
                         ,(partitioned-edge g nil)
                         ,(limit-partition vs k s)))))
   (z3-assert-fn decls constr)))


(solver-push)
(query '((P1 . P2) (P2 . P3)) 1)
(check-sat)
(solver-pop)


;; * (time (check-sat))
;;   ^C ^C^CEvaluation took:
;;   9690.860 seconds of real time
;;   9677.943205 seconds of total run time (9654.018389 user, 23.924816 system)
;;   99.87% CPU
;;   0 bytes consed

;; (solver-push)
;; (query (ACL2S::take 3000 ACL2S::*ropsten*) 30)
;; (time (check-sat))
;; (solver-pop)


;; (solver-push)
;; (query (ACL2S::take 4000 ACL2S::*ropsten*) 60)
;; (time (check-sat))
;; (solver-pop)

;; Evaluation took:
;;   51.460 seconds of real time
;;   51.459950 seconds of total run time (51.391735 user, 0.068215 system)
;;   100.00% CPU


;; (solver-push)
;; (ACL2S::b*
;;  ((g ACL2S::*ropsten*)
;;   (vs (ACL2S::remove-duplicates
;;          (ACL2S::append (mapcar #'car g) (mapcar #'cdr g))
;;          :test #'equal))
;;     (n (ACL2S::len vs))
;;     (k (ACL2S::floor n 10))
;;     (s 100))
;;    (query g k s))
;; (time (check-sat))
;; (solver-pop)


;; inctrementally from k=50 to 30
;; SAT , 518.543 seconds for the last round
(solver-push)
(ACL2S::b*
 ((g ACL2S::*rinkeby*)
  (vs (ACL2S::remove-duplicates
         (ACL2S::append (mapcar #'car g) (mapcar #'cdr g))
         :test #'equal))
    (n (ACL2S::len vs))
    (k 30)
    (s 50))
   (query g k s))
(time (check-sat))
(solver-pop)


(solver-push)
(ACL2S::b*
 ((g ACL2S::*ropsten*)
  (vs (ACL2S::remove-duplicates
         (ACL2S::append (mapcar #'car g) (mapcar #'cdr g))
         :test #'equal))
    (n (ACL2S::len vs))
    (k 10)
    (s 20))
   (query g k s))
(time (check-sat))
(solver-pop)


(defun pos-x-vars (vs al acc)
  (cond
   ((endp vs) acc)
   (t (pos-x-vars (cdr vs) al (cons (cdr (ACL2S::assoc-equal (get-node-var "X" (car cs)) al))
                                    acc)))))

(defun validate (al)
  (ACL2S::b*
   ((g *ropsten*)
    (vs (remove-duplicates
         (append (mapcar #'car g) (mapcar #'cdr g))
         :test #'equal)))
   (pos-x-vars vs al nil)))
