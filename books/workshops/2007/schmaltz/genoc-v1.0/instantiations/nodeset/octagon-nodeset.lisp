;; Julien Schmaltz
;; File: octagon-nodeset.lisp
;; August 15th
;; definition and validation of the nodes of the Octagon
(in-package "ACL2")
;; we import the book containing the generic definition of NodeSet
(include-book "../../generic-modules/GeNoC-nodeset")

;; 1. OctagonNodeSetGenerator
;; -------------------------
(defun naturals (bound)
  ;; define the naturals up to bound
  ;; they are the nodes of the Octagon
  (if (zp bound)
      (list 0)
    (cons bound (naturals (1- bound)))))

(defun OctagonNodeSetGenerator (bound)
  ;; more precisely we choose the bound to be the
  ;; number of nodes in one quarter of the Octagon
  (naturals (+ -1 (* 4 bound))))

(defun OctagonValidParamsp (x)
  ;; the parameter is a positive integer and not zero
  (and (integerp x) (< 0 x)))

;; 2. OctagonNodeSetp
;; -----------------
(defun OctagonValidNodep (x)
  ;; a valid node is simply a natural
  (natp x))

(defun OctagonNodeSetp (x)
  ;; corresponds to the predicate NodeSetp
  (if (endp x)
      t
    (and (OctagonValidNodep (car x))
         (OctagonNodeSetp (cdr x)))))

;; 3. Validation of the nodes of the Octagon
;; -----------------------------------------
;; we need to prove

(defthm octagon-subsets-are-valid
  (implies (and (OctagonNodeSetp x)
                (subsetp y x))
           (OctagonNodeSetp y)))

(defthm OctagonNodeSetp-naturals
  ;; lemma needed for the next theorem
  (implies (and (integerp bound) (< 0 bound))
           (OctagonNodeSetp (naturals bound))))

(defthm check-compliance-octagon-nodeset
  t
  :rule-classes nil
  :hints (("GOAL"
           :use (:functional-instance
                 nodeset-generates-valid-nodes
                 (ValidParamsp OctagonValidParamsp)
                 (NodeSetp OctagonNodeSetp)
                 (Nodesetgenerator OctagonNodeSetGenerator))
           :in-theory (disable nodeset-generates-valid-nodes))))
