#|$ACL2s-Preamble$;
;;Amr HELMY
;; 19th march 2008
;;GeNoC-priority.lisp
;; this file contains the proof obligations of the generic priority function
;; the priority is implemented as a sorting function that classes the
;; travels in order of their priority folowing an order



(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "own-perm")
(include-book "GeNoC-types")
(include-book "GeNoC-misc")

(defspec GenericPriority
  (((prioritysorting * *)=> * ))


  (local
   (defun prioritysorting (trlst order)
     (declare (ignore order))
     trlst))

  ;; the output of the function is just a permutation of the input
  (defthm isperm-prioritysorting
    (implies (trlstp trlst nodeset)
             (is-perm (v-ids (prioritysorting trlst order))
                      (v-ids trlst))))

  ;;the type of the output is a trlstp
  (defthm trlstp-prioritysorting
    (implies (trlstp trlst nodeset)
             (trlstp (prioritysorting trlst order) nodeset)))

  ;; the output is a subsetp of the input (to be sure no travels are created)
  (defthm subsetp-prioritysorting-trlst
    (implies (trlstp trlst nodeset)
             (subsetp (prioritysorting trlst order) trlst)))

  ;; the identifiers of the output is a subset of those of the input
  ;; remove and put a general relation between is-perm and subsetp
  (defthm subsetp-v-ids-priority-trlst
    (implies (trlstp trlst nodeset)
             (subsetp (v-ids (prioritysorting trlst order))
                      (v-ids trlst))))
  ;; the result of the function is a true-listp
  ;;remove next theorem
  (defthm true-listp-priority-sorting
    (implies (trlstp trlst nodeset)
             (true-listp (prioritysorting trlst order))))

  ;; the origins of the output is a subset of those of the input
  (defthm subsetp-orgs-prioritysort
    (implies (trlstp trlst nodeset)
             (subsetp (v-orgs (prioritysorting trlst order))
                      (v-orgs trlst))))

  ;; the frames of the output is a subset of those of the input
  (defthm subsetp-frms-prioritysort
    (implies (trlstp trlst nodeset)
             (subsetp (v-frms (prioritysorting trlst order))
                      (v-frms trlst))))

  ;; the destinations of the output after transformation to missives
  ;; is a subset of those of the input after the same transformation
  (defthm subsetp-prioritysort_mdests
    (implies (trlstp trlst nodeset)
             (subsetp (m-dests (tomissives
                                (totmissives (prioritysorting trlst order)) ))
                      (m-dests (tomissives(totmissives trlst))))))


  );;END OF encapsulation
