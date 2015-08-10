#|$ACL2s-Preamble$;
;;-------------------------------------------------------------------------
;;-------------------------------------------------------------------------
;;
;;
;; Functional Specification and Validation of the Octagon Network on
;;              Chip using the ACL2 Theorem Prover
;;
;;
;;                          Proof Script
;;
;;
;;                         Julien Schmaltz
;;                     Joseph Fourier University
;;               46, av. Felix Viallet 38031 Grenoble Cedex
;;                             FRANCE
;;                      Julien.Schmaltz@imag.fr
;;
;;-------------------------------------------------------------------------
;;-------------------------------------------------------------------------
;; we reuse the book developed for the study of the
;; Octagon and presented at the ACL2 workshop 2004

;; File: intersect.lisp
;; Contains definitions and lemmas about the intersection of routes
;; Link this concept to other functions, e.g. no-duplicatesp
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")
(include-book "data-structures/list-defuns" :dir :system)
(include-book "data-structures/list-defthms" :dir :system)


;;-------------------------------------------------------------
;;                      EMPTY INTERSECTION
;;------------------------------------------------------------
(defun no_intersectp (l1 l2)
  ;; returns t if every element of l1 is not in l2
  ;; i.e. if l1 and l2 have an empty intersection
  (if (endp l1)
      t
    (and (not (member (car l1) l2))
         (no_intersectp (cdr l1) l2))))#|ACL2s-ToDo-Line|#


;; we prove some properties of this predicate
(defthm commutativity_no_intersectp
  ;; it is commutative
  (equal (no_intersectp l1 l2)
         (no_intersectp l2 l1)))

(defthm no_intersectp_append
  ;; we link this concept with APPEND
  (equal (no_intersectp l1 (append l2 l3))
         (and (no_intersectp l1 l2)
              (no_intersectp l1 l3))))

(defthm no_intersectp_append-1
  ;; it should be better to have some kind of normalization
  ;; but the proof of rules to go to the normal form is
  ;; not automatic in ACL2, but this rule is automatic.
  (equal (no_intersectp (append l1 l2) l3)
         (and (no_intersectp l1 l3)
              (no_intersectp l2 l3))))

#|

;;---------------------------------------------------------
;;                NODE COLLECTION
;;--------------------------------------------------------
  (i-am-here)
(defun grab_nodes (travel_list)
  ;; collects all the nodes of all the routes of the travel list
  ;; Pb: in the new version of GeNoC there are several routes
  ;; not just one :-)
  (if (endp travel_list)
      nil
    (append (RoutesV (car travel_list))
            (grab_nodes (cdr travel_list)))))

(defthm no-duplicatesp-append
  (implies (and (no-duplicatesp l1)
                (no-duplicatesp l2)
                (no_intersectp l1 l2))
           (no-duplicatesp (append l1 l2))))

(defthm no-duplicatesp-append-nil
  (implies (no-duplicatesp l)
           (no-duplicatesp (append l nil))))

(defun all_no_intersectp (route travel_list)
  ;; returns t if route does not intersect with all the routes
  ;; of the travel list
  (if (endp travel_list)
      t
    (and (no_intersectp route (cdr (car travel_list)))
         (all_no_intersectp route (cdr travel_list)))))

(defthm all_no_intersectp_append
  ;; we link this concept with append
  (equal (all_no_intersectp l1 (append l2 l3))
         (and (all_no_intersectp l1 l2)
              (all_no_intersectp l1 l3))))


(defthm all_no_intersectp_grab_nodes
  ;; we also link it with grab_nodes
  (equal (all_no_intersectp r tl)
         (no_intersectp r (grab_nodes tl))))

(defun all_no_intersectp_routep (travel_list)
  ;; returns t if every route of the travel list has no intersection with
  ;; every other route
  (if (endp (cdr travel_list))
      t
    (and (all_no_intersectp (cdr (car travel_list))
                            (cdr travel_list))
         (all_no_intersectp_routep (cdr travel_list)))))
|#

#|

(defthm all_no_duplicates_and_all_no_intersectp_route_=>_no_dupli_grab_nodes
  ;; we prove that this concept and if every route has no duplicate,
  ;; then grab_nodes of this travel list has no duplicate
  (implies (and (all_no_intersectp_routep l)
                (all_no_duplicatesp l))
           (no-duplicatesp (grab_nodes l)))
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;   :hints (("GOAL"
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)))
  )
|#

