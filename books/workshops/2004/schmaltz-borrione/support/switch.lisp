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

;; File: switch.lisp
;; Definition of the function Switch

(in-package "ACL2")


;;----------------------------------------------
;;
;;             4x4 Non Blocking Switch
;;
;;---------------------------------------------

;; the switch is the following component

;;                 ----------------
;;                |                |
;;     ---------->|    Switch      |--------->
;;    from_node   |                | to_node
;;                |                |
;;     ---------->|                |--------->
;;    from_cwise  |                | to_cwise
;;                |                |
;;    ----------->|                |--------->
;;   from_ccwise  |                | to_ccwise
;;                |                |
;;    ----------->|                |--------->
;;   from_across  |                | to_across
;;                |                |
;;                 ----------------
;;                        /|\
;;                         |
;;                         |
;;                   route_from_to

;; A switch has the following parameters:
;;
;;    - sw_nb: is the number of the switch (= node number)
;;    - from_cwise_nb: is the number of the node that is connected
;;      to the from_cwise port
;;    - from_ccwise_nb: is the number of the node that is connected
;;      to the from_ccwise port
;;    _ from_across_nb: is the number of the node that is connected
;;      to the from_across port
;;    - to_cwise_nb: is the number of the node that is connected
;;      to the to_cwise port
;;    - to_ccwise_nb: is the number of the node that is connected
;;      to the to_ccwise port
;;    - to_across_nb: is the number of the node that is connected
;;      to the to_across port
;;    - route_from_to is a list containing two numbers: the first one
;;      is the input where there is a message, and the second element is
;;      the output port to which the message should be send

;; The switch put the message in the output list corresponding to
;; the route_from_to list.

;; the output list is (to_node to_cwise to_ccwise to_across)
;; from_across_nb and to_across_nb are not used

(defun switch (from_node from_cwise from_ccwise from_across
               sw_nb from_cwise_nb from_ccwise_nb from_across_nb
               to_cwise_nb to_ccwise_nb  to_across_nb
               origin_target)
  (let ((origin (car origin_target))
        (target (cadr origin_target)))
    (cond ((equal target sw_nb)
           ;; the target is the current node
           (cond ((equal origin sw_nb)
                  ;; the origin is the current node
                  (mv from_node nil nil nil))
                 ((equal origin from_cwise_nb)
                  ;; the origin is the previous clockwise node
                  (mv from_cwise nil nil nil))
                 ((equal origin from_ccwise_nb)
                  ;; the origin is the previous counterclockwise node
                  (mv from_ccwise nil nil nil))
                 ((equal origin from_across_nb)
                  ;; the origin is the previous across node
                  (mv from_across nil nil nil))
                 (t
                  ;; the origin is not valid
                  (mv nil nil nil nil))))
          ((equal target to_cwise_nb)
           ;; the target is the next clockwise node
           (cond ((equal origin sw_nb)
                  ;; the origin is the current node
                  (mv nil from_node nil nil))
                 ((equal origin from_cwise_nb)
                  ;; the origin is the previous clockwise node
                  (mv nil from_cwise nil nil))
                 ((equal origin from_ccwise_nb)
                  ;; the origin is the previous counterclockwise node
                  (mv nil from_ccwise nil nil))
                 ((equal origin from_across_nb)
                  ;; the origin is the previous across node
                  (mv nil from_across nil nil))
                 (t
                  ;; the origin is not valid
                  (mv nil nil nil nil))))
          ((equal target to_ccwise_nb)
           ;; the target is the next counterclockwise node
           (cond ((equal origin sw_nb)
                  ;; the origin is the current node
                  (mv nil nil from_node nil))
                 ((equal origin from_cwise_nb)
                  ;; the origin is the previous clockwise node
                  (mv nil nil from_cwise nil))
                 ((equal origin from_ccwise_nb)
                  ;; the origin is the previous counterclockwise node
                  (mv nil nil from_ccwise nil))
                 ((equal origin from_across_nb)
                  ;; the origin is the previous across node
                  (mv nil nil from_across nil))
                 (t
                  ;; the origin is not valid
                  (mv nil nil nil nil))))
          ((equal target to_across_nb)
           ;; the target is the next across node
           (cond ((equal origin sw_nb)
                  ;; the origin is the current node
                  (mv nil nil nil from_node))
                 ((equal origin from_cwise_nb)
                  ;; the origin is the previous clockwise node
                  (mv nil nil nil from_cwise))
                 ((equal origin from_ccwise_nb)
                  ;; the origin is the previous counterclockwise node
                  (mv nil nil nil from_ccwise))
                 ((equal origin from_across_nb)
                  ;; the origin is the previous across node
                  (mv nil nil nil from_across))
                 (t
                  ;; the origin is not valid
                  (mv nil nil nil nil))))
          (t
           ;; the target is not a valid node
           (mv nil nil nil nil))))
)
