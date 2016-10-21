(in-package "SAT")

(include-book "assignment-equiv")
(include-book "create-farray")
(include-book "reader")

(defun create-rat-checker (nVars st)
  (declare (xargs :guard (posp nVars)
                  :stobjs (st)))
  (create-farray
   (list 1
         1
         (1+ nVars)
         (+ 2 (* 2 nVars)))
   0 st))


;; create a new farray for rat-checker
(create-rat-checker 1227 st)

;; write number of variables to rat-checker
(fwrite *num-vars* 0 1227 *s* st)


(defttag t)

(remove-untouchable acl2::create-state t)

(defun read-and-parse-local-state (filename)
  ;; This function requires the STATE, so we use the next form
  (with-local-state
   ;; "Powerful" macro that provides access to the state, but
   ;; requires the two events above.
   (mv-let (err num-vars num-clauses formula state)
           (ACL2::read-and-parse filename)
           (mv err num-vars num-clauses formula))))

;; Example Read -- filename can be changed.

;; (defconst *cnf*
;;   (mv-let (err num-vars num-clauses formula)
;;           (read-and-parse-local-state "small-unsat.cnf")
;;           (list err num-vars num-clauses formula)))

(defconst *cnf*
  (mv-let (err num-vars num-clauses formula)
          (read-and-parse-local-state "rbcl_xits_06_UNSAT-10-new.cnf")
          (list err num-vars num-clauses formula)))


(defun read-and-parse-proof-local-state (filename)
  ;; This function requires the STATE, so we use the next form
  (with-local-state
   ;; "Powerful" macro that provides access to the state, but
   ;; requires the two events above.
   (mv-let (err num-clauses proof state)
           (ACL2::read-and-parse-proof filename)
           (mv err num-clauses proof))))


;; (defconst *proof*
;;   (mv-let (err num-clauses proof)
;;           (read-and-parse-proof-local-state "small-unsat.rat")
;;           (list err num-clauses proof)))

(defconst *proof*
  (mv-let (err num-clauses proof)
          (read-and-parse-proof-local-state "rbcl_xits_06_UNSAT-10-combined-lemmas-no-d-head-100.cnf")
          (list err num-clauses proof)))


;; (assignment-stp st)
;; (clause-listp (caddr *proof*))
;; (formulap (cadddr *cnf*))

(defun verify-proof-st-count (clause-list formula count max st)
  (declare (xargs :guard (and (assignment-stp st)
                              (clause-listp clause-list)
                              (clause-list-in-rangep clause-list st)
                              (formulap formula)
                              (formula-in-rangep formula st)
                              (natp count)
                              (posp max))
                  :stobjs (st)))
  (if (atom clause-list)
      (mv t st)
    (mv-let (vc st)
            (verify-clause-st (car clause-list) formula st)
            (if (not vc)
                (mv nil st)
              (if (equal (mod count 100) 0)
                  (b* ((percent (floor (* 100 count) max))
                       (- (cw "~x0% (~x1 / ~x2) ~%" percent count max)))
                      (verify-proof-st-count (cdr clause-list)
                                             (cons (car clause-list) formula)
                                             (1+ count)
                                             max
                                             st))
                (verify-proof-st-count (cdr clause-list)
                                       (cons (car clause-list) formula)
                                       (1+ count)
                                       max
                                       st))))))


(i-am-here)
;; ===================================================================

(profile 'evaluate-literal-st)

(time$
 (verify-proof-st-count (caddr *proof*)
                        (cadddr *cnf*)
                        0
                        (cadr *proof*)
                        st))

(memsum)
;; =
;; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* ...) took 
;; 143.51 seconds realtime, 138.73 seconds runtime
;; (60,880 bytes allocated).
;; (EVALUATE-LITERAL-ST
;;  Calls                                                    8.97E+8
;;  Time of all outermost calls                               124.77
;;  Time per call                                            1.39E-7
;;  From other functions          8.97E+8 calls took 1.25E+2; 100.0%)


;; ===================================================================

(clear-memoize-statistics)
(unmemoize 'evaluate-literal-st)

(profile 'evaluate-literal)

(time$
 (verify-proof (caddr *proof*)
               (cadddr *cnf*)))


(memsum)
;; =
;; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* ...) took 
;; 1126.50 seconds realtime, 1105.15 seconds runtime
;; (1,867,856 bytes allocated).
;; (EVALUATE-LITERAL
;;  Calls                                                                  8.97E+8
;;  Time of all outermost calls                                            1.61E+3
;;  Time per call                                                         1.799E-6
;;  From other functions                        8.97E+8 calls took 1.61E+3; 100.0%)


;; ===================================================================

(clear-memoize-statistics)
(unmemoize 'evaluate-literal)


(profile 'unit-propagation-st)

(time$
 (verify-proof-st-count (caddr *proof*)
                        (cadddr *cnf*)
                        0
                        (cadr *proof*)
                        st))

(memsum)
;; =
;; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* ...) took 
;; 53.13 seconds realtime, 52.99 seconds runtime
;; (60,880 bytes allocated).
;; (UNIT-PROPAGATION-ST
;;  Calls                                                                      836
;;  Time of all outermost calls                                              78.61
;;  Time per call                                                             0.09
;;  From other functions                        8.36E+2 calls took 7.86E+1; 100.0%)


;; ===================================================================

(clear-memoize-statistics)
(unmemoize 'unit-propagation-st)

(profile 'unit-propagation)

(time$
 (verify-proof (caddr *proof*)
               (cadddr *cnf*)))


(memsum)
;; =
;; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* ...) took 
;; 1045.40 seconds realtime, 1036.13 seconds runtime
;; (1,867,856 bytes allocated).
;; (UNIT-PROPAGATION
;;  Calls                                                                      836
;;  Time of all outermost calls                                            1.55E+3
;;  Time per call                                                             1.86
;;  Heap bytes allocated                                           1.73E+6; 100.0%
;;  Heap bytes allocated per call                                          2.07E+3
;;  From other functions                        8.36E+2 calls took 1.55E+3; 100.0%)

