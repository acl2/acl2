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
(create-rat-checker 4641 st)

;; write number of variables to rat-checker
(fwrite *num-vars* 0 4641 *s* st)


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
          (read-and-parse-local-state "R_4_4_18.cnf")
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
          (read-and-parse-proof-local-state "R_4_4_18.rat")
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
              (if (equal (mod count 1000) 0)
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


(time$
 (verify-proof-st-count (caddr *proof*)
                        (cadddr *cnf*)
                        0
                        (cadr *proof*)
                        st))
