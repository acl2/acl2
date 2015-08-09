#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "make-event/defspec"  :dir :system)
(include-book "network")
(include-book "types")#|ACL2s-ToDo-Line|#


(defspec GenericDeparture
  (((depart * * *) => (mv * *)))

  (local (defun depart (ntkst transactions time)
           ;; This function splits the list of transactions into a list of delayed and departing transmissions depending on the current time of the simulation
           ;;
           ;; Arguments:
           ;; - ntkst : a list of ports.
           ;; - transactions : a list of transactions.
           ;; - time : the time of the simulation step.
           (if (endp transactions)
             (mv ntkst nil)
             (let ((transaction (car transactions)))
               (if (and (>= time (timeT transaction))
                        (ntkst-canDepart ntkst transaction))
                 (depart (ntkst-depart ntkst transaction) (cdr transactions) time)
                 (mv-let (newntkst delayed)
                         (depart ntkst (cdr transactions) time)
                         (mv newntkst (cons transaction delayed)))))))))


