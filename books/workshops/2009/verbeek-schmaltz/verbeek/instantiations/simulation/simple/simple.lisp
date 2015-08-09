#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")


(include-book "../../../generic-modules/GeNoC-simulation")
(set-state-ok t)
(set-ignore-ok t)

(defun simple-treat-state-entry (coor contents)
  (cons coor contents))

(defun simple-extract-simulation (ntkstate)
  (if (endp ntkstate)
      nil
    (append (simple-treat-state-entry (cadaar ntkstate) (cdadr (car ntkstate)))
            (simple-extract-simulation (cdr ntkstate)))))


(definstance Genericsimulationextraction simple-simulation-compliance
  ;; ACL2 proves automatically that our spidergon nodeset is a valid instance
  ;; of the generic nodeset of GeNoC.
  :functional-substitution
  ((extract-simulation simple-extract-simulation)))

