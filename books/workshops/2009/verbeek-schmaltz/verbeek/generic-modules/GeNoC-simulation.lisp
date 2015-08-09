#|$ACL2s-Preamble$;
;;Amr helmy
;;4th august 2008
;; GeNoC-simulation.lisp
;; this file contains the definition of the generic simulation extraction
;; functions, they only are used to extract the simulation and have no formal value.
(begin-book );$ACL2s-Preamble$|#


(in-package "ACL2")
(include-book "make-event/defspec" :dir :system)




(defspec Genericsimulationextraction
(((extract-simulation *) => *))
;;the next two function should be modified given the form of the network state
(local (defun treat-state-entry (coor contents)
  (if (endp contents)
      nil
    (cons (list coor (caar contents) (cadar contents))
          (treat-state-entry coor (cdr contents))))))

(local
(defun extract-simulation (ntkstate)
  (if (endp ntkstate)
      nil
    (append (treat-state-entry (cadaar ntkstate) (cdadr
                                                  (car
                                                   ntkstate)))
            (extract-simulation (cdr ntkstate))))))

)#|ACL2s-ToDo-Line|#
