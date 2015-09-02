#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "make-event/defspec" :dir :system)
(include-book "types")#|ACL2s-ToDo-Line|#


;;
;; Router
;;

(defspec GenericDatalink
  (((ProcessInputs *) => *)
   ((ProcessOutputs *) => *))


  (local (defun ProcessInputs (ports)
           ports))

  (local (defun ProcessOutputs (ports)
           ports)))



