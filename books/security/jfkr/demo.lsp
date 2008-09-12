(ld "package.lsp")

(in-package "JFKR")

(include-book "jfkr")

(defconst *1-step-run-ex*
  (mv-let (x y z)
          (run-1-step-honest nil 
                             *initiator-constants* 
                             *responder-constants* 
                             *public-constants* 
                             nil
                             nil)
          (list x y z)))
          
*1-step-run-ex*


(defconst *2-step-run-ex*
  (mv-let (x y z)
          (run-2-steps-honest nil 
                              *initiator-constants* 
                              *responder-constants* 
                              *public-constants* 
                              nil
                              nil)
          (list x y z))) 

*2-step-run-ex*


(defconst *3-step-run-ex*
  (mv-let (x y z)
          (run-3-steps-honest nil 
                              *initiator-constants* 
                              *responder-constants* 
                              *public-constants* 
                              nil
                              nil)
          (list x y z)))

*3-step-run-ex*


(defconst *4-step-run-ex*
  (mv-let (x y z)
          (run-4-steps-honest nil 
                              *initiator-constants* 
                              *responder-constants* 
                              *public-constants* 
                              nil
                              nil)
          (list x y z)))

*4-step-run-ex*


(defconst *5-step-run-ex* 
  (mv-let (x y z)
          (run-5-steps-honest nil 
                              *initiator-constants* 
                              *responder-constants* 
                              *public-constants* 
                              nil
                              nil)
          (list x y z)))

*5-step-run-ex*


(thm
 (mv-let (network-s initiator-s responder-s)
         *5-step-run-ex*
         (declare (ignore network-s))

         (and
          ;; responder stores the correct partner
          (equal (id *initiator-constants*)
                 (id-i responder-s))

          ;; Initiator stores the correct partner
          (equal (id *responder-constants*)
                 (id-r initiator-s))
              
          (equal (session-key initiator-s)
                 (session-key responder-s))))))
