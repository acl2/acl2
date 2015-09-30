(in-package "ACL2S")

(defdata pc nat)
(defdata reg nat) 
(defdata address nat) 
(defdata data integer) 
(defdata register-file (oneof nil (acons address data register-file)))
; no jump, branch and indirect store (consider only a basic block)
(defdata op-code (enum '(add sub mul)))
(defdata vec-op-code (enum '(vadd vsub vmul)))

(defdata inst (record (op . op-code)
                      (rc . reg)
                      (ra . reg)
                      (rb . reg)))

  
(defdata imem (listof inst))

(defdata isa-state (record (prc . pc)
                           (regs . register-file)
                           (inmem . imem)))


(defdata vecreg (cons reg reg))

(defdata vecinst (record (op . vec-op-code)
                         (rc . vecreg)
                         (ra . vecreg)
                         (rb . vecreg)))

(defdata mix-inst (oneof inst vecinst))

(defdata vecimem (listof mix-inst))

(defdata vecisa-state (record (prc . pc)
                              (regs . register-file)
                              (vecinmem . vecimem)))

