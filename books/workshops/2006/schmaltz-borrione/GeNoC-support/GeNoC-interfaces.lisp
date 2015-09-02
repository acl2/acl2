;; Julien Schmaltz
;; Interface Module of GeNoC
;; June 17th
;; File: GeNoC-interfaces.lisp
(in-package "ACL2")

;;------------------------------------------------------------
;;
;;                     INTERFACES
;;
;;------------------------------------------------------------
(encapsulate

 (
  ;; Any peer has an interface that can send and receive messages
  ;; Function p2psend
  ;; argument: a message msg and [options]
  ;; output: a frame frm
  ((p2psend *) => *)
  ;; Function p2precv
  ;; argument: a frame frm and [options]
  ;; output: a message msg
  ((p2precv *) => *)
  )

 (local (defun p2psend (msg) msg))
 (local (defun p2precv (frm) frm))

 (defthm p2p-Correctness
   ;; the composition of p2precv and p2psend
   ;; is the identity function
   (equal (p2precv (p2psend msg)) msg))

 (defthm p2psend-nil
   ;; if msg is nil then p2psend is nil too
  (not (p2psend nil)))

(defthm p2psend-not-nil
  ;; if msg is not nil then p2psend is not nil too
  (implies msg
           (p2psend msg)))
) ;; end of interfaces
