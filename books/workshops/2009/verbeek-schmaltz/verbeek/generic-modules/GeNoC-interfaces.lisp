#|$ACL2s-Preamble$;
;; Julien Schmaltz
;; Interface Module of GeNoC
;; June 17th
;; File: GeNoC-interfaces.lisp
;;Amr helmy
;;31st october 2007

(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")
(include-book "make-event/defspec" :dir :system)

;;------------------------------------------------------------
;;
;;                     INTERFACES
;;
;;------------------------------------------------------------

(defspec GenericInterfaces

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

  (defthm p2precv-nil
    ;; if frm is nil then p2precv is nil too
    (not (p2precv nil)))

  (defthm p2precv-not-nil
    ;; if frm is not nil then p2precv is not nil too
    (implies frm
             (p2precv frm)))

  ) ;; end of interfaces