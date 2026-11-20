; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "run-helpers")

; idle -> terminated -----------------------------------------------------------

; A node without children runs till it terminates and sends its message if any.
(defruled inv-of-run-idle-to-terminated
  (b* ((pp (omap::lookup p net))
       (parent (omap::lookup 'Parent (wtree-bind pp)))
       (proc (change-proc pp
               :s (apply-k (proc->s pp) (proc->klst pp))
               :ps :terminated
               :klst nil)))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (pid-p pid) (omap::assoc pid net)
      (equal (proc->ps pp) :idle)
      (not (consp (erl-val-cons->lst
                    (omap::lookup 'ChildPids (wtree-bind pp)))))
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (natp (erl-val-integer->val (omap::lookup 'Index (wtree-bind pp))))
      (not (equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
                  p)))
    (inv pid (omap::update p proc net))))
  :enable wtree-fields
  :disable (inv-of-inv-all inv-of-run-to-terminated inv-of-run-non-child
            apply-k-of-idle-with-no-children)
  :expand (inv p net)
  :use ((:instance inv-of-inv-all (pid p))
        (:instance apply-k-of-idle-with-no-children
          (s (proc->s (omap::lookup p net)))
          (klst (proc->klst (omap::lookup p net)))
          (self p)
          (parent (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
          (index (erl-val-integer->val
                   (omap::lookup 'Index (wtree-bind (omap::lookup p net))))))
        (:instance inv-of-run-to-terminated
          (proc (change-proc (omap::lookup p net)
                  :s (apply-k (proc->s (omap::lookup p net))
                              (proc->klst (omap::lookup p net)))
                  :ps :terminated :klst nil)))
        (:instance inv-of-run-non-child
          (proc (change-proc (omap::lookup p net)
                  :s (apply-k (proc->s (omap::lookup p net))
                              (proc->klst (omap::lookup p net)))
                  :ps :terminated :klst nil)))))
