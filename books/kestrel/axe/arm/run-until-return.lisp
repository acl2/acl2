; Running until we return from a function or hit a stop PC
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "A")

;; This machinery is useful for symbolic execution.
;; See also run-until-return-with-tracing.lisp.

(include-book "portcullis")
(include-book "run-until-return-common")
(include-book "misc/defpun" :dir :system)
;(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/lists-light/memberp" :dir :system)
(local (include-book "kestrel/alists-light/acons" :dir :system))

(local (in-theory (disable alistp)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider stopping if the error field of the state is set.
;; It would be nice to support the :stobjs arm below, but it is
;; not very important, because a defpun is already non-executable.
(defpun run-until-return-aux (call-stack-height arm)
  ;; (declare (xargs :stobjs arm))
  (if (< call-stack-height 0)
      arm ; stop since we've returned from the function being lifted
    ;; Step the state and also update our tracked version of the call-stack-height:
    (run-until-return-aux (update-call-stack-height call-stack-height arm) (step arm))))

;; TODO: Can we prove this?
;; (thm
;;   (implies (armp arm)
;;            (armp (run-until-return-aux call-stack-height arm))))

;; This is a non-Axe rule
(defthm run-until-return-aux-base
  (implies (and (syntaxp (not (and (consp arm) (eq 'if (ffn-symb arm)))))
                (< call-stack-height 0))
           (equal (run-until-return-aux call-stack-height arm)
                  arm)))

;; This is a non-Axe rule
(defthm run-until-return-aux-opener
  (implies (and (syntaxp (not (and (consp arm) (eq 'if (ffn-symb arm)))))
                (not (< call-stack-height 0)))
           (equal (run-until-return-aux call-stack-height arm)
                  ;; todo: decoding is done here twice (in update-call-stack-height and step):
                  (run-until-return-aux (update-call-stack-height call-stack-height arm) (step arm)))))

;; todo: add "smart" if handling, like we do elsewhere
(defthm run-until-return-aux-of-if-arg2
  (equal (run-until-return-aux call-stack-height (if test arma armb))
         (if test
             (run-until-return-aux call-stack-height arma)
           (run-until-return-aux call-stack-height armb))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Run until we return from the current function.
(defund run-until-return (arm)
  ;; (declare (xargs :stobjs arm))
  (run-until-return-aux
   0 ; initial call-stack-height
   arm))

(defund run-subroutine (arm)
  ;; (declare (xargs :stobjs arm))  ;; (declare (xargs :guard )) ; todo: need a property of the defpun
  ;; OLD: We start by stepping once.  This increases the stack height.  Then we run
  ;; until the stack height decreases again.  Finally, we step one more time to
  ;; do the RET.
  ;;(step32 (run-until-return (step32 arm)))
  (run-until-return arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Should we stop if the error field of the state is set?  Probably not, since the
;; run did not in fact finish but we may be able to prove things about the error state.
;; It would be nice to support the :stobjs arm below, but it is
;; not very important, because a defpun is already non-executable.
(defpun run-until-return-or-reach-pc-aux (call-stack-height stop-pcs arm)
  ;; (declare (xargs :stobjs arm))
  (if (or (< call-stack-height 0)
          (memberp (reg *pc* arm) ; (pc arm)
                   stop-pcs))
      arm ; stop since we've returned from the function being lifted or reached a stop-pc
    ;; Step the state and also update our tracked version of the call-stack-height:
    (run-until-return-or-reach-pc-aux (update-call-stack-height call-stack-height arm) stop-pcs (step arm))))

;; TODO: Can we prove this?
;; (thm
;;   (implies (armp arm)
;;            (armp (run-until-return-or-reach-pc-aux call-stack-height stop-pcs arm))))

;; This is a non-Axe rule
(defthm run-until-return-or-reach-pc-aux-base
  (implies (and (syntaxp (not (and (consp arm) (eq 'if (ffn-symb arm)))))
                (or (< call-stack-height 0)
                    (memberp (reg *pc* arm) ; (pc arm)
                             stop-pcs)))
           (equal (run-until-return-or-reach-pc-aux call-stack-height stop-pcs arm)
                  arm)))

;; This is a non-Axe rule
(defthm run-until-return-or-reach-pc-aux-opener
  (implies (and (syntaxp (not (and (consp arm) (eq 'if (ffn-symb arm)))))
                (not (or (< call-stack-height 0)
                         (memberp (reg *pc* arm) ; (pc arm)
                                  stop-pcs))))
           (equal (run-until-return-or-reach-pc-aux call-stack-height stop-pcs arm)
                  ;; todo: decoding is done here twice (in update-call-stack-height and step):
                  (run-until-return-or-reach-pc-aux (update-call-stack-height call-stack-height arm) stop-pcs (step arm)))))

;; todo: add "smart" if handling, like we do elsewhere
(defthm run-until-return-or-reach-pc-aux-of-if-arg2
  (equal (run-until-return-or-reach-pc-aux call-stack-height stop-pcs (if test arma armb))
         (if test
             (run-until-return-or-reach-pc-aux call-stack-height stop-pcs arma)
           (run-until-return-or-reach-pc-aux call-stack-height stop-pcs armb))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Run until we return from the current function or hit one of the STOP-PCS.
(defund run-until-return-or-reach-pc (stop-pcs arm)
  ;; (declare (xargs :stobjs arm))
  (run-until-return-or-reach-pc-aux
   0 ; initial call-stack-height
   stop-pcs
   arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpun run-until-reach-pc-aux (stop-pcs arm)
  ;; (declare (xargs :stobjs arm))
  (if (memberp (reg *pc* arm) ; (pc arm)
               stop-pcs)
      arm ; stop since we've reached a stop-pc
    ;; Step the state:
    (run-until-reach-pc-aux stop-pcs (step arm))))

;; This is a non-Axe rule
(defthm run-until-reach-pc-aux-base
  (implies (and (syntaxp (not (and (consp arm) (eq 'if (ffn-symb arm)))))
                (memberp (reg *pc* arm) ; (pc arm)
                         stop-pcs))
           (equal (run-until-reach-pc-aux stop-pcs arm)
                  arm)))

;; This is a non-Axe rule
(defthm run-until-reach-pc-aux-opener
  (implies (and (syntaxp (not (and (consp arm) (eq 'if (ffn-symb arm)))))
                (not (memberp (reg *pc* arm) ; (pc arm)
                                  stop-pcs)))
           (equal (run-until-reach-pc-aux stop-pcs arm)
                  (run-until-reach-pc-aux stop-pcs (step arm)))))

;; todo: add "smart" if handling, like we do elsewhere
(defthm run-until-reach-pc-aux-of-if-arg2
  (equal (run-until-reach-pc-aux stop-pcs (if test arma armb))
         (if test
             (run-until-reach-pc-aux stop-pcs arma)
           (run-until-reach-pc-aux stop-pcs armb))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Run until we hit one of the STOP-PCS.
(defund run-until-reach-pc (stop-pcs arm)
  ;; (declare (xargs :stobjs arm))
  (run-until-reach-pc-aux stop-pcs arm))
