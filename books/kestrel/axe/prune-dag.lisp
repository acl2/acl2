; Pruning irrelevant IF-branches in a DAG
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This utility tries to resolve IF/MYIF/BOOLIF/BVIF tests in the dag, using STP and the contexts of the nodes.

;; TODO: Flesh this out

;(include-book "prove-with-stp")

;; (defund prune-dag-with-contexts (dag
;;                                  ;; assumptions
;;                                  rules interpreted-fns monitored-rules
;;                                  call-stp
;;                                  state)
;;   (declare (xargs :guard (and (pseudo-dagp dag)
;;                               ;; (pseudo-term-listp assumptions)
;;                               (symbol-listp rules)
;;                               (symbol-listp interpreted-fns)
;;                               (symbol-listp monitored-rules)
;;                               (or (booleanp call-stp)
;;                                   (natp call-stp))
;;                               (ilks-plist-worldp (w state)))
;;                   :stobjs state))
;;   (let ((context-array (make-full-context-array-for-dag dag)))
