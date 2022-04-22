; A tool to choose which rules to apply in a proof
;
; Copyright (C) 2022 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

;; ;; Union X into each of the YS.
;; (defun union-equal-with-all (x ys)
;;   (declare (xargs :guard (and (true-listp x)
;;                               (true-list-listp ys))))
;;   (if (endp ys)
;;       nil
;;     (cons (union-equal x (first ys))
;;           (union-equal-with-all x (rest ys)))))

;; ;; Subtract X from each of the YS.
;; (defun set-difference-equal-from-all (x ys)
;;   (declare (xargs :guard (and (true-listp x)
;;                               (true-list-listp ys))))
;;   (if (endp ys)
;;       nil
;;     (cons (set-difference-equal (first ys) x)
;;           (set-difference-equal-from-all x (rest ys)))))

;; TODO: Have this return a list of rule-lists and add the rule-lists arg back.
;; Returns a list of rule names.
;todo: use this in unroll-spec and unroll-spec-basic
(defun choose-rules (rules
                     ;;rule-lists
                     extra-rules remove-rules default-rules)
  (declare (xargs :guard (and (or (eq :auto rules)
                                  (symbol-listp rules))
                              ;; (or (eq :auto rule-lists)
                              ;;     (symbol-list-listp rule-lists))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp default-rules)
                              )))
  (b* ( ;; ((when (and (not (eq :auto rules))
       ;;             (not (eq :auto rule-lists))))
       ;;  (er hard? 'def-simplified-fn ":rules and :rule-lists should not both be given.")
       ;;  (mv (erp-t) nil))
       (rule-list ;; (if (not (eq :auto rule-lists))
        ;;     rule-lists
        (if (eq :auto rules)
            ;;(list
            default-rules
          ;;)
          ;;(list
          rules
          ;;)
          ))
       (rule-list (union-equal ;-with-all
                   extra-rules rule-list))
       (rule-list (set-difference-equal ;-from-all ; note arg order
                   rule-list
                   remove-rules)))
    rule-list))
