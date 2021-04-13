; A function to check an alist wrt to a list of hyps to be relieved
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "axe-rules")
(local (include-book "kestrel/std/system/all-vars" :dir :system))
(local (in-theory (disable all-vars)))

;; Check whether ALIST is suitable for relieving all of the HYPS, in order.
(defun alist-suitable-for-hypps (alist hyps)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (axe-rule-hyp-listp hyps))
                  :guard-hints (("Goal" :expand (axe-rule-hyp-listp hyps)
                                 :in-theory (enable axe-rule-hypp)))))
  (if (endp hyps)
      t
    (let* ((hyp (first hyps))
           (fn (ffn-symb hyp)))
      (case fn
        (:axe-syntaxp t)
        (:axe-bind-free t) ;todo check the vars declared to be bound
        ;; a hyp marked with :free-vars must have at least 1 free var:
        (:free-vars (let* ((hyp-vars (all-vars hyp))
                           (alist-vars (strip-cars alist))
                           (free-vars (set-difference-eq hyp-vars alist-vars)))
                      (if free-vars t nil)))
        ;; a hyp not marked with :free-vars muct have no free vars:
        (otherwise (let* ((hyp-vars (all-vars hyp))
                          (alist-vars (strip-cars alist))
                          (free-vars (set-difference-eq hyp-vars alist-vars)))
                     (not free-vars)))))))
