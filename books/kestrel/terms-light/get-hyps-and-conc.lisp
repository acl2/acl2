; Getting the hyps and conclusion of a translated term
;
; Copyright (C) 2018-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "get-conjuncts")

;; Returns (mv hyps conc).
(defun get-hyps-and-conc (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (eq 'implies (ffn-symb term)))
      (mv-let (hyps1 conc)
        (get-hyps-and-conc (fargn term 2))
        ;; todo: call union-equal here?:
        (mv (append (get-conjuncts (fargn term 1))
                    hyps1)
            conc))
    ;; todo: handle lambdas
    (mv nil term)))
