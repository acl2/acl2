; Getting the hyps and conclusion of a translated term
;
; Copyright (C) 2018-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "get-conjuncts")
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(in-theory (disable mv-nth))

;; Returns (mv hyps conc).
(defund get-hyps-and-conc (term)
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

(defthm pseudo-term-listp-of-mv-nth-0-of-get-hyps-and-conc
  (implies (pseudo-termp term)
           (pseudo-term-listp (mv-nth 0 (get-hyps-and-conc term))))
  :hints (("Goal" :in-theory (enable get-hyps-and-conc))))

(defthm pseudo-termp-of-mv-nth-1-of-get-hyps-and-conc
  (implies (pseudo-termp term)
           (pseudo-termp (mv-nth 1 (get-hyps-and-conc term))))
  :hints (("Goal" :in-theory (enable get-hyps-and-conc))))
