; Equivalence relations used by Axe
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We may some day support more equivalence relation, but for now we only
;; support 'equal and 'iff.
(defund equivp (x)
  (declare (xargs :guard t))
  (member-equal x '(equal iff)))

(defthm equivp-forward-to-symbolp
  (implies (equivp x)
           (symbolp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable equivp))))

(defund equiv-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (equivp (first x))
         (equiv-listp (rest x)))))

(defthm equivp-of-car-when-equiv-listp
  (implies (and (equiv-listp x)
                (consp x))
           (equivp (car x)))
  :hints (("Goal" :in-theory (enable equiv-listp))))

(defthm equiv-listp-of-cdr
  (implies (equiv-listp equivs)
           (equiv-listp (cdr equivs)))
  :hints (("Goal" :in-theory (enable equiv-listp))))
