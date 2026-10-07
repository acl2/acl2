; Helper for new-57.  Certifies legitimately; its .cert carries a
; :type-prescription cert-data entry whose :corollary mentions MYCONSP, a
; function introduced only by a LOCAL event.
(in-package "ACL2")
(local (defun myconsp (x) (consp x)))
(local
 (defthm myconsp-tsi
   (equal (if (myconsp x) (consp x) nil) (consp x))
   :rule-classes ((:type-set-inverter))))
(defun fc (x) (cons x x))
