

(in-package "ACL2")



;; theory stuff
(set-compile-fns t)
;; compile this so we don't get stack overflows
(defun rules-of-type1 (ruletype list acc)
  (declare (xargs :guard (and (symbolp ruletype)
                              (true-listp acc))))
  (if (atom list)
      (reverse acc)
    (if (and (consp (car list))
             (eq (caar list) ruletype))
        (rules-of-type1 ruletype (cdr list) (cons (car list) acc))
      (rules-of-type1 ruletype (cdr list) acc))))

(set-compile-fns nil)

(defun rules-of-type (ruletype list)
  (declare (xargs :guard (symbolp ruletype)))
  (rules-of-type1 ruletype list nil))






(defun find-equal-in-tree (x tree)
  (declare (xargs :mode :program))
  (or (equal tree x)
      (and (consp tree)
           (or (find-equal-in-tree x (car tree))
               (find-equal-in-tree x (cdr tree))))))


(defun find-in-concl (x clause)
  (declare (xargs :mode :program))
  (find-equal-in-tree x (car (last clause))))


