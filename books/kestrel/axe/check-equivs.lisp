; A tool to check an equivalence table
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "equivs")

(include-book "kestrel/utilities/make-var-names" :dir :system)
(include-book "kestrel/utilities/substitution" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;example justification:
;; (thm
;;  (implies (iff x1 x1-alt)
;;           (equal (iff x1 x2)
;;                  (iff x1-alt x2))))

;; Returns a list of thms.
(defund equiv-alist-thms-aux-aux (args arg-equivs fn all-args outer-equiv)
  (declare (xargs :guard (and (symbol-listp args)
                              (equiv-listp arg-equivs)
                              (equal (len args) (len arg-equivs))
                              (symbol-listp all-args)
                              (equivp outer-equiv))))
  (if (endp args)
      nil
    (let* ((arg (first args))
           (equiv-for-arg (first arg-equivs))
           (equiv-arg (pack$ arg '-equiv))
           (equiv-args (my-sublis-var-lst (acons arg equiv-arg nil)
                                          all-args)))
      (cons `(thm
              (implies (,equiv-for-arg ,arg ,equiv-arg)
                       (,outer-equiv (,fn ,@all-args)
                                     (,fn ,@equiv-args))))
            (equiv-alist-thms-aux-aux (rest args) (rest arg-equivs) fn all-args outer-equiv)))))

;; Returns a list of thms.
(defund equiv-alist-thms-aux (outer-equiv fn-to-arg-equivs-alist)
  (declare (xargs :guard (and (equivp outer-equiv)
                              (symbol-to-equivs-alistp fn-to-arg-equivs-alist))
                  :guard-hints (("Goal" :in-theory (enable SYMBOL-TO-EQUIVS-ALISTP)))
                  ))
  (if (endp fn-to-arg-equivs-alist)
      nil
    (let* ((pair (first fn-to-arg-equivs-alist))
           (fn (car pair))
           (arg-equivs (cdr pair))
           (arity (len arg-equivs))
           (args (make-var-names arity 'x)))
      (append (equiv-alist-thms-aux-aux args arg-equivs fn args outer-equiv)
              (equiv-alist-thms-aux outer-equiv (rest fn-to-arg-equivs-alist))))))

;; Returns a list of thms.
(defund equiv-alist-thms (equiv-alist)
  (declare (xargs :guard (equiv-alistp equiv-alist)
                  :guard-hints (("Goal" :in-theory (enable equiv-alistp
                                                           ALL-SYMBOL-TO-EQUIVS-ALISTP
                                                           EQUIV-LISTP)))))
  (if (endp equiv-alist)
      nil
    (append (equiv-alist-thms-aux (car (first equiv-alist)) (cdr (first equiv-alist)))
            (equiv-alist-thms (rest equiv-alist)))))

(defun check-equiv-alist-fn (equiv-alist)
  (declare (xargs :guard (equiv-alistp equiv-alist)))
  `(progn ,@(equiv-alist-thms equiv-alist)))

(defmacro check-equiv-alist (equiv-alist)
  `(make-event (check-equiv-alist-fn ,equiv-alist)))
