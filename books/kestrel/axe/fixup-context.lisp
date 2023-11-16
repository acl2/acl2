; Renaming nodes that occur in contexts
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "contexts")
(include-book "renaming-array")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

(local
 (defthm natp-of-+-of-1
   (implies (integerp x)
            (equal (natp (+ 1 x))
                   (<= -1 x)))))

;rename the nodenums in the context according to renaming-array
;fixme there was a bug (a context node got renamed to a constant) which prevented this from returning a contextp - prove that it does, given that the renaming-array is good
;; TODO: Specialize to the case where the renaming-array never maps anything to a constant (may always be the case when this is called).
(defun fixup-possibly-negated-nodenums (context renaming-array-name renaming-array)
  (declare (xargs :guard (and (array1p renaming-array-name renaming-array) ; todo: strengthen
                              (bounded-possibly-negated-nodenumsp context (alen1 renaming-array-name renaming-array)))
                  :guard-hints (("Goal" :in-theory (enable bounded-possibly-negated-nodenumsp
                                                           bounded-possibly-negated-nodenump)))))
  (if (endp context)
      nil
    (let* ((item (first context))
           (negatedp (consp item))
           ;;strips off the not, if present:
           (nodenum (if negatedp
                        (farg1 item)
                      item))
           (new-nodenum-or-quotep (aref1 renaming-array-name renaming-array nodenum)))
      (if (myquotep new-nodenum-or-quotep) ;todo: just use consp? would need to know something about the values in the renaming array?
          ;; TODO: This case may not be possible in practice
          (let ((item-val (let ((unquoted-val (unquote new-nodenum-or-quotep)))
                            (if negatedp
                                (not unquoted-val)
                              unquoted-val))))
            (if item-val
                ;; this item is non-nil (true), so drop it from the context :
                (progn$ (cw "!!! Dropping non-nil constant in context: ~x0 !!!~%" new-nodenum-or-quotep)
                        (fixup-possibly-negated-nodenums (rest context) renaming-array-name renaming-array))
              ;;the item is nil, so the whole context (which is a conjunction), is false:
              (progn$ (cw "!!! Found nil in context !!!")
                      (false-context))))
        ;; The nodenum was renamed to a new nodenum:
        (let ((rest-result (fixup-possibly-negated-nodenums (rest context) renaming-array-name renaming-array)))
          (if (false-contextp rest-result)
              rest-result
            (cons (if negatedp ;put the not back on, if appropriate:
                      `(not ,new-nodenum-or-quotep)
                    new-nodenum-or-quotep)
                  rest-result)))))))

;; ;; have to know that nothing gets mapped to a quotep
(defthm contextp-of-fixup-possibly-negated-nodenums
  (implies (and (renaming-arrayp renaming-array-name renaming-array (+ 1 (max-nodenum-in-possibly-negated-nodenums context))) ; todo: too strong?  it only renames the nodes that appear in the context (and their supporters)?
                (bounded-possibly-negated-nodenumsp context (alen1 renaming-array-name renaming-array)))
           (contextp (fixup-possibly-negated-nodenums context renaming-array-name renaming-array)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (fixup-possibly-negated-nodenums
                            bounded-possibly-negated-nodenumsp
                            bounded-possibly-negated-nodenump
                            contextp
                            max-nodenum-in-possibly-negated-nodenums
                            possibly-negated-nodenump
                            acl2-numberp-when-integerp
                            max-nodenum-in-possibly-negated-nodenums-aux)
                           (natp
                            myquotep)))))

(defund fixup-non-false-context (context renaming-array-name renaming-array)
  (declare (xargs :guard (and (not (false-contextp context))
                              (array1p renaming-array-name renaming-array)
                              (bounded-contextp context (alen1 renaming-array-name renaming-array)))
                  :guard-hints (("Goal" :in-theory (enable bounded-contextp)))))
  (fixup-possibly-negated-nodenums context renaming-array-name renaming-array))

(defthm contextp-of-fixup-fixup-non-false-context
  (implies (and (contextp context)
                (not (false-contextp context))
                (renaming-arrayp renaming-array-name renaming-array (+ 1 (max-nodenum-in-possibly-negated-nodenums context)))
                (bounded-contextp context (alen1 renaming-array-name renaming-array)))
           (contextp (fixup-non-false-context context renaming-array-name renaming-array)))
  :hints (("Goal" :in-theory (enable fixup-non-false-context contextp bounded-contextp fixup-possibly-negated-nodenums))))

;; This would justify an optimization to the equivalence-checker, if something like this were true.
;; (thm
;;  (implies (and (contextp context)
;;                (not (false-contextp context))
;;                (array1p renaming-array-name renaming-array)
;;                (bounded-contextp context (alen1 renaming-array-name renaming-array)))
;;           (not (false-contextp (fixup-non-false-context context renaming-array-name renaming-array))))
;;  :hints (("Goal" :in-theory (enable fixup-non-false-context contextp fixup-possibly-negated-nodenums))))

;deprecate?
;; (defund fixup-context (context renaming-array-name renaming-array)
;;   (declare (xargs :guard (and (array1p renaming-array-name renaming-array)
;;                               (bounded-contextp context (alen1 renaming-array-name renaming-array)))
;;                   :guard-hints (("Goal" :in-theory (enable bounded-contextp)))))
;;   (if (false-contextp context) ;may be impossible for some calls of fixup-context?
;;       context
;;     (fixup-non-false-context context renaming-array-name renaming-array)))

;; ;; have to know that nothing gets mapped to a quotep, or have to handle that (drop or return a false context, depending on the constant)
;; (thm
;;  (implies (and (renaming-arrayp renaming-array-name renaming-array renaming-array-len)
;;                (bounded-contextp context (alen1 renaming-array-name renaming-array)))
;;           (contextp (fixup-context context renaming-array-name renaming-array)))
;;  :hints (("Goal" :in-theory (enable fixup-context))))
