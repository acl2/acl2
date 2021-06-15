; Renaming nodes that occur in contexts
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "contexts")

;rename the nodenums in the context according to renaming-array
;fixme there was a bug (a context node got renamed to a constant) which prevented this from returning a contextp - prove that it does, given that the renaming-array is good
(defun fixup-possibly-negated-nodenums (context renaming-array-name renaming-array)
  (declare (xargs :guard (and (array1p renaming-array-name renaming-array)
                              (possibly-negated-nodenumsp-with-bound context (alen1 renaming-array-name renaming-array)))))
  (if (endp context)
      nil
    (let* ((item (first context))
           ;;strips off the not, if present:
           (nodenum (if (consp item)
                        (farg1 item)
                      item))
           (new-nodenum-or-quotep (aref1 renaming-array-name renaming-array nodenum)))
      (if (myquotep new-nodenum-or-quotep) ;just use consp? would need to know something about the values in the renaming array?
          (if (unquote new-nodenum-or-quotep)
              ;;this item is non-nil (true), so drop it from the context :
              (prog2$ (cw "!!! Dropping non-nil constant in context: ~x0 !!!~%" new-nodenum-or-quotep)
                      (fixup-possibly-negated-nodenums (rest context) renaming-array-name renaming-array))
            ;;the item is nil, so the whole context (which is a conjunction, is false):
            (prog2$ (cw "!!! Found nil in context !!!")
                    (false-context)))
        (cons (if (consp item) ;put the not back on, if approriate:
                  `(not ,new-nodenum-or-quotep)
                new-nodenum-or-quotep)
              (fixup-possibly-negated-nodenums (rest context) renaming-array-name renaming-array))))))

;; ;; have to know that nothing gets mapped to a quotep
;; (thm
;;  (implies (and (renaming-arrayp renaming-array-name renaming-array renaming-array-len)
;;                (contextp-with-bound context (alen1 renaming-array-name renaming-array)))
;;           (contextp (fixup-possibly-negated-nodenums context renaming-array-name renaming-array)))
;;  :hints (("Goal" :in-theory (e/d (fixup-possibly-negated-nodenums
;;                                     CONTEXTP-WITH-BOUND
;;                                     CONTEXTP)
;;                                  (natp
;;                                   myquotep)))))

(defund fixup-context (context renaming-array-name renaming-array)
  (declare (xargs :guard (and (array1p renaming-array-name renaming-array)
                              (contextp-with-bound context (alen1 renaming-array-name renaming-array)))
                  :guard-hints (("Goal" :in-theory (enable contextp-with-bound)))))
  (if (false-contextp context) ;may be impossible for some calls of fixup-context?
      context
    (fixup-possibly-negated-nodenums context renaming-array-name renaming-array)))

;; ;; have to know that nothing gets mapped to a quotep, or have to handle that (drop or return a false context, depending on the constant)
;; (thm
;;  (implies (and (renaming-arrayp renaming-array-name renaming-array renaming-array-len)
;;                (contextp-with-bound context (alen1 renaming-array-name renaming-array)))
;;           (contextp (fixup-context context renaming-array-name renaming-array)))
;;  :hints (("Goal" :in-theory (enable FIXUP-CONTEXT))))
