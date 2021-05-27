; Utilities to make variable names
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: compare to new-var-names

(include-book "kestrel/utilities/pack" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))

;;;
;;; make-var-names-aux
;;;

;; Makes a list of symbols each of which is BASE-SYMBOL with a numeric suffix
;; added to it.  The result contains symbols from BASE-SYMBOL with a suffix of
;; STARTNUM through BASE-SYMBOL with a suffix of ENDNUM.
(defund make-var-names-aux (base-symbol startnum endnum)
  (declare (xargs :guard (symbolp base-symbol)
                  :measure (nfix (+ 1 (- endnum startnum)))
                  ))
  (if (or (not (natp startnum))
          (not (natp endnum))
          (< endnum startnum))
      nil
    (cons (pack-in-package-of-symbol base-symbol base-symbol (nat-to-string startnum))
          (make-var-names-aux base-symbol (+ 1 startnum) endnum))))

(defthm symbol-listp-of-make-var-names-aux
  (symbol-listp (make-var-names-aux base-symbol startnum endnum))
  :hints (("Goal" :in-theory (enable make-var-names-aux))))

;; because they are symbols
(defthm pseudo-term-listp-of-make-var-names-aux
  (pseudo-term-listp (make-var-names-aux base-symbol startnum endnum))
  :hints (("Goal" :in-theory (enable make-var-names-aux))))

(defthm len-of-make-var-names-aux
  (implies (and (natp startnum)
                (integerp endnum)
                (<= startnum (+ 1 endnum)))
           (equal (len (make-var-names-aux base-symbol startnum endnum))
                  (+ 1 (- endnum startnum))))
  :hints (("Goal" :in-theory (enable make-var-names-aux))))

(defthm consp-of-make-var-names-aux
  (implies (and (natp startnum)
                (integerp endnum)
                (<= startnum (+ 1 endnum)))
           (equal (consp (make-var-names-aux base-symbol startnum endnum))
                  (<= startnum endnum)))
  :hints (("Goal" :in-theory (enable make-var-names-aux))))

;; ;was called make-var-names
;; (defund make-var-names-x (namecount)
;;   (declare (xargs ;:mode :program
;;                   :guard t))
;;   (reverse (make-var-names-aux 'x 1 namecount)))

;;;
;;; make-var-names
;;;

;; Makes a list of symbols each of which is BASE-SYMBOL with a numeric suffix
;; added to it.  The result contains symbols from BASE-SYMBOL with a suffix of
;; 0 through BASE-SYMBOL with a suffix of COUNT minus 1.
(defund make-var-names (count base-name)
  (declare (xargs :guard (and (natp count)
                              (symbolp base-name))))
  (make-var-names-aux base-name 0 (+ -1 count)))

(defthm symbol-listp-of-make-var-names
  (symbol-listp (make-var-names count base-name))
  :hints (("Goal" :in-theory (enable make-var-names))))

(defthm true-listp-of-make-var-names
  (true-listp (make-var-names count base-name))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable make-var-names))))

(defthm len-of-make-var-names
  (implies (natp count)
           (equal (len (make-var-names count base-name))
                  count))
  :hints (("Goal" :in-theory (enable make-var-names))))

(defthm consp-of-make-var-names
  (implies (natp count)
           (equal (consp (make-var-names count base-name))
                  (posp count)))
  :hints (("Goal" :in-theory (enable make-var-names))))

;; ;;;
;; ;;; rev-make-var-names (TODO: deprecate in favor of make-var-names)
;; ;;;

;; ;; Makes a list of symbols each of which is BASE-SYMBOL with a numeric suffix
;; ;; added to it.  The result contains symbols from BASE-SYMBOL with a suffix of
;; ;; COUNT minus 1, through BASE-SYMBOL with a suffix of 0.
;; (defund rev-make-var-names (count base-name)
;;   (declare (xargs :guard (and (natp count)
;;                               (symbolp base-name))))
;;   (reverse (make-var-names-aux base-name 0 (+ -1 count))))

;; (defthm symbol-listp-of-rev-make-var-names
;;   (symbol-listp (rev-make-var-names count base-name))
;;   :hints (("Goal" :in-theory (enable rev-make-var-names))))

;; (defthm true-listp-of-rev-make-var-names
;;   (true-listp (rev-make-var-names count base-name))
;;   :rule-classes :type-prescription
;;   :hints (("Goal" :in-theory (enable rev-make-var-names))))

;; (defthm len-of-rev-make-var-names
;;   (implies (natp count)
;;            (equal (len (rev-make-var-names count base-name))
;;                   count))
;;   :hints (("Goal" :in-theory (enable rev-make-var-names))))

;; (defthm consp-of-rev-make-var-names
;;   (implies (natp count)
;;            (equal (consp (rev-make-var-names count base-name))
;;                   (posp count)))
;;   :hints (("Goal" :in-theory (enable rev-make-var-names))))
