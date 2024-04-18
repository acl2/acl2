; Utilities to make variable names
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

;; See also fresh-names.lisp and fresh-names2.lisp.

;; todo: consider removing "var" from these names, as these numbered symbols
;; could be used for other purposes.

(include-book "pack")
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Makes a list of symbols each of which is BASE-SYMBOL with a numeric suffix
;; added.  The first numeric suffix is START, and subsequent ones are
;; consecutive, with a total of COUNT symbols generated.
;rename?
(defund make-var-name-range (base-symbol start count)
  (declare (xargs :guard (and (symbolp base-symbol)
                              (natp start)
                              (natp count))))
    (make-var-names-aux base-symbol start (+ -1 start count)))

(defthm symbol-listp-of-make-var-name-range
  (symbol-listp (make-var-name-range base-symbol start count))
  :hints (("Goal" :in-theory (enable make-var-name-range))))

(defthm len-of-make-var-name-range
  (implies (and (natp start)
                (natp count))
           (equal (len (make-var-name-range base-symbol start count))
                  count))
  :hints (("Goal" :in-theory (enable make-var-name-range))))

(defthm consp-of-make-var-name-range
  (implies (and (natp start)
                (natp count))
           (equal (consp (make-var-name-range base-symbol start count))
                  (posp count)))
  :hints (("Goal" :in-theory (enable make-var-name-range))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Special case where the names start at 0.
;; Makes a list of symbols each of which is BASE-SYMBOL with a numeric suffix
;; added to it.  The result contains symbols from BASE-SYMBOL with a suffix of
;; 0 through BASE-SYMBOL with a suffix of COUNT minus 1.
;; Example: (make-var-names 'in 4) = (in0 in1 in2 in3).
(defund make-var-names (base-symbol count)
  (declare (xargs :guard (and (natp count)
                              (symbolp base-symbol))))
  (make-var-name-range base-symbol 0 count))

(defthm symbol-listp-of-make-var-names
  (symbol-listp (make-var-names base-symbol count))
  :hints (("Goal" :in-theory (enable make-var-names))))

(defthm true-listp-of-make-var-names
  (true-listp (make-var-names base-symbol count))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable make-var-names))))

(defthm len-of-make-var-names
  (implies (natp count)
           (equal (len (make-var-names base-symbol count))
                  count))
  :hints (("Goal" :in-theory (enable make-var-names))))

(defthm consp-of-make-var-names
  (implies (natp count)
           (equal (consp (make-var-names base-symbol count))
                  (posp count)))
  :hints (("Goal" :in-theory (enable make-var-names))))
