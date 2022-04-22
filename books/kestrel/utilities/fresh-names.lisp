; Utilities for making fresh names
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "pack")
(local (include-book "coerce"))
(local (include-book "intern-in-package-of-symbol"))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
;(local (include-book "kestrel/lists-light/member-equal" :dir :system))

;;;
;;; fresh-symbol-aux
;;;

;; Keeps trying numeric suffixes, starting with CURRENT-NUM, adding each one to
;; BASE-SYM until a symbol not in SYMS-TO-AVOID is found.
(defund fresh-symbol-aux (base-sym current-num syms-to-avoid)
  (declare (xargs :guard (and (symbolp base-sym)
                              (natp current-num)
                              (symbol-listp syms-to-avoid))
                  :split-types t
                  :measure (len syms-to-avoid))
           (type (integer 0 *) current-num))
  (let ((candidate (pack$ base-sym current-num)))
    (if (not (member-eq candidate syms-to-avoid))
        candidate
      (fresh-symbol-aux base-sym
                      (+ 1 current-num)
                      (remove-eq candidate
                                 syms-to-avoid)))))

(local
 (defthm fresh-symbol-aux-of-remove-equal-irrel
   (implies (and (< current-num current-num+)
                 (natp current-num)
                 (natp current-num+))
            (equal (FRESH-SYMBOL-AUX BASE-SYM
                                   CURRENT-NUM+
                                   (REMOVE-EQUAL
                                    (pack$ base-sym current-num)
                                    SYMS-TO-AVOID))
                   (FRESH-SYMBOL-AUX BASE-SYM
                                   CURRENT-NUM+
                                   SYMS-TO-AVOID)))
   :hints (("Goal" :induct (FRESH-SYMBOL-AUX BASE-SYM CURRENT-NUM+ SYMS-TO-AVOID)
            :expand (FRESH-SYMBOL-AUX
                     BASE-SYM CURRENT-NUM+
                     (REMOVE-EQUAL
                      (INTERN-IN-PACKAGE-OF-SYMBOL (BINARY-PACK BASE-SYM CURRENT-NUM)
                                                   'REWRITE)
                      SYMS-TO-AVOID))
            :in-theory (enable FRESH-SYMBOL-AUX to-string)))))


(local
 (defthm not-equal-of-fresh-symbol-aux-and-pack$-lower-num
   (implies (and (< current-num current-num+)
                 (natp current-num)
                 (natp current-num+))
            (not (equal (fresh-symbol-aux base-sym current-num+ syms-to-avoid)
                        (pack$ base-sym current-num))))
   :hints (("Goal" :in-theory (enable fresh-symbol-aux)))))

(defthm not-member-equal-of-fresh-symbol-aux-same
  (implies (natp current-num)
           (not (member-equal (fresh-symbol-aux base-sym current-num syms-to-avoid)
                              syms-to-avoid)))
  :hints (("Goal" :in-theory (enable fresh-symbol-aux))))

(defthm not-member-equal-of-fresh-symbol-aux
  (implies (and (subsetp-equal syms syms-to-avoid)
                (natp current-num))
           (not (member-equal (fresh-symbol-aux base-sym current-num syms-to-avoid)
                              syms)))
  :hints (("Goal" :use (:instance not-member-equal-of-fresh-symbol-aux-same)
           :in-theory (disable not-member-equal-of-fresh-symbol-aux-same))))

;todo: gen
(defthm fresh-symbol-aux-of-x-not-nil
  (fresh-symbol-aux 'x current-num syms-to-avoid)
  :hints (("Goal" :in-theory (enable fresh-symbol-aux
                                     BINARY-PACK))))

;;;
;;; fresh-symbol
;;;

;; Returns DESIRED-SYM unless it is in SYMS-TO-AVOID, in which case this
;; tries adding numeric suffixes, starting with 1, until a symbol not in
;; SYMS-TO-AVOID is found.
;; Example: (fresh-symbol 'x '(x x1 x2 x3 x5)) = x4
;; TODO: Perhaps disallow creating nil here?
(defund fresh-symbol (desired-sym syms-to-avoid)
  (declare (xargs :guard (and (symbolp desired-sym)
                              (symbol-listp syms-to-avoid))))
  (if (not (member-eq desired-sym syms-to-avoid))
      desired-sym
    (fresh-symbol-aux desired-sym 1 syms-to-avoid)))

(defthm not-member-equal-of-fresh-symbol-same
  (implies (natp current-num)
           (not (member-equal (fresh-symbol desired-sym syms-to-avoid)
                              syms-to-avoid)))
  :hints (("Goal" :in-theory (enable fresh-symbol))))

;todo: gen
(defthm fresh-symbol-of-x-not-nil
  (fresh-symbol 'x syms-to-avoid)
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fresh-symbol))))

;; ;type-prescription already knows this?
;; (defthm symbolp-of-fresh-symbol
;;   (implies (symbolp desired-sym)
;;            (symbolp (fresh-symbol desired-sym syms-to-avoid)))
;;   :rule-classes :type-prescription)

(defund fresh-var-names (num base-sym syms-to-avoid)
  (declare (xargs :guard (and (natp num)
                              (symbolp base-sym)
                              (symbol-listp syms-to-avoid))
                  :split-types t)
           (type (integer 0 *) num))
  (if (zp num)
      nil
    (let ((fresh-name (fresh-symbol-aux base-sym 0 syms-to-avoid))) ;should this return a new starting-num?
      (cons fresh-name (fresh-var-names (+ -1 num) base-sym (cons fresh-name syms-to-avoid))))))

;; TODO: Make later names avoid earlier names?
(defund make-fresh-names (desired-names names-to-avoid)
  (declare (xargs :guard (and (symbol-listp desired-names)
                              (symbol-listp names-to-avoid))))
  (if (endp desired-names)
      nil
    (cons (fresh-symbol (first desired-names) names-to-avoid)
          (make-fresh-names (rest desired-names) (rest names-to-avoid)))))

(defthm symbol-listp-of-make-fresh-names
  (implies (symbol-listp desired-names)
           (symbol-listp (make-fresh-names desired-names names-to-avoid)))
  :hints (("Goal" :in-theory (enable make-fresh-names))))

(defthm len-of-make-fresh-names
  (equal (len (make-fresh-names desired-names names-to-avoid))
         (len desired-names))
  :hints (("Goal" :in-theory (enable make-fresh-names))))
