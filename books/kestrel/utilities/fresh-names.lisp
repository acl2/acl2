; Utilities for making fresh names
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
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
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
;(local (include-book "kestrel/lists-light/member-equal" :dir :system))

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
                        ;; removal is needed for the measure:
                        (remove-eq candidate syms-to-avoid)))))

(local
  (defthm fresh-symbol-aux-of-remove-equal-irrel
    (implies (and (< current-num current-num+)
                  (natp current-num)
                  (natp current-num+))
             (equal (fresh-symbol-aux base-sym current-num+ (remove-equal (pack$ base-sym current-num) syms-to-avoid))
                    (fresh-symbol-aux base-sym current-num+ syms-to-avoid)))
    :hints (("Goal" :induct (fresh-symbol-aux base-sym current-num+ syms-to-avoid)
             :expand (fresh-symbol-aux
                       base-sym current-num+
                       (remove-equal
                         (intern-in-package-of-symbol (binary-pack base-sym current-num)
                                                      'rewrite)
                         syms-to-avoid))
             :in-theory (enable fresh-symbol-aux to-string)))))

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

;; (local
;;   (defthm not-equal-of-coerce-of-nat-to-string
;;     (implies (and (not (all-digit-charsp x 10))
;;                   (natp n))
;;              (not (equal x (coerce (nat-to-string n) 'list))))))

(local
  (defthm not-equal-of-nat-to-string
    (implies (and (not (all-digit-charsp (coerce x 'list) 10))
                  (natp n))
             (not (equal x (nat-to-string n))))
    :hints (("Goal" :in-theory (enable nat-to-string)))))

(defthm fresh-symbol-aux-not-nil
  (implies (and base-sym
                (natp current-num))
           (fresh-symbol-aux base-sym current-num syms-to-avoid))
  :hints (("Goal" :in-theory (enable fresh-symbol-aux
                                     binary-pack
                                     equal-of-append
                                     to-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns DESIRED-SYM unless it is in SYMS-TO-AVOID, in which case this
;; tries adding numeric suffixes, starting with 1, until a symbol not in
;; SYMS-TO-AVOID is found.
;; Example: (fresh-symbol 'x '(x x1 x2 x3 x5)) = x4
;; TODO: Perhaps disallow creating nil here?
(defund fresh-symbol (desired-sym syms-to-avoid)
  (declare (xargs :guard (and (symbolp desired-sym)
                              (symbol-listp syms-to-avoid))))
  (if (and (not (member-eq desired-sym syms-to-avoid))
           (mbt (symbolp desired-sym)))
      desired-sym
    (fresh-symbol-aux desired-sym 1 syms-to-avoid)))

(defthm not-member-equal-of-fresh-symbol-same
  (implies (natp current-num)
           (not (member-equal (fresh-symbol desired-sym syms-to-avoid)
                              syms-to-avoid)))
  :hints (("Goal" :in-theory (enable fresh-symbol))))

(defthm fresh-symbol-not-nil
  (implies base-sym
           (fresh-symbol base-sym syms-to-avoid))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fresh-symbol))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: rename to fresh-symbols?
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
