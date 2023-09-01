; A simple model to recommend :induct hints.
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HELP")

(include-book "recommendations")
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "kestrel/utilities/nat-to-string" :dir :system)
(include-book "kestrel/utilities/world" :dir :system) ; for fn-formals
(include-book "kestrel/typed-lists-light/cons-listp-dollar" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/lists-light/firstn-def" :dir :system)
(include-book "kestrel/terms-light/function-call-subterms" :dir :system)
(include-book "kestrel/world-light/defined-functionp" :dir :system)
(include-book "kestrel/std/system/measured-subset-plus" :dir :system)
;(include-book "kestrel/utilities/rational-printing" :dir :system)
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/remove-duplicates-equal" :dir :system))

(verify-termination induction-depth-limit) ; move
;; (verify-guards induction-depth-limit) ; todo: needs a guard

(acl2::defthm-flag-find-all-fn-call-subterms
  (defthm theorem-for-find-all-fn-call-subterms
    (implies (pseudo-termp acl2::term)
             (acl2::cons-listp$ (acl2::find-all-fn-call-subterms acl2::term acl2::dead-vars)))
    :flag acl2::find-all-fn-call-subterms)
  (defthm theorem-for-find-all-fn-call-subterms-lst
    (implies (pseudo-term-listp acl2::terms)
             (acl2::cons-listp$ (acl2::find-all-fn-call-subterms-lst acl2::terms acl2::dead-vars)))
    :flag acl2::find-all-fn-call-subterms-lst)
  :hints (("Goal" :in-theory (enable acl2::find-all-fn-call-subterms
                                     acl2::find-all-fn-call-subterms-lst))))

(defthm cons-listp$-of-find-all-fn-call-subterms
  (implies (pseudo-termp term)
           (acl2::cons-listp$ (acl2::find-all-fn-call-subterms term dead-vars)))
  :hints (("Goal" :in-theory (enable acl2::find-all-fn-call-subterms))))

;Walks through the FORMALS and ACTUALS, picking out those ACTUALS whose formals
;are in TARGET-FORMALS.  The order of the returned actuals is the same as in
;the original list of ACTUALS.
(defun filter-actuals-for-formals (formals actuals target-formals)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp actuals)
                              (symbol-listp target-formals))))
  (if (endp formals)
      nil
    (let ((formal (first formals))
          (actual (first actuals)))
      (if (member-eq formal target-formals)
          (cons actual (filter-actuals-for-formals (rest formals) (rest actuals) target-formals))
        (filter-actuals-for-formals (rest formals) (rest actuals) target-formals)))))

(defund filter-good-induct-calls (calls wrld)
  (declare (xargs :guard (and (pseudo-term-listp calls)
                              (acl2::cons-listp$ calls)
                              (plist-worldp wrld))))
  (if (endp calls)
      nil
    (let* ((call (first calls))
           (fn (acl2::ffn-symb call)))
      (if (and (symbolp fn)
               (acl2::defined-functionp fn wrld)
               (acl2::recursivep fn nil wrld)
               (let ((controlling-actuals (filter-actuals-for-formals (acl2::fn-formals fn wrld) (acl2::fargs call) (acl2::measured-subset+ fn wrld))))
                 (and (symbol-listp controlling-actuals)
                      (no-duplicatesp-eq controlling-actuals))))
          (cons call (filter-good-induct-calls (rest calls) wrld))
        (filter-good-induct-calls (rest calls) wrld)))))

(defthm not-member-equal-of-filter-good-induct-calls
  (implies (not (member-equal call calls))
           (not (member-equal call (filter-good-induct-calls calls wrld))))
  :hints (("Goal" :in-theory (enable filter-good-induct-calls))))

(defthm no-duplicatesp-equal-of-filter-good-induct-calls
  (implies (no-duplicatesp-equal calls)
           (no-duplicatesp-equal (filter-good-induct-calls calls wrld)))
  :hints (("Goal" :in-theory (enable filter-good-induct-calls))))

;; Find every subexpression in TERM that is suitable for induction (a call of a
;; recursive function where the controlling actuals are distinct vars).
(defund induct-expressions-in-term (term wrld)
  (declare (xargs :guard (and (pseudo-termp term)
                              (plist-worldp wrld))))
  (let ((calls (acl2::find-all-fn-call-subterms term nil)))
    (filter-good-induct-calls calls wrld)))

;; Just to check
(defthm no-duplicatesp-equal-of-induct-expressions-in-term
  (implies (no-duplicatesp-equal calls)
           (no-duplicatesp-equal (induct-expressions-in-term term wrld)))
  :hints (("Goal" :in-theory (enable induct-expressions-in-term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund induct-expressions-in-terms (terms wrld)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (plist-worldp wrld))))
  (if (endp terms)
      nil
    (union-equal (induct-expressions-in-term (first terms) wrld)
                 (induct-expressions-in-terms (rest terms) wrld))))

;; Just to check
(defthm no-duplicatesp-equal-of-induct-expressions-in-terms
  (implies (no-duplicatesp-equal terms)
           (no-duplicatesp-equal (induct-expressions-in-terms terms wrld)))
  :hints (("Goal" :in-theory (enable induct-expressions-in-terms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund induct-expressions-in-term-lists (term-lists wrld)
  (declare (xargs :guard (and (acl2::pseudo-term-list-listp term-lists)
                              (plist-worldp wrld))))
  (if (endp term-lists)
      nil
    (union-equal (remove-duplicates-equal (induct-expressions-in-terms (first term-lists) wrld)) ; probably, there will never be duplicates if we have a clause
                 (induct-expressions-in-term-lists (rest term-lists) wrld))))

;; Just to check
(defthm no-duplicatesp-equal-of-induct-expressions-in-term-lists
  (implies (no-duplicatesp-equal term-lists)
           (no-duplicatesp-equal (induct-expressions-in-term-lists term-lists wrld)))
  :hints (("Goal" :in-theory (enable induct-expressions-in-term-lists))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-induct-recs-aux (induct-args num)
  (declare (xargs :guard (and (true-listp induct-args)
                              (posp num))))
  (if (endp induct-args)
      nil
    (cons (make-rec (concatenate 'string "induct" (acl2::nat-to-string num))
                    :add-induct-hint
                    (first induct-args)
                    3             ; confidence percentage (quite high) TODO: allow unknown?)
                    nil ; book map ; todo: indicate that the name must be present?
                    )
          (make-induct-recs-aux (rest induct-args) (+ 1 num)))))

(defun make-induct-recs (translated-theorem-body
                         checkpoint-clauses-top
                         checkpoint-clauses-non-top
                         num-recs
                         print
                         state)
  (declare (xargs :guard (and (pseudo-termp translated-theorem-body)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-top)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-non-top)
                              (natp num-recs)
                              (acl2::print-levelp print))
                  :verify-guards nil ; because this calls induction-depth-limit
                  :stobjs state))
  (declare (ignore checkpoint-clauses-non-top)) ;todo?
  (b* ((wrld (w state))
       (- (and (acl2::print-level-at-least-tp print)
               (cw "Making ~x0 :induct recommendations: " ; the line is ended below when we print the time
                   num-recs)))
       (induct-args-from-body (induct-expressions-in-term translated-theorem-body wrld))
       (induct-args-from-top-cps (induct-expressions-in-term-lists checkpoint-clauses-top wrld))
       ;; (induct-args-from-non-top-cps nil) ; todo: should use the non-top-cps somehow?
       ;; todo: how to choose when we can't return them all?:
       (induct-args (acl2::firstn num-recs (append induct-args-from-body
                                                   induct-args-from-top-cps
                                                   ;; if the user has limited the induction depth limit to 0, we may need an explicit :induct t:
                                                   (if (equal 0 (acl2::induction-depth-limit wrld))
                                                       (list t)
                                                     nil)
                                                   ;; (list nil) ; always fails?  the meaning of :induct nil is being discussed
                                                   ;; induct-args-from-non-top-cps
                                                   )))
       (recs (make-induct-recs-aux induct-args 1)))
    (mv nil recs state)))
