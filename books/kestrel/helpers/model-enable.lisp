(in-package "HELP")

; A simple model to recommend enabling functions in a theorem
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "recommendations")
(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/utilities/nat-to-string" :dir :system)
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/world-light/defined-fns-in-term" :dir :system)
(include-book "kestrel/lists-light/firstn-def" :dir :system)
(include-book "kestrel/typed-lists-light/symbol-listp" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system)

(local (in-theory (disable mv-nth)))

(local
 (defthm symbol-listp-of-firstn
   (implies (symbol-listp syms)
            (symbol-listp (acl2::firstn n syms)))
   :hints (("Goal" :in-theory (enable acl2::firstn)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund acl2::defined-fns-in-terms (terms wrld acc)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (plist-worldp wrld)
                              (symbol-listp acc))))
  (if (endp terms)
      acc ; todo: think about the order here
    (acl2::defined-fns-in-terms (rest terms) wrld (union-eq (acl2::defined-fns-in-term (first terms) wrld)
                                                            acc))))

(defthm symbol-listp-of-defined-fns-in-terms
  (implies (and (pseudo-term-listp terms)
                (symbol-listp acc))
           (symbol-listp (acl2::defined-fns-in-terms terms wrld acc)))
  :hints (("Goal" :in-theory (enable acl2::defined-fns-in-terms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund acl2::defined-fns-in-term-lists (term-lists wrld acc)
  (declare (xargs :guard (and (acl2::pseudo-term-list-listp term-lists)
                              (plist-worldp wrld)
                              (symbol-listp acc))))
  (if (endp term-lists)
      acc
    (acl2::defined-fns-in-term-lists (rest term-lists) wrld (acl2::defined-fns-in-terms (first term-lists) wrld acc))))

(defthm symbol-listp-of-defined-fns-in-term-lists
  (implies (and (acl2::pseudo-term-list-listp term-lists)
                (symbol-listp acc))
           (symbol-listp (acl2::defined-fns-in-term-lists term-lists wrld acc)))
  :hints (("Goal" :in-theory (enable acl2::defined-fns-in-term-lists))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move
(local
 (defthm rationalp-of-mv-nth-0-of-read-run-time
  (rationalp (mv-nth 0 (read-run-time state)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-run-time)))))

;; todo: support enabling more than one thing in a single rec
(defun make-enable-recs-aux (names num)
  (declare (xargs :guard (and (symbol-listp names)
                              (posp num))))
  (if (endp names)
      nil
    (cons (make-rec (concatenate 'string "enable" (acl2::nat-to-string num))
                    :add-enable-hint
                    (first names) ; the name to enable
                    5             ; confidence percentage (quite high) TODO: allow unknown?)
                    nil ; book map ; todo: indicate that the name must be present?
                    )
          (make-enable-recs-aux (rest names) (+ 1 num)))))

(local
 (defthm recommendation-listp-of-make-enable-recs-aux
   (implies (symbol-listp names)
            (recommendation-listp (make-enable-recs-aux names num)))
   :hints (("Goal" :in-theory (enable recommendation-listp)))))

;; Don't bother wasting time with trying to enable implies or not.
;; (I suppose we could try if they are disabled, but that is very rare.)
(defconst *fns-to-never-enable* '(implies not))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This version keeps the first of each set of duplicates.
(defund remove-duplicates-equal-alt (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (let ((item (first x)))
      (cons item
            (remove-duplicates-equal-alt
             (if (member-equal item (rest x))
                 (remove-equal item (rest x))
               (rest x)))))))

(defthm symbol-listp-of-remove-duplicates-equal-alt
  (implies (symbol-listp x)
           (symbol-listp (remove-duplicates-equal-alt x)))
  :hints (("Goal" :in-theory (enable remove-duplicates-equal-alt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Don't even make recs for things that are enabled (in the theory, or by the current hints)?
;; TODO: Put in macro-aliases, like append, when possible.  What if there are multiple macro-aliases for a function?  Prefer ones that appear in the untranslated formula?
;; Returns (mv erp recs state), where recs is a list of recs, which should contain no duplicates.
(defun make-enable-fns-body-recs (translated-theorem-body
                                  num-recs
                                  print
                                  state)
  (declare (xargs :guard (and (pseudo-termp translated-theorem-body)
                              (natp num-recs)
                              (acl2::print-levelp print))
                  :stobjs state))
  (b* ((wrld (w state))
       (- (and (acl2::print-level-at-least-tp print)
               (cw "Making ~x0 :enable recommendations for body functions: " ; the line is ended below when we print the time
                   num-recs)))
       ; (translated-formula (acl2::translate-term formula 'make-enable-recs wrld))
       (fns-in-goal (acl2::defined-fns-in-term translated-theorem-body wrld))
       ;; we'll try the ones in the goal first (todo: do a more sophisticated ranking?):
       ;; todo: prefer ones defined in the current book?  more complex ones?
       ;; todo: make a rec that enables all (sensible functions?)
       ;; todo: remove any functions already enabled, at least in the goal hint?
       ;; todo: try all defined functions in the conclusion
       ;; todo: try all defined functions
       ;; perhaps count occurences
       ;; the order here matters (todo: what order to choose?)
       (fns-to-try-enabling (set-difference-eq fns-in-goal *fns-to-never-enable*))
       ;; (fns-to-try-enabling (remove-duplicates-equal-alt fns-to-try-enabling)) ; keeps the first instance of each
       (fns-to-try-enabling (acl2::firstn num-recs fns-to-try-enabling))
       (fns-beyond-the-limit (nthcdr num-recs fns-to-try-enabling))
       (- (and fns-beyond-the-limit
               (cw "Suppressing ~x0 enable recs (beyond num-recs): ~X12.~%" (len fns-beyond-the-limit) fns-beyond-the-limit nil)))
       (recs (make-enable-recs-aux fns-to-try-enabling 1)))
    (mv nil recs state)))

;; (local
;;  (defthm recommendation-listp-of-make-enable-recs
;;    (implies (pseudo-termp formula)
;;             (recommendation-listp (make-enable-recs formula wrld)))))

(defun make-enable-fns-checkpoints-recs (checkpoint-clauses
                                         num-recs
                                         print
                                         state)
  (declare (xargs :guard (and (acl2::pseudo-term-list-listp checkpoint-clauses)
                              (natp num-recs)
                              (acl2::print-levelp print))
                  :stobjs state
;                  :mode :program ; because of acl2::translate-term
                  ))
  (b* ((wrld (w state))
       (- (and (acl2::print-level-at-least-tp print)
               (cw "Making ~x0 :enable recommendations for checkpoints functions: " ; the line is ended below when we print the time
                   num-recs)))
       (fns-in-checkpoints (set-difference-eq (acl2::defined-fns-in-term-lists checkpoint-clauses wrld nil)
                                              *fns-to-never-enable*))
       ;; we'll try the ones in the goal first (todo: do a more sophisticated ranking?):
       ;; todo: prefer ones defined in the current book?  more complex ones?
       ;; todo: make a rec that enables all (sensible functions?)
       ;; todo: remove any functions already enabled, at least in the goal hint?
       ;; todo: try all defined functions in the conclusion
       ;; todo: try all defined functions
       ;; the order here matters (todo: what order to choose?)
       (fns-to-try-enabling fns-in-checkpoints)
       (fns-to-try-enabling (remove-duplicates-equal-alt fns-to-try-enabling)) ; keeps the first instance of each
       (fns-to-try-enabling (acl2::firstn num-recs fns-to-try-enabling))
       (fns-beyond-the-limit (nthcdr num-recs fns-to-try-enabling))
       (- (and fns-beyond-the-limit
               (cw "Suppressing ~x0 enable recs (beyond num-recs): ~X12.~%" (len fns-beyond-the-limit) fns-beyond-the-limit nil)))
       (recs (make-enable-recs-aux fns-to-try-enabling 1)))
    (mv nil recs state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move
(defund rewrite-rules-for-fn (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (getprop fn 'acl2::lemmas nil 'acl2::current-acl2-world wrld))

(defun acl2::one-way-unifyp (pat term)
  (declare (xargs :guard (and (pseudo-termp pat)
                              (pseudo-termp term))))
  (mv-let (matchp subst)
    (acl2::one-way-unify pat term)
    (declare (ignore subst))
    matchp))

(defun rules-that-match-term-aux (rules term)
  (declare (xargs :guard (and (true-listp rules) ; todo
                              (pseudo-termp term))
                  :verify-guards nil))
  (if (endp rules)
      nil
    (let* ((rule (first rules))
           (lhs (access acl2::rewrite-rule rule :lhs)))
      (if (not (pseudo-termp lhs)) ; drop?  ;for guards
          (er hard? 'rules-that-match-term-aux "Bad rule: ~x0." rule)
        (if (acl2::one-way-unifyp lhs term)
            (cons (access acl2::rewrite-rule rule :rune)
                  (rules-that-match-term-aux (rest rules) term))
          (rules-that-match-term-aux (rest rules) term))))))

(defund rules-that-match-term (term wrld)
  (declare (xargs :guard (and (pseudo-termp term)
                              (plist-worldp wrld))
                  :verify-guards nil ; todo
                  ))
  (if (or (acl2::variablep term)
          (acl2::fquotep term))
      nil
    (let ((fn (acl2::ffn-symb term)))
      (if (acl2::flambdap fn)
          nil
        (rules-that-match-term-aux (rewrite-rules-for-fn fn wrld) term)))))

(mutual-recursion
 ;todo: these are really runes?
 (defund rules-that-match-any-subterm (term wrld)
   (declare (xargs :guard (and (pseudo-termp term)
                               (plist-worldp wrld))
                   :verify-guards nil ;;done below
                   ))
   (if (acl2::variablep term)
       nil
     (let ((fn (acl2::ffn-symb term)))
       (if (eq 'quote fn)
           nil
         (union-equal (rules-that-match-term term wrld)
                      (union-equal (if (acl2::flambdap fn)
                                       (rules-that-match-any-subterm (acl2::lambda-body fn) wrld)
                                     nil)
                                   (rules-that-match-any-subterm-list (acl2::fargs term) wrld)))))))

 (defund rules-that-match-any-subterm-list (terms wrld)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (plist-worldp wrld))))
   (if (endp terms)
       nil
     (union-equal (rules-that-match-any-subterm (first terms) wrld)
                  (rules-that-match-any-subterm-list (rest terms) wrld)))))

;(verify-guards rules-that-match-any-subterm)

(defund rules-that-match-any-subterm-list-list (term-lists wrld)
  (declare (xargs :guard (and (acl2::pseudo-term-list-listp term-lists)
                              (plist-worldp wrld))
                  :verify-guards nil ; todo
                  ))
  (if (endp term-lists)
      nil
    (union-equal (rules-that-match-any-subterm-list (first term-lists) wrld)
                 (rules-that-match-any-subterm-list-list (rest term-lists) wrld))))

(defun filter-runes (runes rule-classes)
  (if (endp runes)
      nil
    (let ((rune (first runes)))
      (if (member-eq (car rune) rule-classes)
          (cons rune (filter-runes (rest runes) rule-classes))
        (filter-runes (rest runes) rule-classes)))))

;also works for symbols, etc?
(defun filter-disabled-runes (runes end wrld)
  (if (endp runes)
      nil
    (let ((rune (first runes)))
      (if (acl2::disabledp-fn rune end wrld)
          (cons rune (filter-disabled-runes (rest runes) end wrld))
        (filter-disabled-runes (rest runes) end wrld)))))

;; Returns (mv erp recs state), where recs is a list of recs, which should contain no duplicates.
(defun make-enable-rules-body-recs (translated-theorem-body
                                    num-recs
                                    print
                                    state)
  (declare (xargs :guard (and (pseudo-termp translated-theorem-body)
                              (natp num-recs)
                              (acl2::print-levelp print))
                  :verify-guards nil ; todo
                  :stobjs state))
  (b* ((wrld (w state))
       (- (and (acl2::print-level-at-least-tp print)
               (cw "Making ~x0 :enable rule recs for checkpoints: " ; the line is ended below when we print the time
                   num-recs)))
       (runes (rules-that-match-any-subterm translated-theorem-body wrld))
       ;; Keep only :rewrite rules:
       (runes (filter-runes runes '(:rewrite)))
       (runes (filter-disabled-runes runes (acl2::ens state) (w state)))
       ;; we'll try the ones in the goal first (todo: do a more sophisticated ranking?):
       ;; todo: prefer ones introduced in the current book?  more complex ones?
       ;; todo: make a rec that enables all (sensible) rules?
       ;; todo: remove any rules already enabled, at least in the goal hint?
       ;; todo: prefer ones in the conclusion
       ;; perhaps count occurences
       ;; the order here matters (todo: what order to choose?)
       ;; (fns-to-try-enabling (set-difference-eq fns-in-goal *fns-to-never-enable*))
       ;; (fns-to-try-enabling (remove-duplicates-equal-alt fns-to-try-enabling)) ; keeps the first instance of each
       (runes-to-try-enabling (acl2::firstn num-recs runes))
       (runes-beyond-the-limit (nthcdr num-recs runes-to-try-enabling))
       (- (and runes-beyond-the-limit
               (cw "Suppressing ~x0 enable recs (beyond num-recs): ~X12.~%" (len runes-beyond-the-limit) runes-beyond-the-limit nil)))
       (names-to-enable (acl2::strip-cadrs runes-to-try-enabling)) ;todo: maybe avoid this?  todo: consider corollaries
       (recs (make-enable-recs-aux names-to-enable 1)))
    (mv nil recs state)))

(defun make-enable-rules-checkpoints-recs (checkpoint-clauses
                                           num-recs
                                           print
                                           state)
  (declare (xargs :guard (and (acl2::pseudo-term-list-listp checkpoint-clauses)
                              (natp num-recs)
                              (acl2::print-levelp print))
                  :verify-guards nil ; todo
                  :stobjs state))
  (b* ((wrld (w state))
       (- (and (acl2::print-level-at-least-tp print)
               (cw "Making ~x0 :enable rule recs for body: " ; the line is ended below when we print the time
                   num-recs)))
       (runes (rules-that-match-any-subterm-list-list checkpoint-clauses wrld))
       ;; Keep only :rewrite rules:
       (runes (filter-runes runes '(:rewrite)))
       (runes (filter-disabled-runes runes (acl2::ens state) (w state)))
       ;; we'll try the ones in the goal first (todo: do a more sophisticated ranking?):
       ;; todo: prefer ones introduced in the current book?  more complex ones?
       ;; todo: make a rec that enables all (sensible) rules?
       ;; todo: remove any rules already enabled, at least in the goal hint?
       ;; todo: prefer ones in the conclusion
       ;; perhaps count occurences
       ;; the order here matters (todo: what order to choose?)
       ;; (fns-to-try-enabling (set-difference-eq fns-in-goal *fns-to-never-enable*))
       ;; (fns-to-try-enabling (remove-duplicates-equal-alt fns-to-try-enabling)) ; keeps the first instance of each
       (runes-to-try-enabling (acl2::firstn num-recs runes))
       (runes-beyond-the-limit (nthcdr num-recs runes-to-try-enabling))
       (- (and runes-beyond-the-limit
               (cw "Suppressing ~x0 enable recs (beyond num-recs): ~X12.~%" (len runes-beyond-the-limit) runes-beyond-the-limit nil)))
       (names-to-enable (acl2::strip-cadrs runes-to-try-enabling)) ;todo: maybe avoid this?  todo: consider corollaries
       (recs (make-enable-recs-aux names-to-enable 1)))
    (mv nil recs state)))
