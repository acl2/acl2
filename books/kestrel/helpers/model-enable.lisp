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

;; TODO: Don't even make recs for things that are enabled (in the theory, or by the current hints)?
;; TODO: Put in macro-aliases, like append, when possible.  What if there are multiple macro-aliases for a function?  Prefer ones that appear in the untranslated formula?
;; Returns (mv erp recs state), where recs is a list of recs, which should contain no duplicates.
(defun make-enable-recs (translated-theorem-body
                         checkpoint-clauses
                         num-recs
                         print
                         state)
  (declare (xargs :guard (and (pseudo-termp translated-theorem-body)
                              (acl2::pseudo-term-list-listp checkpoint-clauses)
                              (natp num-recs)
                              (acl2::print-levelp print))
                  :stobjs state
;                  :mode :program ; because of acl2::translate-term
                  ))
  (b* ((wrld (w state))
       (- (and (acl2::print-level-at-least-tp print)
               (cw "Making ~x0 :enable recommendations: " ; the line is ended below when we print the time
                   num-recs)))
       (print-timep (acl2::print-level-at-least-tp print))
       ((mv start-time state) (if print-timep (acl2::get-real-time state) (mv 0 state)))
       ; (translated-formula (acl2::translate-term formula 'make-enable-recs wrld))
       (fns-in-goal (set-difference-eq (acl2::defined-fns-in-term translated-theorem-body wrld)
                                               ;; Don't bother wasting time with trying to enable implies
                                               ;; (I suppose we could try it if implies is disabled):
                                       '(implies)))
       (fns-in-checkpoints (acl2::defined-fns-in-term-lists checkpoint-clauses wrld nil))
       (fns-only-in-checkpoints (set-difference-eq fns-in-checkpoints fns-in-goal))
       ;; we'll try the ones in the goal first (todo: do a more sophisticated ranking?):
       ;; todo: prefer ones defined in the current book?  more complex ones?
       ;; todo: make a rec that enables all (sensible functions?)
       ;; todo: remove any functions already enabled, at least in the goal hint?
       ;; todo: try all defined functions in the conclusion
       ;; todo: try all defined functions
       ;; the order here matters (todo: what order to choose?)
       (fns-to-try-enabling (append fns-in-goal fns-only-in-checkpoints))
       (fns-to-try-enabling (acl2::firstn num-recs fns-to-try-enabling))
       (fns-beyond-the-limit (nthcdr num-recs fns-to-try-enabling))
       (- (and fns-beyond-the-limit
               (cw "Suppressing ~x0 enable recs (beyond num-recs): ~X12.~%" (len fns-beyond-the-limit) fns-beyond-the-limit nil)))
       (recs (make-enable-recs-aux fns-to-try-enabling 1))
       ;; Compute elapsed time:
       ((mv done-time state) (if print-timep (acl2::get-real-time state) (mv 0 state)))
       (time-diff (- done-time start-time))
       (time-diff (if (< time-diff 0)
                      (prog2$ (cw "Warning: negative time reported: ~x0.~%")
                              0)
                    time-diff))
       (- (and print-timep (prog2$ (acl2::print-to-hundredths time-diff)
                                   (cw "s~%") ; s = seconds
                                   ))))
    (mv nil recs state)))

;; (local
;;  (defthm recommendation-listp-of-make-enable-recs
;;    (implies (pseudo-termp formula)
;;             (recommendation-listp (make-enable-recs formula wrld)))))
