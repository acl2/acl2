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
(include-book "kestrel/utilities/rational-printing" :dir :system)

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
(defun make-enable-recs (formula ; an untranslated term
                         num-recs
                         print
                         state)
  (declare (xargs :guard (and (natp num-recs)
                              (acl2::print-levelp print))
                  :stobjs state
                  :mode :program ; because of acl2::translate-term
                  ))
  (b* ((wrld (w state))
       (- (and (acl2::print-level-at-least-tp print)
               (cw "Making ~x0 :enable recommendations: " ; the line is ended below when we print the time
                   num-recs)))
       (print-timep (acl2::print-level-at-least-tp print))
       ((mv start-time state) (if print-timep (acl2::get-real-time state) (mv 0 state)))
       (translated-formula (acl2::translate-term formula 'make-enable-recs wrld))
       (fns-to-try-enabling (set-difference-eq (acl2::defined-fns-in-term translated-formula wrld)
                                               ;; Don't bother wasting time with trying to enable implies
                                               ;; (I suppose we could try it if implies is disabled):
                                               '(implies)))
       (recs-to-return ;; todo: how to choose when we can't return them all?:
        (acl2::firstn num-recs (make-enable-recs-aux fns-to-try-enabling 1)))
       ((mv done-time state) (if print-timep (acl2::get-real-time state) (mv 0 state)))
       (- (and print-timep (prog2$ (acl2::print-to-hundredths (- done-time start-time))
                                   (cw "s~%") ; s = seconds
                                   ))))
    (mv nil recs-to-return state)))

;; (local
;;  (defthm recommendation-listp-of-make-enable-recs
;;    (implies (pseudo-termp formula)
;;             (recommendation-listp (make-enable-recs formula wrld)))))
