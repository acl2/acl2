(in-package "HELP")

(include-book "recommendations")

;; ;; todo: look at checkpoints and goal
;; (defun make-cases-recs (formula num-recs print state)
;;   (declare (xargs :guard (and ;; formula is an untranslated term
;;                           (natp num-recs))
;;                   :stobjs state
;;                   :mode :program ; because of acl2::translate-term
;;                   ))
;;   (b* ((wrld (w state))
;;        (- (and (acl2::print-level-at-least-tp print)
;;                (cw "Making ~x0 :cases recommendations: " ; the line is ended below when we print the time
;;                    num-recs)))
;;        (print-timep (acl2::print-level-at-least-tp print))
;;        ((mv start-time state) (if print-timep (acl2::get-real-time state) (mv 0 state)))
;;        (translated-formula (acl2::translate-term formula 'make-enable-recs wrld))
;;        ;; For now, just suggest cases when we have a boolean term equated to something else
;;        (equated-boolean-terms (acl2::equated-boolean-subterms

;;        ;; (fns-to-try-enabling (set-difference-eq (acl2::defined-fns-in-term translated-formula wrld)
;;        ;;                                         ;; Don't bother wasting time with trying to enable implies
;;        ;;                                         ;; (I suppose we could try it if implies is disabled):
;;        ;;                                         '(implies)))
;;        (recs-to-return ;; todo: how to choose when we can't return them all?:
;;         (acl2::firstn num-recs (make-enable-recs-aux fns-to-try-enabling 1)))
;;        ((mv done-time state) (if print-timep (acl2::get-real-time state) (mv 0 state)))
;;        (- (and print-timep (prog2$ (acl2::print-to-hundredths (- done-time start-time))
;;                                    (cw "s~%") ; s = seconds
;;                                    ))))
;;     (mv nil recs-to-return state)))
