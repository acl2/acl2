(in-package "ACL2")

(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "make-becomes-theorem")
(include-book "kestrel/utilities/verify-guards-dollar" :dir :system) ; only needed for verify-guards-for-defun?
(include-book "kestrel/std/system/guard-verified-p" :dir :system)
(include-book "becomes-theorem-names")

;; Generate a verify-guards form for FN.  Returns an
;; event.  The verify-guards form assumes the new function and "becomes"
;; theorem have already been admitted.  TODO: What if the "becomes" theorem
;; has assumptions?
;; todo: rename to verify-guards-form-for-new-defun
(defun verify-guards-for-defun (fn ;the old function
                                function-renaming ;maps fn to new-fn, etc.
                                guard-hints ;; :auto or a list of hints
                                )
  (declare (xargs :guard (and (symbolp fn)
                              (function-renamingp function-renaming))))
  (let ((new-fn (lookup-eq-safe fn function-renaming))
        (guard-hints (if (eq :auto guard-hints)
                         `(("Goal" :use (:instance (:guard-theorem ,fn
                                                                   nil ; don't simplify
                                                                   ))
                            :do-not '(generalize eliminate-destructors) ;;TODO; Turn off more stuff:
                            ;; we use the becomes lemma(s):
                            :in-theory '(,@(becomes-theorem-names function-renaming)
                                         ;; because untranslate can
                                         ;; introduce CASE, which will have
                                         ;; EQLABLEP guard obligations that
                                         ;; may not be in the original
                                         ;; function:
                                         (:e eqlablep)
                                         (:e eqlable-listp) ; not sure whether this is needed, depends on what kinds of CASE untranslate can put in
                                         )))
                       guard-hints)))
    `(verify-guards$ ,new-fn
                      :hints ,guard-hints
                      :guard-simplify nil ;; matches the nil given to :guard-theorem above
                      :otf-flg t)))

;; Maybe generate a verify-guards form for FN.  Returns a (possibly empty) list
;; of events.
(defun maybe-verify-guards-for-defun (fn ;the old function
                                      function-renaming ;maps fn to new-fn, etc.
                                      verify-guards ;; t, nil, or :auto
                                      guard-hints ;; :auto or a list of hints
                                      wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (member-eq verify-guards '(t nil :auto))
                              (function-renamingp function-renaming)
                              (plist-worldp wrld))))
  (let* ((verify-guards (if (eq :auto verify-guards)
                            (guard-verified-p fn wrld)
                          verify-guards)))
    (if (not verify-guards)
        nil ;; empty list of events
      (list (verify-guards-for-defun fn function-renaming guard-hints)))))
