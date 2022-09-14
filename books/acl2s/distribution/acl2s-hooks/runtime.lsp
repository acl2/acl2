(include-book "acl2s" :dir :acl2s-hooks)

;; Why do we need this file?
;; Due to https://github.com/acl2/acl2/issues/1343, if we include the below
;; modify-raw-defun forms in books that will be certified, cert.pl breaks.
;; Therefore, we pull these function definitions out into a separate file
;; so they can be evaluated at runtime.


(defttag :acl2s-runtime-redefs)

; disallow user to exit with good-bye
(make-event
 (let ((formals (getprop 'good-bye-fn 'formals nil 'current-acl2-world (w state))))
   `(acl2::modify-raw-defun acl2::good-bye-fn original-good-bye-fn ,formals
                      (progn
                       (when (acl2s-hooks::acl2s-protected-modep acl2::*the-live-state*)
                             (hard-error
                              'good-bye
                              "Please use the user interface to exit.~%"
                              ()))
                       (original-good-bye-fn . ,formals)))))

(acl2::modify-raw-defun read-object original-read-object (chan st)
                  (progn (when (and (acl2::live-state-p st)
                                    (eq chan *standard-oi*)
                                    (acl2s-hooks::acl2s-interactionp st))
                               (format t "${ReAd-ObJeCt}$~%"))
                         (original-read-object chan st)))

(defttag nil)
