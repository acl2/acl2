#|

Adapted from prove-cgen.lisp and top.lisp in acl2s/cgen

|#

(in-package "ACL2S")
(include-book "itest-cgen")

(program)
(set-verify-guards-eagerness 1)

(defun itest?-fn (form hints override-defaults state)
  (declare (xargs :stobjs (state)))
  (b* ((ctx 'itest?)
       (cgen::cgen-state (cgen::make-cgen-state-fn form (cons :USER-DEFINED ctx)
                                                   override-defaults (w state)))       
       (vl              (cgen::cget verbosity-level))
       (pts?            (cgen::cget print-cgen-summary))
       (timeout (cgen::cget cgen-timeout))
       (hints (append '() ;acl2::*bash-skip-forcing-round-hints*
                      (acl2::add-string-val-pair-to-string-val-alist
                       "Goal" :do-not (list 'quote '(acl2::generalize acl2::fertilize))
                       (acl2::add-string-val-pair-to-string-val-alist
                        "Goal" :do-not-induct T hints))))
       ((mv res cgen::cgen-state state) 
        (with-prover-time-limit timeout
                                (prove/cgen form hints cgen::cgen-state state)))
       ((er &) (cond ((not (cgen::cgen-state-p cgen::cgen-state)) (value nil))
                     ((and (<= (acl2::access cgen::gcs% (cgen::cget gcs) :cts) 0)
                           (not pts?))
                      (value nil))
                     (t (cgen::print-testing-summary cgen::cgen-state ctx state))))
       ((mv cgen-err cts-found? state)
        (cond
         ((eq res :falsifiable)
          (prog2$
           (cgen::cw? (cgen::normal-output-flag vl)
"~%Itest? found a counterexample.~%")
           (mv nil t state)))
         ((eq res t)
          (prog2$
           (cgen::cw? (and pts? (cgen::normal-output-flag vl))
"~|Itest? failed (probably due to a hard error).~%")
           (mv t nil state)))
         ((eq res nil)
          (prog2$
           (cgen::cw? (and pts? (cgen::normal-output-flag vl))
"~%Itest? proved the conjecture under consideration~s0. ~
~%Therefore, no counterexamples exist. ~%"
                      (if hints "" " (without induction)"))
           (mv nil NIL state)))
         (t (prog2$
             (cgen::cw? (and pts? (cgen::normal-output-flag vl))
                        "~%Itest? succeeded. No counterexamples were found.~%")
             (mv nil NIL state)))))
       ((er counterexamples) ;; TODO: make sure that what I did below is OK
	(if cgen-err (mv t nil state) (cgen::extract-cgen cgen::cgen-state state))))
      (mv cgen-err (list cts-found? (cons res counterexamples)) state)))

(logic)

(defmacro itest? (form &rest kwd-val-lst) 
  (let* ((vl-entry (assoc-keyword :verbosity-level kwd-val-lst))
         (vl (and vl-entry (cadr vl-entry)))
         (debug (and (natp vl) (cgen::debug-flag vl)))
         (hints-entry (assoc-keyword :hints kwd-val-lst))
         (hints (and hints-entry (cadr hints-entry))))
    `(with-output!
      :stack :push
      ,(if debug :on :off) :all
      :gag-mode ,(not debug)
      (itest?-fn ',form ',hints ',kwd-val-lst state))))

(defconst *hints-no-induct-gen*
  '(:hints (("goal" :do-not-induct t :do-not '(generalize)))))

(defconst *hints-no-induct-gen-otf-on*
  `(,@*hints-no-induct-gen* :otf-flg t))

(defmacro thm-no-induct-gen (f)
  `(thm ,f ,@*hints-no-induct-gen*))

(defmacro thm-no-induct-gen-otf-on (f)
  `(thm ,f ,@*hints-no-induct-gen-otf-on*))

#|

Here are some examples of the how to use itest?, the interface version
of test?.


(mv-let 
 (cx x state)
 (itest? (implies (natp x) (integerp x)))
 (let ((r (car x))
       (cgen-state (cadr x)))
   (cond (cx (prog2$ (cw "~%We got the following counterexamples.~%~x0~%"
                         cgen-state)
                     (mv x 'cgen state)))
         ((not r)
          (prog2$ (cw "~%Theorem.~%")
                  (mv x 'false state)))
         (t (prog2$ (cw "~%Unknown.~%")
                    (mv x 'unknown state))))))

(mv-let 
 (cx x state)
 (itest? (implies (integerp x) (natp x)))
 (let ((r (car x))
       (cgen-state (cadr x)))
   (cond (cx (prog2$ (cw "~%We got the following counterexample.~%~x0~%"
                         cgen-state)
                     (mv x 'cgen state)))
         ((not r)
          (prog2$ (cw "~%Theorem.~%")
                  (mv x 'false state)))
         (t (prog2$ (cw "~%Unknown.~%")
                    (mv x 'unknown state))))))
|#

