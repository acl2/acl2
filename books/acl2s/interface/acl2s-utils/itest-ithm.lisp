#|

Adapted from prove-cgen.lisp and top.lisp in acl2s/cgen

|#

(in-package "ACL2S")
(include-book "itest-cgen")

(set-verify-guards-eagerness 1)

#|

 itest?-fn returns an error-triple.

 If there is an error, then the returned value is nil.

 If there is no error, then the returned value is a list
 (cts-found? itest?-res), where

 1. cts-found? is t if counterexamples were found and nil otherwise.

 2. itest?-res is of the form (status cts wts)

 3. if cts-found? is nil (no counterexamples) and itest?-fn proved
 the conjecture, then itest?-res is (nil nil wts), where wts is a
 list witnesses found (could be nil). A witness is an assignment of
 values to the variables appearing in the conjecture, which satisfies
 the hypotheses and the conclusion of the conjecture.

 4. if cts-found? is nil (no counterexamples) and itest?-fn did not
 prove the conjecture, then itest?-res is (:? nil wts), where wts is
 a list witnesses found (could be nil). 

 5. if cts-found? is t, then itest?-res is of the form
 (:falsifiable cts wts), where cts is a list of counterexamples and
 wts is a list of witnesses. A counterexample is an assignment of
 values to the variables appearing in the conjecture, which falsifies
 the conjecture.

 Here are some examples

 Error example
 (itest?-fn '(foo x) nil nil state)

 Falsifiable example 1. This example produces both counterexamples
 and witnesses.
 (itest?-fn '(integerp x) nil nil state)

 Falsifiable example 2. This example produces both counterexamples
 and witnesses and is more complex that the previous example. Note
 that assignments, witnesses in this case, may be consistent with
 subgoals, but not with the top-level goal. 
 (itest?-fn '(implies (and (natp x) (natp y) (natp z) (> x 0) (> y 0) (< z 100))
                      (!= z (+ (* x x) (* y y))))
            nil nil state)

 Falsifiable example 3. This example produces only
 counterexamples. Note that ACL2 may do some inference which generates
 a subgoal that does not have witnesses, even if the top level goal
 did.
 (itest?-fn '(/= 0 x) nil nil state)

 Proof example 1. Note that this proof also comes with witnesses. In
 this case witnesses are not that interesting, but if you have hyps,
 finding witnesses can be hard.
 (itest?-fn '(consp (cons x y)) nil nil state)

 No counterexamples and no proof example 1. Notice that we did find
 witnesses. 
 (itest?-fn '(implies (and (integerp x) (integerp y) (integerp z))
                      (/= (+ (expt x 3) (expt y 3) (expt z 3)) 33))
            nil nil state)

 No counterexamples and no proof example 2.
 (itest?-fn '(implies (tlp x) (< (length x) 50)) nil nil state)

 Note that you can use feature of defdata to find counterexamples by
 giving bounds on list lengths.

|#

(defun itest?-fn1 (form hints override-defaults state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* ((ctx 'itest?)
       (debug-enable (acl2::f-get-global 'acl2::debugger-enable state))
       (state (acl2::f-put-global 'acl2::debugger-enable
                                  :never
                                  state))

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
        (with-time-limit timeout
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
Therefore, no counterexamples exist. ~%"
                      (if hints "" " (without induction)"))
           (mv nil NIL state)))
         (t (prog2$
             (cgen::cw? (and pts? (cgen::normal-output-flag vl))
                        "~%Itest? succeeded. No counterexamples were found.~%")
             (mv nil NIL state)))))
       ((er counterexamples) ;; TODO: make sure that what I did below is OK
        (if cgen-err
            (mv t nil state)
          (cgen::extract-cgen cgen::cgen-state state)))
       (state (acl2::f-put-global 'acl2::debugger-enable
                                  debug-enable
                                  state))
       )
    (mv cgen-err (list cts-found? (cons res counterexamples)) state)))

(defun itest?-fn (form hints override-defaults state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (revert-world (itest?-fn1 form hints override-defaults state)))

; This is a version of itest?-fn if you don't have any hints or
; override-defaults.
(defun itest?-fn-simple (form state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (itest?-fn form nil nil state))

(defmacro itest? (form &rest kwd-val-lst) 
  (let* ((vl-entry (assoc-keyword :verbosity-level kwd-val-lst))
         (vl (and vl-entry (cadr vl-entry)))
         (debug (and (natp vl) (cgen::debug-flag vl)))
         (hints-entry (assoc-keyword :hints kwd-val-lst))
         (hints (and hints-entry (cadr hints-entry))))
    `(with-output
      :stack :push
      ,@(if debug '(:on :all :summary-on :all) '(:off :all :summary-off :all))
      ,@(if debug nil (list :on 'comment))
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

Here are some examples of the how to use itest?, itest?-fn and
itest?-fn-simple, the interface versions of test?.

(itest? (foo x))
(itest? (integerp x))
(itest? (implies (and (natp x) (natp y) (natp z) (> x 0) (> y 0) (< z 100))
                 (!= z (+ (* x x) (* y y)))))
(itest? (/= 0 x))
(itest? (consp (cons x y)))
(itest? (implies (and (integerp x) (integerp y) (integerp z))
                 (/= (+ (expt x 3) (expt y 3) (expt z 3)) 33)))
(itest? (implies (tlp x) (< (length x) 50)))

(itest? (implies (and (natp x) (evenp x)) (posp x)))
(itest? (implies (natp x) (integerp x)))
(itest? (implies (integerp x) (natp x)))
(itest? (implies (evenp x) (natp x)))

(itest?-fn-simple '(foo x) state)
(itest?-fn-simple '(integerp x) state)
(itest?-fn-simple '(implies (and (natp x) (natp y) (natp z) (> x 0) (> y 0) (< z 100))
                            (!= z (+ (* x x) (* y y))))
                   state)
(itest?-fn-simple '(/= 0 x) state)
(itest?-fn-simple '(consp (cons x y)) state)
(itest?-fn-simple '(implies (and (integerp x) (integerp y) (integerp z))
                            (/= (+ (expt x 3) (expt y 3) (expt z 3)) 33))
                  state)
(itest?-fn-simple '(implies (tlp x) (< (length x) 50)) state)

(itest?-fn-simple '(implies (and (natp x) (evenp x)) (posp x)) state)
(itest?-fn-simple '(implies (natp x) (integerp x)) state)
(itest?-fn-simple '(implies (integerp x) (natp x)) state)
(itest?-fn-simple '(implies (evenp x) (natp x)) state)

(itest?-fn '(foo x) nil nil state)
(itest?-fn '(implies (and (natp x) (evenp x)) (posp x)) nil nil state)
(itest?-fn '(implies (natp x) (integerp x)) nil nil state)
(itest?-fn '(implies (integerp x) (natp x)) nil nil state)
(itest?-fn '(implies (evenp x) (natp x)) nil nil state)
|#

#|

Here is an example of how you could use itest? and itest?-fn
programmatically. Just comment/uncomment the (itest?-fn ...)
and (itest? ...) forms to try different examples.

(mv-let 
  (er res state)
  (itest?-fn '(implies (natp x) (integerp x)) nil nil state)
;  (itest?-fn-simple '(implies (natp x) (integerp x)) state)
;  (itest? (implies (natp x) (integerp x)))
;  (itest? (implies (integerp x) (natp x)))
;  (itest? (foo x))
;  (itest? (implies (and (integerp x) (integerp y) (integerp z))
;                 (/= (+ (expt x 3) (expt y 3) (expt z 3)) 33)))

  (b* (((when er)
        (prog2$ (cw "~%The itest? form returned an error.~%")
                (mv t nil state)))
       ((list cts-found? itest?-res) res)
       ((list status cts wts) itest?-res))
    (cond (cts-found?
           (prog2$ (cw "~%Not a Theorem!
We got the following counterexamples.~%~x0
We got the following witnesses.~%~x1~%"
                       cts wts)
                   (mv itest?-res 'cgen state)))
          ((not status)
           (prog2$ (cw "~%Theorem!
We got the following witnesses.~%~x0~%"
                       wts)
                   (mv itest?-res 'Theorem state)))
          (t (prog2$ (cw "~%Unknown.
We got the following witnesses.~%~x0~%"
                         wts)
                     (mv itest?-res 'Unknown state))))))

|#

