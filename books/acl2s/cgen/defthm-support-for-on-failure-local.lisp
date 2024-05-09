#|

 BACKGROUND:

 This file redefines defthm.

 See defthm-support-for-on-failure for a related version that may be
 preferable to this one.  This version was motivated by discussions
 with Alessandro Coglio. The issue with including cgen/top or
 cgen/cgen-no-thms is that top includes some rules that may interfere
 with the proof, e.g., Eric Smith had an example where cgen/top
 included a simple tau rule that proved a defthm that failed without
 cgen/top included. That led to the book cgen/cgen-no-thms, which does
 not add any enabled theorems, but it does include some books, e.g.,
 some std books, and their defthms are disabled. Alessandro had another
 book where he included cgen/cgen-no-thms and then after that included
 some of the std books in cgen and that cause proof failures because
 loading the std books again did not enable the disabled theorems. So,
 now cgen/cgen-no-thms was causing proof failures.

 That brings us to this version. The idea is to redefine defthm so
 that it only tries cgen after a failure and it then locally includes
 the cgen books for this counterexample generation effort. You pay a
 penalty of ~1 second to load the book, but cgen isn't otherwise
 loaded so it can't interfere with your other proofs.  Note that it is
 still possible that cgen will prove the theorem, e.g., consider the
 Eric Smith example mentioned above, but, if that happens, we still
 fail.

 EXAMPLES:

 :trans1 (defthm foo (integerp x))
 :trans1 (defthm foo (integerp x) :no-retry t)
 :trans1 (defthm foo (integerp x) :no-retry nil)

|#

(in-package "ACL2")

(defttag t)
(redef+)

(defmacro defthm (&whole event-form
                         name term
                         &key (rule-classes '(:REWRITE))
                         instructions
                         hints
                         otf-flg
                         (no-retry 'nil)) ; no-retry is a new keyword argument.
  (cond
   ;; This defthm-fn form should be kept in sync with the definition of
   ;; defthm in axioms.lisp
   (no-retry `(defthm-fn ',name ',term state ',rule-classes
                ',instructions ',hints ',otf-flg ',event-form
                #+:non-standard-analysis ; std-p
                nil))
   (t (let ((new-form
             `(defthm ,name ,term :no-retry t
                ,@(acl2::remove-keyword :no-retry (cdddr event-form)))))
        `(with-output
          :off :all
          :stack :push
          (make-event
           '(:or (with-output :stack :pop ,new-form)
                 (encapsulate
                  ()
                  (local (include-book "acl2s/cgen/top" :dir :system :ttags :all))
                  (local (acl2s-defaults :set testing-enabled t))
                  (with-output :stack :pop ,new-form)
                  (mv nil nil state))) ; Fail even if cgen gets the thm!
           :expansion? ,new-form))))))

(redef-)
