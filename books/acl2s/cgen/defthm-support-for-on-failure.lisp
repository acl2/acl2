#|

 BACKGROUND:

 This file redefines defthm.

 The redefinition was motivated by discussions with Eric Smith and
 Alessandro Coglio, who saw various issues with slowdowns due to cgen,
 e.g., in one case a c::defstruct form was taking ~700 seconds with
 cgen on, but only ~4 seconds without it. Even after setting timeouts
 to small numbers, on my machine the defstruct took ~12 seconds, which
 was still significantly slower, so we considered doing something I
 have considered doing for definec, which is to only use
 counterexample generation when a defthm fails.

 We had a meeting with Matt, Rubin, Eric, Alessandro and some other
 folks and I proposed a version of defthm that has a hook that allows
 us to do something if the proof fails. That didn't seem easy, given
 feedback from Matt. I then proposed redefining defthm and Matt saw
 how to do that and volunteered to do it. He sent an initial
 version. The version in this file is based on that.  I fixed a bug in
 the previous version (which was missing a defthm in the definition of
 new-form) and I simplified some of the code. I also changed the
 behavior in a few ways. I'll just explain how this version works with
 further comparisons.

 BEHAVIOR:

 The behavior of defthm is now controlled by the setting the
 testing-enabled acl2s-defaults variable. You have there options: nil,
 :on-failure t and t. There are examples at the end of the file. With
 the nil setting, testing is disabled, so no testing occurs. With the
 :on-failure setting, defthm tries to prove the theorem with testing
 disabled and if that works, no testing is done; however, if it fails,
 then ACL2 tries the defthm again, this time with testing
 enabled. With the t setting, you get the previous behavior, which is
 that the defthm is tried, once, with testing enabled.

 Finally, the :no-retry keyword argument is used to get the behavior
 of defthm before it was redefined, i.e., it is just the appropriate
 call to defthm-fn. There is no need to use this argument at the top
 level, but if you do, then there is only one call to defthm-fn and
 with testing-enabled set to nil, no testing is done, otherwise we do
 test during the proof (for both t and :on-failure).

 EXAMPLES:

 (acl2s-defaults :set testing-enabled nil)
 :trans1 (defthm foo (integerp x))
 :trans1 (defthm foo (integerp x) :no-retry t)
 :trans1 (defthm foo (integerp x) :no-retry nil)

 (acl2s-defaults :set testing-enabled :on-failure)
 :trans1 (defthm foo (integerp x))
 :trans1 (defthm foo (integerp x) :no-retry t)
 :trans1 (defthm foo (integerp x) :no-retry nil)

 (acl2s-defaults :set testing-enabled t)
 :trans1 (defthm foo (integerp x))
 :trans1 (defthm foo (integerp x) :no-retry t)
 :trans1 (defthm foo (integerp x) :no-retry nil)

|#

(in-package "ACL2")
(include-book "acl2s/cgen/top" :dir :system :ttags :all)

; If you want a minimal cgen use this instead of the above.
; (include-book "acl2s/cgen/cgen-no-thms" :dir :system)

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
           (b* ((testing? (acl2s-defaults :get testing-enabled)))
             (if (eq testing? :on-failure)
                 '(:or (encapsulate
                        ()
                        (local (acl2s-defaults :set testing-enabled nil))
                        (with-output :stack :pop ,new-form))
                       (with-output :stack :pop ,new-form))
               '(with-output :stack :pop ,new-form)))
           :expansion? ,new-form))))))

(redef-)
