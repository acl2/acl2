; A tool to make an axe-bind-free evaluator for given functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-axe-syntaxp-evaluator") ;todo: reduce
(include-book "kestrel/alists-light/symbol-alistp" :dir :system) ;todo: make local to the generated event (but need the :dir to make that convenient)

(local (in-theory (enable rational-listp-when-integer-listp)))

(defun make-axe-bind-free-evaluator-fn (suffix fns enables wrld)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbol-listp fns)
                              (plist-worldp wrld))))
  (b* ((eval-axe-bind-free-function-application-fn (pack$ 'eval-axe-bind-free-function-application- suffix))
       (arity-alist (bind-fns-to-arities fns wrld nil))
       (arities (strip-cars arity-alist))
       (max-arity (max-val arities -1)))
    `(encapsulate ()
       (local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
       (local (include-book "kestrel/lists-light/union-equal" :dir :system))
       (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
       (local (include-book "kestrel/arithmetic-light/natp" :dir :system))
       (local (include-book "kestrel/lists-light/len" :dir :system))

       (local (in-theory (enable assoc-equal-iff-two
                                 natp-of-lookup-equal-when-all-dargp-of-strip-cdrs-when-member-equal
                                 not-<-of-largest-non-quotep-of-strip-cdrs-and-lookup-equal-when-member-equal
                                 natp-of-+-of-1)))
       (local (in-theory (disable myquotep
                                  natp
                                  ;; prevent induction:
                                  strip-cdrs
                                  strip-cars
                                  symbol-alistp
                                  alistp)))

       (defund ,eval-axe-bind-free-function-application-fn (fn args alist dag-array)
         (declare (xargs :guard (and (symbolp fn)
                                     (list-of-variables-and-constantsp args)
                                     (symbol-alistp alist)
                                     (all-dargp (strip-cdrs alist))
                                     (subsetp-eq (free-vars-in-terms args) (strip-cars alist))
                                     (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep (strip-cdrs alist)))))
                         :guard-hints (("Goal" :in-theory (e/d (list-of-variables-and-constantsp
                                                                free-vars-in-terms-opener)
                                                               (dargp))
                                        :expand ((free-vars-in-terms args)
                                                 (free-vars-in-term (car args))))))
                  (ignorable dag-array))
         ,(make-axe-syntaxp-evaluator-cases 0 max-arity arity-alist eval-axe-bind-free-function-application-fn wrld))

       (defthm ,(pack$ 'symbol-alistp-of- eval-axe-bind-free-function-application-fn)
         (symbol-alistp (,eval-axe-bind-free-function-application-fn fn args alist dag-array))
         :hints (("Goal" :in-theory (enable ,eval-axe-bind-free-function-application-fn
                                            ,@enables))))

       (defthm ,(pack$ 'true-listp-of- eval-axe-bind-free-function-application-fn)
         (true-listp (,eval-axe-bind-free-function-application-fn fn args alist dag-array))
         :rule-classes :type-prescription
         :hints (("Goal" :use (:instance ,(pack$ 'symbol-alistp-of- eval-axe-bind-free-function-application-fn))
                  :in-theory (disable ,(pack$ 'symbol-alistp-of- eval-axe-bind-free-function-application-fn))))))))

(defmacro make-axe-bind-free-evaluator (suffix
                                        fns &key
                                        (enables 'nil) ;for proving the generated function returns an alist
                                        )
  `(make-event (make-axe-bind-free-evaluator-fn ,suffix ,fns ,enables (w state))))
