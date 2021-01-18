; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol-list" :dir :system)
(include-book "std/lists/rcons" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defmax-nat-implementation
  :parents (defmax-nat)
  :short "Implementation of @(tsee defmax-nat)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The implementation functions have formal parameters
     consistently named as follows:")
   (xdoc::ul
    (xdoc::li
     "@('state') is the ACL2 @(see state).")
    (xdoc::li
     "@('ctx') is the context used for errors.")
    (xdoc::li
     "@('f'),
      @('y'),
      @('x1...xn'),
      @('body'),
      @('guard'), and
      @('verify-guards')
      are the honomynous inputs to @(tsee defmax-nat),
      where @('x1...xn') is shown as @('(x1 ... xn')) in the documentation.
      They have no types before being processed,
      then they acquire types implied by their validation.")))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defmax-nat-input-processing
  :parents (defmax-nat-implementation)
  :short "Input processing performed by @(tsee defmax-nat)."
  :long
  (xdoc::topstring-p
   "Currently this validates the inputs lightly.
    It should be improved to do a more thorough validation.")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmax-nat-process-inputs
  (f y x1...xn body guard verify-guards ctx state)
  :returns (mv erp (nothing null) state)
  :short "Process all the inputs."
  :long
  (xdoc::topstring-p
   "We just check that the inputs have the right types.
    We do not check the @('body') and @('guard') inputs,
    since those are untranslated term,
    for which we do not quite have a ``type'' readily available.")
  (declare (ignore body guard))
  (b* (((er &) (ensure-value-is-symbol$ f "The first input" t nil))
       ((er &) (ensure-value-is-symbol$ y "The second input" t nil))
       ((er &) (ensure-value-is-symbol-list$ x1...xn "The third input" t nil))
       ((er &) (ensure-value-is-boolean$ verify-guards
                                         "The :VERIFY-GUARDS input" t nil)))
    (value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defmax-nat-event-generation
  :parents (defmax-nat-implementation)
  :short "Event generation performed by @(tsee defmax-nat)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmax-nat-gen-everything ((f symbolp)
                                   (y symbolp)
                                   (x1...xn symbol-listp)
                                   body
                                   guard
                                   (verify-guards booleanp))
  :returns (event "A @(tsee pseudo-event-formp).")
  :mode :program
  :short "Generate the top-level event."
  :long
  (xdoc::topstring-p
   "The events are generated inside an @(tsee encapsulate).
    Some events are only local, just used to prove the first helper theorem
    @('f.existsp-when-nonempty-and-bounded').
    The exported theorems that have hints are generated
    first locally with the hints,
    then non-locally and redundantly without hints,
    to keep the history ``cleaner''.")
  (b* ((y0 (genvar y (symbol-name y) 0 (list* y x1...xn)))
       (y1 (genvar y (symbol-name y) 1 (list* y y0 x1...xn)))
       (x1...xn-y (rcons y x1...xn))
       (elementp (add-suffix-to-fn f ".ELEMENTP"))
       (uboundp (add-suffix-to-fn f ".UBOUNDP"))
       (existsp (add-suffix-to-fn f ".EXISTSP"))
       (existsp-witness (add-suffix-to-fn existsp "-WITNESS"))
       (uboundp-witness (add-suffix-to-fn uboundp "-WITNESS"))
       (uboundp-necc (add-suffix-to-fn uboundp "-NECC"))
       (existsp-suff (add-suffix-to-fn existsp "-SUFF"))
       (pkgwit (pkg-witness (symbol-package-name f)))
       (booleanp-of-uboundp (packn-pos (list 'booleanp-of uboundp) pkgwit))
       (booleanp-of-existsp (packn-pos (list 'booleanp-of existsp) pkgwit))
       (maybe-natp-of-f (packn-pos (list 'maybe-natp-of- f) pkgwit))
       (natp-of-f-equal-existsp (packn-pos (list 'natp-of- f '-equal- existsp)
                                           pkgwit))
       (natp-of-f-when-existsp (packn-pos (list 'natp-of- f '-when- existsp)
                                          pkgwit))
       (f-iff-existsp (packn-pos (list f '-iff- existsp) pkgwit))
       (not-f-when-not-existsp (packn-pos (list 'not- f '-when-not- existsp)
                                          pkgwit))
       (elementp-of-f-when-existsp (packn-pos
                                    (list elementp '-of- f '-when- existsp)
                                    pkgwit))
       (uboundp-of-f-when-existsp (packn-pos
                                   (list uboundp '-of- f '-when-' existsp)
                                   pkgwit))
       (f-geq-when-existsp-linear (packn-pos
                                   (list f '-geq-when- existsp '-linear)
                                   pkgwit))
       (f-geq-when-existsp-rewrite (packn-pos
                                    (list f '-geq-when- existsp '-rewrite)
                                    pkgwit))
       (f-leq-when-existsp-linear (packn-pos
                                   (list f '-leq-when- existsp '-linear)
                                   pkgwit))
       (f-leq-when-existsp-rewrite (packn-pos
                                    (list f '-leq-when- existsp '-rewrite)
                                    pkgwit))
       (ubound-geq-member (packn-pos (list f '.ubound-geq-member) pkgwit))
       (ubound-nonmember-gt-member (packn-pos
                                    (list f '.ubound-nonmember-gt-member)
                                    pkgwit))
       (find-max (packn-pos (list f '.find-max) pkgwit))
       (find-max-uboundp-preservation (packn-pos
                                       (list f '.find-max-uboundp-preservation)
                                       pkgwit))
       (elementp-of-find-max (packn-pos (list f '.elementp-of-find-max) pkgwit))
       (uboundp-of-find-max (packn-pos (list f '.uboundp-of-find-max) pkgwit))
       (existsp-when-nonempty-and-bounded
        (packn-pos (list f '.existsp-when-nonempty-and-bounded) pkgwit))
       (equal-when-member-and-ubound
        (packn-pos (list f '.equal-when-member-and-ubound) pkgwit))
       (elementp-events
        `((defun ,elementp ,x1...xn-y
            (declare (xargs :guard (and ,guard (natp ,y))))
            ,body)
          ,@(and verify-guards `((verify-guards ,elementp)))
          (in-theory (disable ,elementp))))
       (uboundp-events
        `((defun-sk ,uboundp ,x1...xn-y
            (declare (xargs :guard (and ,guard (natp ,y)) :verify-guards nil))
            (forall (,y1)
                    (impliez (and (natp ,y1)
                                  (,elementp ,@x1...xn ,y1))
                             (>= (nfix ,y) ,y1)))
            :rewrite (implies (and (,uboundp ,@x1...xn-y)
                                   (natp ,y1)
                                   (,elementp ,@x1...xn ,y1))
                              (>= (nfix ,y) ,y1)))
          ,@(and verify-guards `((verify-guards ,uboundp)))
          (defthm ,booleanp-of-uboundp
            (booleanp (,uboundp ,@x1...xn-y)))
          (in-theory (disable ,uboundp ,uboundp-necc))))
       (existsp-events
        `((defun-sk ,existsp ,x1...xn
            (declare (xargs :guard ,guard :verify-guards nil))
            (exists (,y)
                    (and (natp ,y)
                         (,elementp ,@x1...xn-y)
                         (,uboundp ,@x1...xn-y))))
          ,@(and verify-guards `((verify-guards ,existsp)))
          (defthm ,booleanp-of-existsp
            (booleanp (,existsp ,@x1...xn)))
          (in-theory (disable ,existsp ,existsp-suff))))
       (f-events
        `((defun ,f ,x1...xn
            (declare (xargs :guard ,guard))
            (if (,existsp ,@x1...xn)
                (,existsp-witness ,@x1...xn)
              nil))
          ,@(and verify-guards `((verify-guards ,f)))
          ,@(and (null x1...xn) `((in-theory (disable (:e ,f)))))
          (local
           (defthm ,maybe-natp-of-f
             (maybe-natp (,f ,@x1...xn))
             :hints (("Goal" :in-theory (enable maybe-natp ,existsp)))))
          (defthm ,maybe-natp-of-f
            (maybe-natp (,f ,@x1...xn)))
          (local
           (defthm ,natp-of-f-equal-existsp
             (equal (natp (,f ,@x1...xn))
                    (,existsp ,@x1...xn))
             :hints (("Goal" :in-theory (enable ,existsp)))))
          (defthm ,natp-of-f-equal-existsp
            (equal (natp (,f ,@x1...xn))
                   (,existsp ,@x1...xn)))
          (defthm ,natp-of-f-when-existsp
            (implies (,existsp ,@x1...xn)
                     (natp (,f ,@x1...xn)))
            :rule-classes :type-prescription)
          (local
           (defthm ,f-iff-existsp
             (iff (,f ,@x1...xn)
                  (,existsp ,@x1...xn))
             :hints (("Goal" :in-theory (enable ,existsp)))))
          (defthm ,f-iff-existsp
            (iff (,f ,@x1...xn)
                 (,existsp ,@x1...xn)))
          (defthm ,not-f-when-not-existsp
            (implies (not (,existsp ,@x1...xn))
                     (not (,f ,@x1...xn)))
            :rule-classes :type-prescription)
          (local
           (defthm ,elementp-of-f-when-existsp
             (implies (,existsp ,@x1...xn)
                      (,elementp ,@x1...xn (,f ,@x1...xn)))
             :hints (("Goal" :in-theory (enable ,existsp)))))
          (defthm ,elementp-of-f-when-existsp
            (implies (,existsp ,@x1...xn)
                     (,elementp ,@x1...xn (,f ,@x1...xn))))
          (local
           (defthm ,uboundp-of-f-when-existsp
             (implies (,existsp ,@x1...xn)
                      (,uboundp ,@x1...xn (,f ,@x1...xn)))
             :hints (("Goal" :in-theory (enable ,existsp)))))
          (defthm ,uboundp-of-f-when-existsp
            (implies (,existsp ,@x1...xn)
                     (,uboundp ,@x1...xn (,f ,@x1...xn))))
          (local
           (defthm ,f-geq-when-existsp-linear
             (implies (and (,existsp ,@x1...xn)
                           (,elementp ,@x1...xn ,y1)
                           (natp ,y1))
                      (>= (,f ,@x1...xn) ,y1))
             :rule-classes :linear
             :hints (("Goal"
                      :use (,uboundp-of-f-when-existsp
                            (:instance ,uboundp-necc (,y (,f ,@x1...xn))))))))
          (defthm ,f-geq-when-existsp-linear
            (implies (and (,existsp ,@x1...xn)
                          (,elementp ,@x1...xn ,y1)
                          (natp ,y1))
                     (>= (,f ,@x1...xn) ,y1))
            :rule-classes :linear)
          (local
           (defthm ,f-geq-when-existsp-rewrite
             (implies (and (,existsp ,@x1...xn)
                           (,elementp ,@x1...xn ,y1)
                           (natp ,y1))
                      (>= (,f ,@x1...xn) ,y1))
             :hints (("Goal" :by ,f-geq-when-existsp-linear))))
          (defthm ,f-geq-when-existsp-rewrite
            (implies (and (,existsp ,@x1...xn)
                          (,elementp ,@x1...xn ,y1)
                          (natp ,y1))
                     (>= (,f ,@x1...xn) ,y1)))
          (local
           (defthm ,f-leq-when-existsp-linear
             (implies (and (,existsp ,@x1...xn)
                           (,uboundp ,@x1...xn ,y1)
                           (natp ,y1))
                      (<= (,f ,@x1...xn) ,y1))
             :rule-classes :linear
             :hints (("Goal"
                      :in-theory (disable ,f)
                      :use (:instance ,uboundp-necc
                            (,y1 (,f ,@x1...xn)) (,y ,y1))))))
          (defthm ,f-leq-when-existsp-linear
            (implies (and (,existsp ,@x1...xn)
                          (,uboundp ,@x1...xn ,y1)
                          (natp ,y1))
                     (<= (,f ,@x1...xn) ,y1))
            :rule-classes :linear)
          (local
           (defthm ,f-leq-when-existsp-rewrite
             (implies (and (,existsp ,@x1...xn)
                           (,uboundp ,@x1...xn ,y1)
                           (natp ,y1))
                      (<= (,f ,@x1...xn) ,y1))
             :hints (("Goal" :by ,f-leq-when-existsp-linear))))
          (defthm ,f-leq-when-existsp-rewrite
            (implies (and (,existsp ,@x1...xn)
                          (,uboundp ,@x1...xn ,y1)
                          (natp ,y1))
                     (<= (,f ,@x1...xn) ,y1)))
          (in-theory (disable ,f))))
       (existsp-when-non-empty-and-bounded-events
        `((local
           (defthm ,ubound-geq-member
             (implies (and (natp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (natp ,y1)
                           (,uboundp ,@x1...xn ,y1))
                      (>= ,y1 ,y0))
             :rule-classes nil
             :hints (("Goal" :use (:instance ,uboundp-necc
                                   (,y ,y1) (,y1 ,y0))))))
          (local
           (defthm ,ubound-nonmember-gt-member
             (implies (and (natp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (natp ,y1)
                           (,uboundp ,@x1...xn ,y1)
                           (not (,elementp ,@x1...xn ,y1)))
                      (> ,y1 ,y0))
             :rule-classes nil
             :hints (("Goal" :use ,ubound-geq-member))))
          (local
           (defun ,find-max (,@x1...xn ,y1 ,y0)
             (declare (xargs :hints (("Goal"
                                      :use ,ubound-nonmember-gt-member))))
             (if (and (natp ,y0)
                      (,elementp ,@x1...xn ,y0)
                      (natp ,y1)
                      (,uboundp ,@x1...xn ,y1))
                 (if (,elementp ,@x1...xn ,y1)
                     ,y1
                   (,find-max ,@x1...xn (1- ,y1) ,y0))
               0))) ; irrelevant
          (local
           (defthm ,find-max-uboundp-preservation
             (implies (and (natp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (natp ,y1)
                           (,uboundp ,@x1...xn ,y1)
                           (not (,elementp ,@x1...xn ,y1)))
                      (,uboundp ,@x1...xn (1- ,y1)))
             :hints (("Goal"
                      :expand ((,uboundp ,@x1...xn (1- ,y1)))
                      :use (:instance ,uboundp-necc
                            (,y ,y1)
                            (,y1 (,uboundp-witness ,@x1...xn (1- ,y1))))))))
          (local
           (defthm ,elementp-of-find-max
             (implies (and (natp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (natp ,y1)
                           (,uboundp ,@x1...xn ,y1))
                      (,elementp ,@x1...xn (,find-max ,@x1...xn ,y1 ,y0)))
             :hints ('(:use (:instance ,uboundp-necc (,y ,y1) (,y1 0)))
                     '(:use (:instance ,uboundp-necc (,y 0) (,y1 ,y0))))))
          (local
           (defthm ,uboundp-of-find-max
             (implies (and (natp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (natp ,y1)
                           (,uboundp ,@x1...xn ,y1))
                      (,uboundp ,@x1...xn (,find-max ,@x1...xn ,y1 ,y0)))
             :hints ('(:use (:instance ,uboundp-necc (,y ,y1) (,y1 0)))
                     '(:use (:instance ,uboundp-necc (,y 0) (,y1 ,y0))))))
          (local
           (defthm ,existsp-when-nonempty-and-bounded
             (implies (and (natp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (natp ,y1)
                           (,uboundp ,@x1...xn ,y1))
                      (,existsp ,@x1...xn))
             :rule-classes nil
             :hints (("Goal" :use (:instance ,existsp-suff
                                   (,y (,find-max ,@x1...xn ,y1 ,y0)))))))
          (defthm ,existsp-when-nonempty-and-bounded
            (implies (and (natp ,y0)
                          (,elementp ,@x1...xn ,y0)
                          (natp ,y1)
                          (,uboundp ,@x1...xn ,y1))
                     (,existsp ,@x1...xn))
            :rule-classes nil)))
       (equal-when-member-and-bound
        `((local
           (defthm ,equal-when-member-and-ubound
             (implies (and (natp ,y)
                           (,elementp ,@x1...xn ,y)
                           (,uboundp ,@x1...xn ,y))
                      (equal (,f ,@x1...xn) ,y))
             :rule-classes nil
             :hints (("Goal"
                      :in-theory (disable ,f-geq-when-existsp-rewrite)
                      :use ((:instance ,existsp-when-nonempty-and-bounded
                             (,y0 ,y) (,y1 ,y))
                            (:instance ,f-geq-when-existsp-rewrite (,y1 ,y))
                            (:instance ,uboundp-necc (,y1 (,f ,@x1...xn))))))))
          (defthm ,equal-when-member-and-ubound
            (implies (and (natp ,y)
                          (,elementp ,@x1...xn ,y)
                          (,uboundp ,@x1...xn ,y))
                     (equal (,f ,@x1...xn) ,y))
            :rule-classes nil))))
    `(encapsulate
       ()
       (set-verify-guards-eagerness 0)
       ,@elementp-events
       ,@uboundp-events
       ,@existsp-events
       ,@f-events
       ,@existsp-when-non-empty-and-bounded-events
       ,@equal-when-member-and-bound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmax-nat-fn (f y x1...xn body guard verify-guards ctx state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :parents (defmax-nat-implementation)
  :short "Process the inputs and generate the event to submit."
  (b* (((er &) (defmax-nat-process-inputs
                 f y x1...xn body guard verify-guards ctx state))
       (event (defmax-nat-gen-everything
                f y x1...xn body guard verify-guards)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defmax-nat-macro-definition
  :parents (defmax-nat-implementation)
  :short "Definition of the @(tsee defmax-nat) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event generated by @(tsee defmax-nat-fn).")
   (xdoc::@def "defmax-nat"))
  (defmacro defmax-nat (f
                        y
                        x1...xn
                        body
                        &key
                        (guard 't)
                        (verify-guards 't))
    `(make-event (defmax-nat-fn
                   ',f
                   ',y
                   ',x1...xn
                   ',body
                   ',guard
                   ',verify-guards
                   (cons 'defmax-nat ',f)
                   state))))
