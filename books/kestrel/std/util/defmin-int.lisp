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

(defxdoc+ defmin-int-implementation
  :parents (defmin-int)
  :short "Implementation of @(tsee defmin-int)."
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
      are the honomynous inputs to @(tsee defmin-int),
      where @('x1...xn') is shown as @('(x1 ... xn')) in the documentation.
      They have no types before being processed,
      then they acquire types implied by their validation.")))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defmin-int-input-processing
  :parents (defmin-int-implementation)
  :short "Input processing performed by @(tsee defmin-int)."
  :long
  (xdoc::topstring-p
   "Currently this validates the inputs lightly.
    It should be improved to do a more thorough validation.")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmin-int-process-inputs
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

(defxdoc+ defmin-int-event-generation
  :parents (defmin-int-implementation)
  :short "Event generation performed by @(tsee defmin-int)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmin-int-gen-everything ((f symbolp)
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
       (lboundp (add-suffix-to-fn f ".LBOUNDP"))
       (existsp (add-suffix-to-fn f ".EXISTSP"))
       (existsp-witness (add-suffix-to-fn existsp "-WITNESS"))
       (lboundp-witness (add-suffix-to-fn lboundp "-WITNESS"))
       (lboundp-necc (add-suffix-to-fn lboundp "-NECC"))
       (existsp-suff (add-suffix-to-fn existsp "-SUFF"))
       (pkgwit (pkg-witness (symbol-package-name f)))
       (booleanp-of-lboundp (packn-pos (list 'booleanp-of lboundp) pkgwit))
       (booleanp-of-existsp (packn-pos (list 'booleanp-of existsp) pkgwit))
       (maybe-integerp-of-f (packn-pos (list 'maybe-integerp-of- f) pkgwit))
       (integerp-of-f-equal-existsp (packn-pos
                                     (list 'integerp-of- f '-equal- existsp)
                                     pkgwit))
       (integerp-of-f-when-existsp (packn-pos
                                    (list 'integerp-of- f '-when- existsp)
                                    pkgwit))
       (f-iff-existsp (packn-pos (list f '-iff- existsp) pkgwit))
       (not-f-when-not-existsp (packn-pos (list 'not- f '-when-not- existsp)
                                          pkgwit))
       (elementp-of-f-when-existsp (packn-pos
                                    (list elementp '-of- f '-when- existsp)
                                    pkgwit))
       (lboundp-of-f-when-existsp (packn-pos
                                   (list lboundp '-of- f '-when-' existsp)
                                   pkgwit))
       (f-leq-when-existsp-linear (packn-pos
                                   (list f '-leq-when- existsp '-linear)
                                   pkgwit))
       (f-leq-when-existsp-rewrite (packn-pos
                                    (list f '-leq-when- existsp '-rewrite)
                                    pkgwit))
       (f-geq-when-existsp-linear (packn-pos
                                   (list f '-geq-when- existsp '-linear)
                                   pkgwit))
       (f-geq-when-existsp-rewrite (packn-pos
                                    (list f '-geq-when- existsp '-rewrite)
                                    pkgwit))
       (lbound-leq-member (packn-pos (list f '.lbound-leq-member) pkgwit))
       (lbound-nonmember-gt-member (packn-pos
                                    (list f '.lbound-nonmember-gt-member)
                                    pkgwit))
       (find-min (packn-pos (list f '.find-min) pkgwit))
       (find-min-lboundp-preservation (packn-pos
                                       (list f '.find-min-lboundp-preservation)
                                       pkgwit))
       (elementp-of-find-min (packn-pos (list f '.elementp-of-find-min) pkgwit))
       (lboundp-of-find-min (packn-pos (list f '.lboundp-of-find-min) pkgwit))
       (existsp-when-nonempty-and-bounded
        (packn-pos (list f '.existsp-when-nonempty-and-bounded) pkgwit))
       (equal-when-member-and-lbound
        (packn-pos (list f '.equal-when-member-and-lbound) pkgwit))
       (elementp-events
        `((defun ,elementp ,x1...xn-y
            (declare (xargs :guard (and ,guard (integerp ,y))))
            ,body)
          ,@(and verify-guards `((verify-guards ,elementp)))
          (in-theory (disable ,elementp))))
       (lboundp-events
        `((defun-sk ,lboundp ,x1...xn-y
            (declare (xargs :guard (and ,guard (integerp ,y))
                            :verify-guards nil))
            (forall (,y1)
                    (impliez (and (integerp ,y1)
                                  (,elementp ,@x1...xn ,y1))
                             (<= (ifix ,y) ,y1)))
            :rewrite (implies (and (,lboundp ,@x1...xn-y)
                                   (integerp ,y1)
                                   (,elementp ,@x1...xn ,y1))
                              (<= (ifix ,y) ,y1)))
          ,@(and verify-guards `((verify-guards ,lboundp)))
          (defthm ,booleanp-of-lboundp
            (booleanp (,lboundp ,@x1...xn-y)))
          (in-theory (disable ,lboundp ,lboundp-necc))))
       (existsp-events
        `((defun-sk ,existsp ,x1...xn
            (declare (xargs :guard ,guard :verify-guards nil))
            (exists (,y)
                    (and (integerp ,y)
                         (,elementp ,@x1...xn-y)
                         (,lboundp ,@x1...xn-y))))
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
           (defthm ,maybe-integerp-of-f
             (maybe-integerp (,f ,@x1...xn))
             :hints (("Goal" :in-theory (enable maybe-integerp ,existsp)))))
          (defthm ,maybe-integerp-of-f
            (maybe-integerp (,f ,@x1...xn)))
          (local
           (defthm ,integerp-of-f-equal-existsp
             (equal (integerp (,f ,@x1...xn))
                    (,existsp ,@x1...xn))
             :hints (("Goal" :in-theory (enable ,existsp)))))
          (defthm ,integerp-of-f-equal-existsp
            (equal (integerp (,f ,@x1...xn))
                   (,existsp ,@x1...xn)))
          (defthm ,integerp-of-f-when-existsp
            (implies (,existsp ,@x1...xn)
                     (integerp (,f ,@x1...xn)))
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
           (defthm ,lboundp-of-f-when-existsp
             (implies (,existsp ,@x1...xn)
                      (,lboundp ,@x1...xn (,f ,@x1...xn)))
             :hints (("Goal" :in-theory (enable ,existsp)))))
          (defthm ,lboundp-of-f-when-existsp
            (implies (,existsp ,@x1...xn)
                     (,lboundp ,@x1...xn (,f ,@x1...xn))))
          (local
           (defthm ,f-leq-when-existsp-linear
             (implies (and (,existsp ,@x1...xn)
                           (,elementp ,@x1...xn ,y1)
                           (integerp ,y1))
                      (<= (,f ,@x1...xn) ,y1))
             :rule-classes :linear
             :hints (("Goal"
                      :in-theory (disable ,f)
                      :use (,lboundp-of-f-when-existsp
                            (:instance ,lboundp-necc (,y (,f ,@x1...xn))))))))
          (defthm ,f-leq-when-existsp-linear
            (implies (and (,existsp ,@x1...xn)
                          (,elementp ,@x1...xn ,y1)
                          (integerp ,y1))
                     (<= (,f ,@x1...xn) ,y1))
            :rule-classes :linear)
          (local
           (defthm ,f-leq-when-existsp-rewrite
             (implies (and (,existsp ,@x1...xn)
                           (,elementp ,@x1...xn ,y1)
                           (integerp ,y1))
                      (<= (,f ,@x1...xn) ,y1))
             :hints (("Goal" :by ,f-leq-when-existsp-linear))))
          (defthm ,f-leq-when-existsp-rewrite
            (implies (and (,existsp ,@x1...xn)
                          (,elementp ,@x1...xn ,y1)
                          (integerp ,y1))
                     (<= (,f ,@x1...xn) ,y1)))
          (local
           (defthm ,f-geq-when-existsp-linear
             (implies (and (,existsp ,@x1...xn)
                           (,lboundp ,@x1...xn ,y1)
                           (integerp ,y1))
                      (>= (,f ,@x1...xn) ,y1))
             :rule-classes :linear
             :hints (("Goal"
                      :in-theory (disable ,f)
                      :use (:instance ,lboundp-necc
                            (,y1 (,f ,@x1...xn)) (,y ,y1))))))
          (defthm ,f-geq-when-existsp-linear
            (implies (and (,existsp ,@x1...xn)
                          (,lboundp ,@x1...xn ,y1)
                          (integerp ,y1))
                     (>= (,f ,@x1...xn) ,y1))
            :rule-classes :linear)
          (local
           (defthm ,f-geq-when-existsp-rewrite
             (implies (and (,existsp ,@x1...xn)
                           (,lboundp ,@x1...xn ,y1)
                           (integerp ,y1))
                      (>= (,f ,@x1...xn) ,y1))
             :hints (("Goal" :by ,f-geq-when-existsp-linear))))
          (defthm ,f-geq-when-existsp-rewrite
            (implies (and (,existsp ,@x1...xn)
                          (,lboundp ,@x1...xn ,y1)
                          (integerp ,y1))
                     (>= (,f ,@x1...xn) ,y1)))
          (in-theory (disable ,f))))
       (existsp-when-non-empty-and-bounded-events
        `((local
           (defthm ,lbound-leq-member
             (implies (and (integerp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (integerp ,y1)
                           (,lboundp ,@x1...xn ,y1))
                      (<= ,y1 ,y0))
             :rule-classes nil
             :hints (("Goal" :use (:instance ,lboundp-necc
                                   (,y ,y1) (,y1 ,y0))))))
          (local
           (defthm ,lbound-nonmember-gt-member
             (implies (and (integerp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (integerp ,y1)
                           (,lboundp ,@x1...xn ,y1)
                           (not (,elementp ,@x1...xn ,y1)))
                      (< ,y1 ,y0))
             :rule-classes nil
             :hints (("Goal" :use ,lbound-leq-member))))
          (local
           (defun ,find-min (,@x1...xn ,y1 ,y0)
             (declare (xargs
                       :measure (nfix (- ,y0 ,y1))
                       :hints (("Goal" :use ,lbound-nonmember-gt-member))))
             (if (and (integerp ,y0)
                      (,elementp ,@x1...xn ,y0)
                      (integerp ,y1)
                      (,lboundp ,@x1...xn ,y1))
                 (if (,elementp ,@x1...xn ,y1)
                     ,y1
                   (,find-min ,@x1...xn (1+ ,y1) ,y0))
               0))) ; irrelevant
          (local
           (defthm ,find-min-lboundp-preservation
             (implies (and (integerp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (integerp ,y1)
                           (,lboundp ,@x1...xn ,y1)
                           (not (,elementp ,@x1...xn ,y1)))
                      (,lboundp ,@x1...xn (1+ ,y1)))
             :hints (("Goal"
                      :expand ((,lboundp ,@x1...xn (1+ ,y1)))
                      :use (:instance ,lboundp-necc
                            (,y ,y1)
                            (,y1 (,lboundp-witness ,@x1...xn (1+ ,y1))))))))
          (local
           (defthm ,elementp-of-find-min
             (implies (and (integerp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (integerp ,y1)
                           (,lboundp ,@x1...xn ,y1))
                      (,elementp ,@x1...xn (,find-min ,@x1...xn ,y1 ,y0)))
             :hints ('(:use (:instance ,lboundp-necc (,y ,y1) (,y1 0)))
                     '(:use (:instance ,lboundp-necc (,y 0) (,y1 ,y0))))))
          (local
           (defthm ,lboundp-of-find-min
             (implies (and (integerp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (integerp ,y1)
                           (,lboundp ,@x1...xn ,y1))
                      (,lboundp ,@x1...xn (,find-min ,@x1...xn ,y1 ,y0)))
             :hints ('(:use (:instance ,lboundp-necc (,y ,y1) (,y1 0)))
                     '(:use (:instance ,lboundp-necc (,y 0) (,y1 ,y0))))))
          (local
           (defthm ,existsp-when-nonempty-and-bounded
             (implies (and (integerp ,y0)
                           (,elementp ,@x1...xn ,y0)
                           (integerp ,y1)
                           (,lboundp ,@x1...xn ,y1))
                      (,existsp ,@x1...xn))
             :rule-classes nil
             :hints (("Goal" :use (:instance ,existsp-suff
                                   (,y (,find-min ,@x1...xn ,y1 ,y0)))))))
          (defthm ,existsp-when-nonempty-and-bounded
            (implies (and (integerp ,y0)
                          (,elementp ,@x1...xn ,y0)
                          (integerp ,y1)
                          (,lboundp ,@x1...xn ,y1))
                     (,existsp ,@x1...xn))
            :rule-classes nil)))
       (equal-when-member-and-bound
        `((local
           (defthm ,equal-when-member-and-lbound
             (implies (and (integerp ,y)
                           (,elementp ,@x1...xn ,y)
                           (,lboundp ,@x1...xn ,y))
                      (equal (,f ,@x1...xn) ,y))
             :rule-classes nil
             :hints (("Goal"
                      :in-theory (disable ,f-leq-when-existsp-rewrite
                                          ,f-geq-when-existsp-rewrite)
                      :use ((:instance ,existsp-when-nonempty-and-bounded
                             (,y0 ,y) (,y1 ,y))
                            (:instance ,f-leq-when-existsp-rewrite (,y1 ,y))
                            (:instance ,lboundp-necc (,y1 (,f ,@x1...xn))))))))
          (defthm ,equal-when-member-and-lbound
            (implies (and (integerp ,y)
                          (,elementp ,@x1...xn ,y)
                          (,lboundp ,@x1...xn ,y))
                     (equal (,f ,@x1...xn) ,y))
            :rule-classes nil))))
    `(encapsulate
       ()
       (set-verify-guards-eagerness 0)
       ,@elementp-events
       ,@lboundp-events
       ,@existsp-events
       ,@f-events
       ,@existsp-when-non-empty-and-bounded-events
       ,@equal-when-member-and-bound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defmin-int-fn (f y x1...xn body guard verify-guards ctx state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :parents (defmin-int-implementation)
  :short "Process the inputs and generate the event to submit."
  (b* (((er &) (defmin-int-process-inputs
                 f y x1...xn body guard verify-guards ctx state))
       (event (defmin-int-gen-everything
                f y x1...xn body guard verify-guards)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defmin-int-macro-definition
  :parents (defmin-int-implementation)
  :short "Definition of the @(tsee defmin-int) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event generated by @(tsee defmin-int-fn).")
   (xdoc::@def "defmin-int"))
  (defmacro defmin-int (f
                        y
                        x1...xn
                        body
                        &key
                        (guard 't)
                        (verify-guards 't))
    `(make-event (defmin-int-fn
                   ',f
                   ',y
                   ',x1...xn
                   ',body
                   ',guard
                   ',verify-guards
                   (cons 'defmin-int ',f)
                   state))))
