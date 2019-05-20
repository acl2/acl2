; Return Type Theorems for Representation of Natural Numbers as Digits
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "core")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defthm-dab-return-types-fn ((eq-thm-name symbolp)
                                    (prefix symbolp)
                                    (topic symbolp)
                                    (topicp booleanp)
                                    (parents symbol-listp)
                                    (parentsp booleanp)
                                    (short stringp)
                                    (shortp booleanp)
                                    (long stringp)
                                    (longp booleanp)
                                    (wrld plist-worldp))
  :returns (event "A @(tsee pseudo-event-formp).")
  :mode :program
  :parents (defthm-dab-return-types)
  :short "Event form to introduce additional return type theorems for
          the conversions from natural numbers to digits."
  :long
  (xdoc::topstring-p
   "See @(tsee defthm-dab-return-types).")
  (b* ((equality (formula eq-thm-name nil wrld))
       (dab-digit-listp-call (cadr equality))
       (base (cadr dab-digit-listp-call))
       (var (caddr dab-digit-listp-call))
       (term (caddr equality))
       (nat=>bendian*-thm-name (packn (list prefix '-nat=>bendian*)))
       (nat=>bendian+-thm-name (packn (list prefix '-nat=>bendian+)))
       (nat=>bendian-thm-name (packn (list prefix '-nat=>bendian)))
       (nat=>lendian*-thm-name (packn (list prefix '-nat=>lendian*)))
       (nat=>lendian+-thm-name (packn (list prefix '-nat=>lendian+)))
       (nat=>lendian-thm-name (packn (list prefix '-nat=>lendian)))
       (nat=>bendian*-call (fcons-term* 'nat=>bendian* base 'nat))
       (nat=>bendian+-call (fcons-term* 'nat=>bendian+ base 'nat))
       (nat=>bendian-call (fcons-term* 'nat=>bendian base 'width 'nat))
       (nat=>lendian*-call (fcons-term* 'nat=>lendian* base 'nat))
       (nat=>lendian+-call (fcons-term* 'nat=>lendian+ base 'nat))
       (nat=>lendian-call (fcons-term* 'nat=>lendian base 'width 'nat))
       (nat=>bendian*-term (fsubcor-var
                            (list var) (list nat=>bendian*-call) term))
       (nat=>bendian+-term (fsubcor-var
                            (list var) (list nat=>bendian+-call) term))
       (nat=>bendian-term (fsubcor-var
                           (list var) (list nat=>bendian-call) term))
       (nat=>lendian*-term (fsubcor-var
                            (list var) (list nat=>lendian*-call) term))
       (nat=>lendian+-term (fsubcor-var
                            (list var) (list nat=>lendian+-call) term))
       (nat=>lendian-term (fsubcor-var
                           (list var) (list nat=>lendian-call) term))
       (theorems
        `((defthm ,nat=>bendian*-thm-name
            ,(untranslate nat=>bendian*-term t wrld)
            :hints (("Goal"
                     :use ((:instance return-type-of-nat=>bendian* (base ,base))
                           (:instance ,eq-thm-name (,var ,nat=>bendian*-call)))
                     :in-theory nil)))
          (defthm ,nat=>bendian+-thm-name
            ,(untranslate nat=>bendian+-term t wrld)
            :hints (("Goal"
                     :use ((:instance return-type-of-nat=>bendian+ (base ,base))
                           (:instance ,eq-thm-name (,var ,nat=>bendian+-call)))
                     :in-theory nil)))
          (defthm ,nat=>bendian-thm-name
            ,(untranslate nat=>bendian-term t wrld)
            :hints (("Goal"
                     :use ((:instance return-type-of-nat=>bendian (base ,base))
                           (:instance ,eq-thm-name (,var ,nat=>bendian-call)))
                     :in-theory nil)))
          (defthm ,nat=>lendian*-thm-name
            ,(untranslate nat=>lendian*-term t wrld)
            :hints (("Goal"
                     :use ((:instance return-type-of-nat=>lendian* (base ,base))
                           (:instance ,eq-thm-name (,var ,nat=>lendian*-call)))
                     :in-theory nil)))
          (defthm ,nat=>lendian+-thm-name
            ,(untranslate nat=>lendian+-term t wrld)
            :hints (("Goal"
                     :use ((:instance return-type-of-nat=>lendian+ (base ,base))
                           (:instance ,eq-thm-name (,var ,nat=>lendian+-call)))
                     :in-theory nil)))
          (defthm ,nat=>lendian-thm-name
            ,(untranslate nat=>lendian-term t wrld)
            :hints (("Goal"
                     :use ((:instance return-type-of-nat=>lendian (base ,base))
                           (:instance ,eq-thm-name (,var ,nat=>lendian-call)))
                     :in-theory nil))))))
    (if topicp
        `(defsection ,topic
           ,@(and parentsp (list :parents parents))
           ,@(and shortp (list :short short))
           ,@(and longp (list :long long))
           ,@theorems)
      `(encapsulate
         ()
         ,@theorems))))

(defsection defthm-dab-return-types
  :parents (digits-any-base)
  :short "Introduce additional return type theorems for
          the conversions from natural numbers to digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given an equality theorem of the form
     @('(equal (dab-digit-listp BASE VAR) TERM<VAR>)'),
     where @('BASE') is an integer greater than 1,
     @('VAR') is a variable,
     and @('TERM<VAR>') is a term with @('VAR') as the only free variable,
     this macro generates six theorems of the form
     @('TERM<(CONV BASE nat)>') or @('TERM<(CONV BASE width nat)>'),
     where @('CONV') is one of the conversions
     @(tsee nat=>bendian*), @(tsee nat=>bendian+), @(tsee nat=>bendian),
     @(tsee nat=>lendian*), @(tsee nat=>lendian+), and @(tsee nat=>lendian),
     where @('TERM<(CONV BASE nat)>') is the result of
     replacing @('VAR') with @('(CONV BASE nat)') in @('TERM<VAR>'),
     and where @('TERM<(CONV BASE width nat)>') is the result of
     replacing @('VAR') with @('(CONV BASE width nat)') in @('TERM<VAR>')
     These are additional return type theorems for these conversions.")
   (xdoc::p
    "The name of the equality theorem
     is the first argument of this macro.
     The name of each generated return type theorem is @('PREFIX-CONV'),
     where @('PREFIX') is the second argument of this macro
     and @('CONV') is the conversion.")
   (xdoc::p
    "The theorems are generated inside a @(tsee defsection)
     whose topic (name), @(':parents'), @(':short'), and @(':long')
     are supplied as keyword arguments.
     If the topic is not supplied, no @(tsee defsection) is generated.
     If any of @(':parents'), @(':short'), or @(':long') is not supplied,
     the @(tsee defsection) has no corresponding
     @(':parents'), @(':short'), or @(':long').")
   (xdoc::p
    "This macro does not thoroughly validates its inputs.
     However, its implementation is quite simple,
     and understanding failures due to incorrect inputs should be easy.
     Regardless, this macro may be extended
     to more thoroughly validate its inputs in the future.")
   (xdoc::@def "defthm-dab-return-types"))

  (defmacro defthm-dab-return-types (eq-thm-name
                                     prefix
                                     &key
                                     (topic 'nil topicp)
                                     (parents 'nil parentsp)
                                     (short '"" shortp)
                                     (long '"" longp))
    (declare (xargs :guard (and (symbolp eq-thm-name)
                                (symbolp prefix)
                                (symbolp topic)
                                (symbol-listp parents)
                                (stringp short)
                                (stringp long))))
    `(make-event (defthm-dab-return-types-fn
                   ',eq-thm-name
                   ',prefix
                   ',topic
                   ',topicp
                   ',parents
                   ',parentsp
                   ',short
                   ',shortp
                   ',long
                   ',longp
                   (w state)))))
