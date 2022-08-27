; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "execution-rules")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-uaconvert-values-rules-generation
  :short "Code to generate the rules for @(tsee uaconvert-values)."

  (define atc-uaconvert-values-rules-gen ((ltype typep) (rtype typep))
    :guard (and (type-nonchar-integerp ltype)
                (type-nonchar-integerp rtype))
    :returns (mv (name symbolp)
                 (event pseudo-event-formp))
    :parents nil
    (b* ((lfixtype (integer-type-to-fixtype ltype))
         (rfixtype (integer-type-to-fixtype rtype))
         (lpred (pack lfixtype 'p))
         (rpred (pack rfixtype 'p))
         (type (uaconvert-types ltype rtype))
         (fixtype (integer-type-to-fixtype type))
         (lterm (if (equal type ltype)
                    'x
                  `(,(pack fixtype '-from- lfixtype) x)))
         (rterm (if (equal type rtype)
                    'y
                  `(,(pack fixtype '-from- rfixtype) y)))
         (name (pack 'uaconvert-values-when- lpred '-and- rpred))
         (event `(defruled ,name
                   (implies (and (,lpred x)
                                 (,rpred y))
                            (equal (uaconvert-values x y)
                                   (mv ,lterm ,rterm)))
                   :enable (uaconvert-values
                            uaconvert-types
                            promote-type
                            convert-integer-value-to-type-of-value
                            type-of-value-when-sintp
                            type-of-value-when-uintp
                            type-of-value-when-slongp
                            type-of-value-when-ulongp
                            type-of-value-when-sllongp
                            type-of-value-when-ullongp
                            value-integerp
                            value-unsigned-integerp-alt-def
                            value-signed-integerp-alt-def
                            ,@*atc-convert-integer-value-rules*))))
      (mv name event))
    :guard-hints (("Goal" :in-theory (enable type-arithmeticp type-realp))))

  (define atc-uaconvert-values-rules-gen-loop-rtypes ((ltype typep)
                                                      (rtypes type-listp))
    :guard (and (type-nonchar-integerp ltype)
                (type-nonchar-integer-listp rtypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp rtypes)) (mv nil nil))
         ((mv name event) (atc-uaconvert-values-rules-gen ltype (car rtypes)))
         ((mv names events)
          (atc-uaconvert-values-rules-gen-loop-rtypes ltype (cdr rtypes))))
      (mv (cons name names) (cons event events))))

  (define atc-uaconvert-values-rules-gen-loop-ltypes ((ltypes type-listp)
                                                      (rtypes type-listp))
    :guard (and (type-nonchar-integer-listp ltypes)
                (type-nonchar-integer-listp rtypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp ltypes)) (mv nil nil))
         ((mv names events)
          (atc-uaconvert-values-rules-gen-loop-rtypes (car ltypes) rtypes))
         ((mv names1 events1)
          (atc-uaconvert-values-rules-gen-loop-ltypes (cdr ltypes) rtypes)))
      (mv (append names names1) (append events events1))))

  (define atc-uaconvert-values-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-uaconvert-values-rules-gen-loop-ltypes
           *nonchar-integer-types**
           *nonchar-integer-types**)))
      `(progn
         (defsection atc-uaconvert-values-rules
           :short "Rules about @(tsee uaconvert-values)
                   on values of given types."
           :long
           (xdoc::topstring
            (xdoc::p
             "These are not used during the symbolic execution;
              they are used to prove rules
              used during the symbolic execution."))
           ,@events
           (defval *atc-uaconvert-values-rules*
             '(,@names)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-uaconvert-values-rules-gen-all))
