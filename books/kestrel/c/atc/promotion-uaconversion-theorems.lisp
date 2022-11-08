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

(include-book "../language/integer-operations")

(include-book "symbolic-execution-rules/integers")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection promotion-uaconversion-theorems
  :short "Two theorems about
          integer promotions and usual arithmetic conversions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These relate @(tsee promote-value) and @(tsee uaconvert-values)
     to the recognizers of integer values from the shallow embedding.
     They were previously used in certain proofs,
     but now they are only retained as validation theorems.
     Actually, they may just be removed at some point."))

  (defruled values-of-promote-value
    (implies (value-arithmeticp val)
             (b* ((pval (promote-value val)))
               (or (uintp pval)
                   (sintp pval)
                   (ulongp pval)
                   (slongp pval)
                   (ullongp pval)
                   (sllongp pval))))
    :use (:instance lemma (val (value-fix val)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (valuep val)
                     (value-arithmeticp val))
                (b* ((pval (promote-value val)))
                  (or (uintp pval)
                      (sintp pval)
                      (ulongp pval)
                      (slongp pval)
                      (ullongp pval)
                      (sllongp pval))))
       :disable (value-promoted-arithmeticp-of-promote-value
                 type-of-value-of-promote-value)
       :use (value-promoted-arithmeticp-of-promote-value
             type-of-value-of-promote-value)
       :enable (value-promoted-arithmeticp-alt-def
                type-of-value-when-uintp
                type-of-value-when-sintp
                type-of-value-when-ulongp
                type-of-value-when-slongp
                type-of-value-when-ullongp
                type-of-value-when-sllongp
                uintp-to-type-of-value
                sintp-to-type-of-value
                ulongp-to-type-of-value
                slongp-to-type-of-value
                ullongp-to-type-of-value
                sllongp-to-type-of-value))))

  (defruled values-of-uaconvert-values
    (implies (and (value-arithmeticp val1)
                  (value-arithmeticp val2))
             (b* (((mv cval1 cval2) (uaconvert-values val1 val2)))
               (or (and (uintp cval1) (uintp cval2))
                   (and (sintp cval1) (sintp cval2))
                   (and (ulongp cval1) (ulongp cval2))
                   (and (slongp cval1) (slongp cval2))
                   (and (ullongp cval1) (ullongp cval2))
                   (and (sllongp cval1) (sllongp cval2)))))
    :use (:instance lemma (val1 (value-fix val1)) (val2 (value-fix val2)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (valuep val1)
                     (valuep val2)
                     (value-arithmeticp val1)
                     (value-arithmeticp val2))
                (b* (((mv cval1 cval2) (uaconvert-values val1 val2)))
                  (or (and (uintp cval1) (uintp cval2))
                      (and (sintp cval1) (sintp cval2))
                      (and (ulongp cval1) (ulongp cval2))
                      (and (slongp cval1) (slongp cval2))
                      (and (ullongp cval1) (ullongp cval2))
                      (and (sllongp cval1) (sllongp cval2)))))
       :disable (value-promoted-arithmeticp-of-uaconvert-values
                 type-of-value-of-uaconvert-values)
       :use (value-promoted-arithmeticp-of-uaconvert-values
             type-of-value-of-uaconvert-values)
       :enable (value-promoted-arithmeticp-alt-def
                type-of-value-when-uintp
                type-of-value-when-sintp
                type-of-value-when-ulongp
                type-of-value-when-slongp
                type-of-value-when-ullongp
                type-of-value-when-sllongp
                uintp-to-type-of-value
                sintp-to-type-of-value
                ulongp-to-type-of-value
                slongp-to-type-of-value
                ullongp-to-type-of-value
                sllongp-to-type-of-value)))))
