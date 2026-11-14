; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../normalization")
(include-book "../quick-check")

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book defines a check, for EVERY code point, that the quick check
; properties of the Unicode Character Database (which this library reads
; from DerivedNormalizationProps.txt, and does not otherwise use)
; agree with the normalization functions of this library
; (which are computed from UnicodeData.txt and from the property
; Full_Composition_Exclusion).  The books quick-check-v<version>
; in this directory run it.
;
; For each code point CP we check that:
;
;   NFD_Quick_Check is No   exactly when NFD does not map (CP) to itself;
;   NFKD_Quick_Check is No  exactly when NFKD does not map (CP) to itself;
;   NFC_Quick_Check is No   exactly when NFC does not map (CP) to itself;
;   NFKC_Quick_Check is No  exactly when NFKC does not map (CP) to itself;
;   NFC_Quick_Check is Maybe, and NFKC_Quick_Check is Maybe, exactly when
;     the value is not No and some code point composes with the first
;     code point of the canonical decomposition of CP after it;
;   Full_Composition_Exclusion holds exactly when NFC_Quick_Check is No.
;
; About Maybe: usually the canonical decomposition of such a CP is CP itself,
; i.e. CP is the second code point of a pair that composes, like a combining
; accent.  But since Unicode 16.0.0 there are also primary composites whose
; decompositions start with such a code point: for example U+16D68 maps to
; U+16D67 U+16D67, and U+16D63 U+16D67 composes to U+16D69; so the NFC form
; of U+16D63 U+16D68 is not that sequence (it is U+16D6A), and the value
; for U+16D68 is Maybe.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The second code points of the pairs of a composition map.

(define composition-map-seconds ((map nat-map-p))
  :returns (seconds nat-listp)
  (cond ((endp map) nil)
        (t (cons (nfix (floor (nfix (car (car map))) #x110000))
                 (composition-map-seconds (cdr map)))))
  :hooks nil
  :verify-guards :after-returns)

(define composes-after-something-p ((cp natp) (seconds nat-listp))
  :returns (yes/no booleanp)
  (or (hangul-v-p cp)
      (hangul-t-p cp)
      (and (member (lnfix cp) seconds) t))
  :hooks nil)

(define quick-check-agrees-p ((cp code-point-p)
                              (seconds nat-listp)
                              (ver versionp))
  :returns (yes/no booleanp)
  (b* ((cps (list cp))
       (nfd-no (equal (nfd-quick-check cp ver) :no))
       (nfkd-no (equal (nfkd-quick-check cp ver) :no))
       (nfc (nfc-quick-check cp ver))
       (nfkc (nfkc-quick-check cp ver))
       (composes (composes-after-something-p (nfix (car (nfd cps ver)))
                                             seconds)))
    (and (equal nfd-no (not (equal (nfd cps ver) cps)))
         (equal nfkd-no (not (equal (nfkd cps ver) cps)))
         (equal (equal nfc :no) (not (equal (nfc cps ver) cps)))
         (equal (equal nfkc :no) (not (equal (nfkc cps ver) cps)))
         (equal (equal nfc :maybe)
                (and composes (not (equal nfc :no))))
         (equal (equal nfkc :maybe)
                (and composes (not (equal nfkc :no))))
         (equal (full-composition-exclusion-p cp ver)
                (equal nfc :no))))
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable code-point-p))))

; Go through all the code points from CP on.
; Return the code points that fail, most recent first.

(define quick-check-failures-from ((cp natp)
                                   (seconds nat-listp)
                                   (ver versionp)
                                   (failures true-listp))
  :returns (new-failures true-listp :hyp (true-listp failures))
  (b* (((unless (mbt (natp cp))) failures)
       ((when (> cp #x10FFFF)) failures))
    (quick-check-failures-from
     (+ 1 cp)
     seconds
     ver
     (if (quick-check-agrees-p cp seconds ver)
         failures
       (cons cp failures))))
  :measure (nfix (- #x110000 (nfix cp)))
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable code-point-p))))

; The whole check: the list of the code points that fail.

(define quick-check-failures ((ver versionp))
  :returns (failures true-listp)
  (quick-check-failures-from 0
                             (composition-map-seconds (composition-map ver))
                             ver
                             nil)
  :hooks nil)
