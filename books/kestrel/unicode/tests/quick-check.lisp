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

(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

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

; The second code points of the canonical decomposition mappings
; of the primary composites among the code points of a list,
; without repetitions.
; (The precomposed Hangul syllables are not in the map of the mappings;
; their second code points are the vowels and the trailing consonants.)

(define composition-seconds ((cps code-point-listp)
                             (ver versionp)
                             (seconds code-point-listp))
  :returns (new-seconds code-point-listp :hints (("Goal" :induct t)))
  (b* ((seconds (code-point-list-fix seconds))
       ((when (endp cps)) seconds)
       (cp (code-point-fix (car cps)))
       (mapping (decomposition-map-lookup cp (canonical-mappings ver)))
       (seconds (if (and (equal (len mapping) 2)
                         (not (full-composition-exclusion-p cp ver))
                         (not (member-equal (second mapping) seconds)))
                    (cons (second mapping) seconds)
                  seconds)))
    (composition-seconds (cdr cps) ver seconds))
  :hooks nil
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable len))))

(define composes-after-something-p ((cp code-point-p)
                                    (seconds code-point-listp))
  :returns (yes/no booleanp)
  (or (hangul-v-p cp)
      (hangul-t-p cp)
      (and (member-equal (code-point-fix cp) seconds) t))
  :hooks nil)

(define quick-check-agrees-p ((cp code-point-p)
                              (seconds code-point-listp)
                              (ver versionp))
  :returns (yes/no booleanp)
  (b* ((cps (list cp))
       (nfd (quick-check-value-kind (nfd-quick-check cp ver)))
       (nfkd (quick-check-value-kind (nfkd-quick-check cp ver)))
       (nfc (quick-check-value-kind (nfc-quick-check cp ver)))
       (nfkc (quick-check-value-kind (nfkc-quick-check cp ver)))
       (nfd-cps (nfd cps ver))
       (composes (and (consp nfd-cps)
                      (composes-after-something-p (car nfd-cps) seconds))))
    (and (equal (equal nfd :no) (not (equal (nfd cps ver) cps)))
         (equal (equal nfkd :no) (not (equal (nfkd cps ver) cps)))
         (equal (equal nfc :no) (not (equal (nfc cps ver) cps)))
         (equal (equal nfkc :no) (not (equal (nfkc cps ver) cps)))
         (equal (equal nfc :maybe)
                (and composes (not (equal nfc :no))))
         (equal (equal nfkc :maybe)
                (and composes (not (equal nfkc :no))))
         (equal (full-composition-exclusion-p cp ver)
                (equal nfc :no))))
  :hooks nil)

; Go through the code points of a list.
; Return the code points that fail, most recent first.

(define quick-check-failures-among ((cps code-point-listp)
                                    (seconds code-point-listp)
                                    (ver versionp)
                                    (failures code-point-listp))
  :returns (new-failures code-point-listp :hints (("Goal" :induct t)))
  (b* ((failures (code-point-list-fix failures))
       ((when (endp cps)) failures)
       (cp (code-point-fix (car cps))))
    (quick-check-failures-among
     (cdr cps)
     seconds
     ver
     (if (quick-check-agrees-p cp seconds ver)
         failures
       (cons cp failures))))
  :hooks nil)

; The whole check: the list of the code points that fail.

(define quick-check-failures ((ver versionp))
  :returns (failures code-point-listp)
  (quick-check-failures-among
   (all-code-points)
   (composition-seconds (all-code-points) ver nil)
   ver
   nil)
  :hooks nil)
