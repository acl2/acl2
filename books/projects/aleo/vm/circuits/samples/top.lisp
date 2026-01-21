; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Older form of JSON from snarkVM. (v1)
; Note that this uses
;   gadget-json-to-r1cs-defagg.lisp
; When we modernize this boolean gadget checking we can
; move that to old/.
(include-book "boolean-json")
(include-book "boolean")

(include-book "field-message-json-auto")
(include-book "group-message-json-auto")

; Fetch using git lfs and then unzip:
;(include-book "u64-message-json-auto")
;(include-book "i64-message-json-auto")
;(include-book "u128-message-json-auto")
;(include-book "i128-message-json-auto")

; 2024-05: call these new for now; combine later
; Don't include them yet, but let cert.pl see them
#||
(include-book "i8-message-json-auto-new")
; Fetch using git lfs and then unzip:
;(include-book "i64-message-json-auto-new")
;(include-book "i128-message-json-auto-new")
||#

; moved to gadgets/old/samples/, but plan to use parts of it soon:
;  (include-book "field-gadget-tests")

(include-book "field-samples")
(include-book "field-div")
(include-book "field-inverse")
(include-book "field-pow")
(include-book "field-to-bits-le-new")
(include-book "field-compare-new")
(include-book "field-neq")
(include-book "field-mul")
(include-book "field-square")
(include-book "field-ternary")
(include-book "field-from-bits-le-new")

(include-book "group-samples")

; i8-samples is WIP
;(include-book "i8-samples")
; 2024-05: The following need to be updated due to circuit changes; see above

; Fetch using git lfs and then unzip:
;(include-book "u64-samples")
;(include-book "i64-samples")
;(include-book "u128-samples")
;(include-book "i128-samples")
;(include-book "i128-samples-new")

(include-book "poseidon-samples")

(include-book "sha3-component-samples")

; Fetch using git lfs and then unzip:
;(include-book "sha3-message-json-auto")
;(include-book "keccak256-permutation-f-json-auto"
;(include-book "sha3-samples")

(include-book "cast-samples")

; pre- and post-optimization samples of shift operations on u8 and i8.
; 2024-05-17 remove soon; a new i8-shift will be coming above
(include-book "shift-sample-compares")
