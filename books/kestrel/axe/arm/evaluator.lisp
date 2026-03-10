; An evaluator for ARM code lifting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; change to A package?

;; (include-book "kestrel/arm/decoder" :dir :system)
(include-book "../evaluator-basic")
(include-book "../unguarded-built-ins") ; for nth-unguarded
(include-book "../unguarded-defuns2") ; for binary-logand-unguarded
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)
(local (include-book "kestrel/bv/bitops" :dir :system))
;(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "kestrel/bv/logapp" :dir :system)) ; for loghead-becomes-bvchop

(local
  (in-theory (disable rational-listp
                      integer-listp
                      assoc-equal
                      min
                      max
                      integer-range-p
                      signed-byte-p
                      bvle)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: import more of these into the R package, if needed:
(defconst *axe-evaluator-arm-fns-and-aliases*
  (append '(implies ; push back to basic evaluator?
             ;; arm::arm32-decode ; todo: problem with mv
            ;; (integer-range-p integer-range-p-unguarded)
            ;; (bitops::part-select-width-low$inline bitops::part-select-width-low$inline-unguarded)
            ;; (lookup lookup-equal-unguarded)
            ;; (loghead$inline loghead$inline-unguarded)
            ;; (logapp logapp-unguarded) ; for flags
            ;; (acl2::packbv acl2::packbv-unguarded)
            ;; (bv-array-read-chunk-little bv-array-read-chunk-little-unguarded)
            ;; power-of-2p
            ;; logmaskp
            ;; bfix$inline
            ;; bool->bit$inline
            ;; (evenp evenp-unguarded)
            ;; (logcount logcount-unguarded)
            ;; (logtail$inline logtail$inline-unguarded)
            ;; (zip zip-unguarded)
            ;; (ash ash-unguarded)
            ;; (acl2::firstn acl2::firstn-unguarded)
            ;; (logbitp logbitp-unguarded)
            (binary-logand binary-logand-unguarded)
            ;; (binary-logior binary-logior-unguarded)
            ;; (nonnegative-integer-quotient nonnegative-integer-quotient-unguarded)
            ;; (acl2::aref1 acl2::aref1-unguarded)
            ;; (acl2::negated-elems-listp acl2::negated-elems-listp-unguarded)
            )
          *axe-evaluator-basic-fns-and-aliases*))

;; Creates acl2::eval-axe-evaluator-arm, etc. ;; todo: package
;; Makes the evaluator (also checks that each alias given is equivalent to its function):
(make-evaluator-simple arm *axe-evaluator-arm-fns-and-aliases*)
