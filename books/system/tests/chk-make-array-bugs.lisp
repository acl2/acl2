; This book was produced by Claude and passed along by Eric Smith.  It tests
; the fix, made before the release of ACL2 Version 8.8, for two bugs in raw
; Lisp function chk-make-array$; see https://github.com/acl2/acl2/pull/2083.

; Chk-make-array$ checks the dimensions given to make-array$ against the host
; Lisp's array-dimension-limit and array-total-size-limit.  Its loop over the
; dimensions checked (car dimensions) every time instead of each dimension in
; turn, and its loop computing the product of the dimensions multiplied by
; (car dimensions) every time.  Only two-dimensional arrays were affected,
; since compress2 is the only caller of make-array$ that passes a list of
; dimensions.  Array2p, the guard of compress2, requires both dimensions to be
; positive, but it allows dimensions far beyond the host Lisp's limits.

; Before the fix, the two must-fail forms below passed chk-make-array$ and then
; called make-array, which caused a raw Lisp error (heap exhaustion in SBCL, an
; allocation error in CCL).  Must-fail does not catch raw Lisp errors, so this
; book failed to certify.  Now chk-make-array$ causes an ACL2 error.  The
; must-succeed form below was rejected before the fix (in SBCL on x86-64)
; though its dimensions are legal.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)

; Record the host Lisp's array limits.  This requires a trust tag, but the
; tests below do not.
(defttag :host-array-limits)
(progn! (set-raw-mode t)
        (f-put-global 'host-array-dimension-limit array-dimension-limit state)
        (f-put-global 'host-array-total-size-limit array-total-size-limit
                      state))
(defttag nil)

(make-event `(defconst *dimension-limit* ,(@ host-array-dimension-limit)))
(make-event `(defconst *total-size-limit* ,(@ host-array-total-size-limit)))

; In a Lisp whose limits are so large that the headers below violate the
; array2p bounds (e.g., some older versions of SBCL), the two must-fail forms
; fail for that reason instead, without allocating anything.

; The second dimension is too large; formerly only the first was checked.
(must-fail
 (defconst *wide*
   (compress2 'wide
              `((:header :dimensions (1 ,*dimension-limit*)
                         :maximum-length ,(+ 1 *dimension-limit*)
                         :default 0
                         :name wide)))))

; Each dimension is legal but their product is too large; formerly the product
; was computed as 2*2.
(must-fail
 (defconst *big*
   (compress2 'big
              `((:header :dimensions (2 ,(ceiling *total-size-limit* 2))
                         :maximum-length ,(+ 1 (* 2 (ceiling *total-size-limit*
                                                             2)))
                         :default 0
                         :name big)))))

; A tall, thin array, which is legal but was formerly rejected because the
; product of its dimensions was computed as rows*rows.  We pick the least power
; of 2 whose square is at least the total size limit (2^22 for SBCL on x86-64),
; and we skip this test if that power is too large to allocate cheaply (as for
; CCL, where it is 2^28).
(defconst *tall-rows*
  (expt 2 (ceiling (integer-length (1- *total-size-limit*)) 2)))

(make-event
 (if (<= *tall-rows* (expt 2 22))
     `(must-succeed
       (defconst *tall*
         (compress2 'tall
                    '((:header :dimensions (,*tall-rows* 1)
                               :maximum-length ,(+ 1 *tall-rows*)
                               :default 0
                               :name tall)))))
   '(value-triple :skipped)))
