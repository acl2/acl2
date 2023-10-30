; A formal specification of the SHA-3 hash function
;
; Copyright (C) 2019-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SHA3")

;; Written from the FIPS-202 standard.

;; See also validation proofs in sha-3-validation.lisp.

;; TODO: Add the Keccak functions.

(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/lists-light/group" :dir :system)
(include-book "kestrel/lists-light/ungroup" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bitand" :dir :system)
(include-book "kestrel/arithmetic-light/lg" :dir :system)
(include-book "kestrel/bv-lists/bvxor-list" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/lists-light/memberp" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes-little" :dir :system)
(include-book "kestrel/bv-lists/bytes-to-bits-little" :dir :system)
;todo: reduce some of this?:
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
;(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/typed-lists-light/all-integerp-of-repeat" :dir :system))
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/firstn" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system)) ;for MOD-OF-*-SUBST-CONSTANT-ARG2
(local (include-book "kestrel/lists-light/group-and-ungroup" :dir :system))
(local (include-book "support"))

;(local (in-theory (disable acl2::group-becomes-group2)))

(local (in-theory (disable true-listp ;prevent inductions
                           bitp)))

(local (in-theory (disable acl2::mod-sum-cases))) ;avoid case splits

;(local (in-theory (disable acl2::update-nth-of-update-nth-becomes-update-subrange)))

(local (in-theory (disable acl2::len-of-group)))

(local (in-theory (enable acl2::memberp-of-cons-when-constant)))

(local
  (defthm bitp-when-unsigned-byte-p-1
    (implies (unsigned-byte-p 1 x)
             (bitp x))
    :hints (("Goal" :in-theory (enable bitp unsigned-byte-p)))))

;; The supported values for b, the width of the Keccak-p permutation, in bits
;; (see Section 2.2 and Table 1)
(defconst *b-vals* '(25 50 100 200 400 800 1600))

;; The supported values for w, the lane size, in bits (see Section 2.2 and
;; Table 1)
(defconst *w-vals* '(1 2 4 8 16 32 64))

;; The supported values for l, the binary logarithm of the lane size, in bits
;; (see Section 2.2 and Table 1)
(defconst *l-vals* '(0 1 2 3 4 5 6))

(defund w-valp (w)
  (declare (xargs :guard t))
  (memberp w *w-vals*))

(defthm w-valp-forward-to-posp
  (implies (w-valp w)
           (posp w))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable w-valp memberp))))

(defthm w-valp-forward-to-<=-64
  (implies (w-valp w)
           (<= w 64))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable w-valp memberp))))

;; Recognize a string of bits.  Bits are numbered starting at 0 and can be
;; accessed with nth.  See the definition of X[i] in Sec 2.3.
(defun bit-stringp (bit-string)
  (declare (xargs :guard t))
  (and (true-listp bit-string)
       (all-unsigned-byte-p 1 bit-string)))

(defthm bit-stringp-of-repeat-of-0
  (bit-stringp (repeat n '0))
  :hints (("Goal" :in-theory (enable bit-stringp))))

;; ;; Like nth but has a stricter guard.
;; (defun bit-n (n bit-string)
;;   (declare (type (integer 0 *) n)
;;            (xargs :guard (and (bit-stringp bit-string)
;;                               (< n (len bit-string)))))
;;   (nth n bit-string))

;; A lane is a list of w bits.
(defund lanep (lane w)
  (declare (xargs :guard (w-valp w)))
  (and (bit-stringp lane)
       (equal w (len lane))))

(defthm lanep-forward-to-true-listp
  (implies (lanep lane w)
           (true-listp lane))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable lanep))))

(defthm len-when-lanep
  (implies (lanep lane w)
           (equal (len lane)
                  w))
  :hints (("Goal" :in-theory (enable lanep))))

;; Extract the nth bit from the given lane
(defund nth-bit (n lane w)
  (declare (xargs :guard (and (w-valp w)
                              (lanep lane w)
                              (natp n)
                              (< n w))
                  :split-types t)
           (type (integer 0 63) n)
           (ignore w))
  (nth n lane))

(defthm integerp-of-nth-bit
  (implies (and (lanep lane w)
                (natp n)
                (< n (len lane)))
           (integerp (nth-bit n lane w)))
  :hints (("Goal" :in-theory (enable lanep nth-bit))))

(defthm unsigned-byte-p-1-of-nth-bit
  (implies (and (lanep lane w)
                (natp n)
                (< n (len lane)))
           (unsigned-byte-p 1 (nth-bit n lane w)))
  :hints (("Goal" :in-theory (enable lanep nth-bit))))

;; Recognize a true-list of lanes.
(defun lane-listp (lanes w)
  (declare (xargs :guard (w-valp w)))
  (if (atom lanes)
      (null lanes)
    (and (lanep (first lanes) w)
         (lane-listp (rest lanes) w))))

;might be slow
(defthm items-have-len-when-lane-listp
  (implies (lane-listp plane w)
           (items-have-len w plane)))

;; A plane is a list of 5 lanes.
(defund planep (plane w)
  (declare (xargs :guard (w-valp w)))
  (and (lane-listp plane w)
       (equal 5 (len plane))))

;might be slow
(defthm items-have-len-when-planep
  (implies (planep plane w)
           (items-have-len w plane))
  :hints (("Goal" :in-theory (enable planep))))

(defthm planep-forward-to-all-true-listp
  (implies (planep plane w)
           (all-true-listp plane))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable planep))))

(defthm planep-forward-to-true-listp
  (implies (planep plane w)
           (true-listp plane))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable planep))))

(defthm len-when-planep
  (implies (planep plane w)
           (equal (len plane)
                  5))
  :hints (("Goal" :in-theory (enable planep))))

;; Extract the nth lane from the given plane
(defund nth-lane (n plane w)
  (declare (xargs :guard (and (w-valp w)
                              (planep plane w)
                              (natp n)
                              (< n 5))
                  :split-types t)
           (type (integer 0 4) n))
  (declare (ignore w))
  (nth n plane))

(defthm lanep-of-nth-lane
  (implies (and (lane-listp lanes w)
                (natp n)
                (< n (len lanes)))
           (lanep (nth-lane n lanes w) w))
  :hints (("Goal" :in-theory (enable nth-lane nth))))

(defthm all-unsigned-byte-p-of-nth-lane
  (implies (and (lane-listp lanes w)
                (natp n)
                (< n (len lanes)))
           (all-unsigned-byte-p 1 (nth-lane n lanes w)))
  :hints (("Goal" :in-theory (enable nth-lane nth lanep))))

(defthm len-of-nth-lane
  (implies (and (lane-listp lanes w)
                (natp n)
                (< n (len lanes)))
           (equal (len (nth-lane n lanes w))
                  w))
  :hints (("Goal" :in-theory (enable nth-lane nth lanep))))

;; Recognize a true-list of planes.
(defun plane-listp (planes w)
  (declare (xargs :guard (w-valp w)))
  (if (atom planes)
      (null planes)
    (and (planep (first planes) w)
         (plane-listp (rest planes) w))))

;; A state-array is a list of 5 planes.  We choose this representation because
;; the conversions between bit strings and the state array (Sections 3.1.2 and
;; 3.1.3) use planes as the first unit of decomposition of the state.  For
;; example, in Section 3.1.3, all of the bits from plane 0 (indicated by a
;; y-coordinate of 0) precede the bits from any other plane.  And in Section
;; 3.1.3, the serialized state is defined in terms of the serializations of the
;; 5 planes.  (The theta transformation is also plane-based.)  A consequence of
;; this decision is that various computations in this specification use the y
;; dimension (that is, the plane number) as the outermost loop, rather than the
;; x dimension as might be expected.

(defund state-arrayp (a w)
  (declare (xargs :guard (w-valp w)))
  (and (plane-listp a w)
       (equal 5 (len a))))

;; might be slow
(defthm len-when-state-arrayp
  (implies (state-arrayp a w)
           (equal (len a)
                  5))
  :hints (("Goal" :in-theory (enable state-arrayp))))

(defthm state-arrayp-forward-to-true-listp
  (implies (state-arrayp a w)
           (true-listp a))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable state-arrayp))))

;; Extract the nth plane from the state array
(defund nth-plane (n a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w)
                              (natp n)
                              (< n 5))))
  (declare (ignore w))
  (nth n a))

(defthm planep-of-nth-plane
  (implies (and (plane-listp planes w)
                (natp n)
                (< n (len planes)))
           (planep (nth-plane n planes w) w))
  :hints (("Goal" :in-theory (enable nth-plane nth))))

(defthm len-of-nth-plane
  (implies (and (plane-listp planes w)
                (natp n)
                (< n (len planes)))
           (equal (len (nth-plane n planes w))
                  5))
  :hints (("Goal" :in-theory (enable nth-plane nth))))

;; Convert a bit-string to a plane.
(defund bit-string-to-plane (bits w)
  (declare (xargs :guard (and (w-valp w)
                              (bit-stringp bits)
                              (equal (len bits) (* 5 w)))))
  (group w bits))

(defthm lane-listp-of-group
  (implies (and (natp w)
                (true-listp bits)
                (all-unsigned-byte-p 1 bits)
                (force (equal 0 (mod (len bits) w))))
           (lane-listp (group w bits) w))
  :hints (("Goal" :in-theory (enable group lane-listp lanep))))

(defthm planep-of-bit-string-to-plane
  (implies (and (posp w)
                (bit-stringp bits)
                (equal (len bits) (* 5 w)))
           (planep (bit-string-to-plane bits w) w))
  :hints (("Goal" :in-theory (enable group planep lane-listp
                                     bit-string-to-plane))))

;; Convert a plane to a bit-string
(defund plane-to-bit-string (plane w)
  (declare (xargs :guard (and (w-valp w)
                              (planep plane w))
                  :guard-hints (("Goal" :in-theory (enable acl2::true-listp-of-car-when-all-true-listp)))))
  (ungroup w plane) ;or call flatten?
  )

(defthm len-of-plane-to-bit-string
  (implies (and (planep plane w)
                (posp w))
           (equal (len (plane-to-bit-string plane w))
                  (* 5 w)))
  :hints (("Goal" :in-theory (enable plane-to-bit-string PLANEP))))

(defthm all-unsigned-byte-p-of-ungroup-3
  (implies (lane-listp plane w)
           (all-unsigned-byte-p 1 (ungroup w plane)))
  :hints (("Goal" :in-theory (enable ungroup lanep))))

(defthm bit-stringp-of-plane-to-bit-string
  (implies (planep plane w)
           (bit-stringp (plane-to-bit-string plane w)))
  :hints (("Goal" :in-theory (enable plane-to-bit-string planep))))

(defthm plane-to-bit-string-of-bit-string-to-plane
  (implies (and (posp w)
                (bit-stringp bits)
                (equal (len bits) (* 5 w)))
           (equal (plane-to-bit-string (bit-string-to-plane bits w) w)
                  bits))
  :hints (("Goal" :in-theory (enable plane-to-bit-string bit-string-to-plane))))

(defthm bit-string-to-plane-of-plane-to-bit-string
  (implies (and (posp w)
                (planep plane w))
           (equal (bit-string-to-plane (plane-to-bit-string plane w) w)
                  plane))
  :hints (("Goal" :in-theory (enable plane-to-bit-string bit-string-to-plane))))

;;
;; converting between bit-strings and the state-array
;;

(defund all-bit-stringp (bit-strings)
  (declare (xargs :guard t))
  (if (consp bit-strings)
      (and (bit-stringp (first bit-strings))
           (all-bit-stringp (rest bit-strings)))
    t))

(defthm all-bit-stringp-of-cdr
  (implies (all-bit-stringp bit-strings)
           (all-bit-stringp (cdr bit-strings)))
  :hints (("Goal" :in-theory (enable all-bit-stringp))))

(defthm all-bit-stringp-of-cons
  (equal (all-bit-stringp (cons a x))
         (and (bit-stringp a)
              (all-bit-stringp x)))
  :hints (("Goal" :in-theory (enable all-bit-stringp))))

(defthm all-bit-stringp-of-append
  (equal (all-bit-stringp (append x y))
         (and (all-bit-stringp x)
              (all-bit-stringp y)))
  :hints (("Goal" :in-theory (enable all-bit-stringp))))

(defthm true-listp-of-car-when-all-bit-stringp
  (implies (all-bit-stringp bit-strings)
           (true-listp (car bit-strings)))
  :hints (("Goal" :in-theory (enable all-bit-stringp))))

(defthm all-unsigned-byte-p-of-car-when-all-bit-stringp
  (implies (all-bit-stringp bit-strings)
           (all-unsigned-byte-p 1 (car bit-strings)))
  :hints (("Goal" :in-theory (enable all-bit-stringp))))

(defthm all-integerp-of-nth-when-all-bit-stringp
  (implies (all-bit-stringp bit-strings)
           (all-integerp (nth n bit-strings)))
  :hints (("Goal" :in-theory (enable all-bit-stringp nth))))

(defthm true-listp-of-nth-when-all-bit-stringp
  (implies (all-bit-stringp bit-strings)
           (true-listp (nth n bit-strings)))
  :hints (("Goal" :in-theory (enable all-bit-stringp nth))))

;; Turn each of the given bit-strings into a plane.
(defun map-bit-string-to-plane (bit-strings w)
  (declare (xargs :guard (and (w-valp w)
                              (all-bit-stringp bit-strings)
                              (true-listp bit-strings)
                              (items-have-len (* 5 w) bit-strings))))
  (if (endp bit-strings)
      nil
    (cons (bit-string-to-plane (first bit-strings) w)
          (map-bit-string-to-plane (rest bit-strings) w))))

(defthm len-of-map-bit-string-to-plane
  (equal (len (map-bit-string-to-plane bit-strings w))
         (len bit-strings)))

(defthm all-bit-stringp-of-group
  (implies (bit-stringp bit-string)
           (all-bit-stringp (group n bit-string)))
  :hints (("Goal" :in-theory (enable group))))

;; Turn each of the given planes into a bit-string.
(defun map-plane-to-bit-string (planes w)
  (declare (xargs :guard (and (w-valp w)
                              (plane-listp planes w))))
  (if (endp planes)
      nil
    (cons (plane-to-bit-string (first planes) w)
          (map-plane-to-bit-string (rest planes) w))))

(defthm len-of-map-plane-to-bit-string
  (equal (len (map-plane-to-bit-string planes w))
         (len planes)))

(defthm items-have-len-of-map-plane-to-bit-string
  (implies (and (plane-listp planes w)
                (posp w))
           (items-have-len (* 5 w)
                           (map-plane-to-bit-string planes w)))
  :hints (("Goal" :in-theory (enable planep))))

(defthm all-bit-stringp-of-map-plane-to-bit-string
  (implies (and (plane-listp planes w)
                (posp w))
           (all-bit-stringp (map-plane-to-bit-string planes w))))

(defthm all-true-listp-of-map-plane-to-bit-string
  (implies (and (plane-listp planes w)
                (posp w))
           (all-true-listp (map-plane-to-bit-string planes w))))

;; Convert a bit-string to a state-array (Sec 3.1.2)
(defund bits-to-state-array (bits w)
  (declare (xargs :guard (and (w-valp w)
                              (bit-stringp bits)
                              (equal (len bits) (* 25 w)))))
  (map-bit-string-to-plane (group (* 5 w) bits) w))

(defthm bit-stringp-of-car
  (implies (all-bit-stringp bit-strings)
           (bit-stringp (car bit-strings))))

(defthm plane-listp-of-map-bit-string-to-plane
  (implies  (and (posp w)
                 (all-bit-stringp bit-strings)
                 (true-listp bit-strings)
                 (items-have-len (* 5 w) bit-strings))
            (plane-listp (map-bit-string-to-plane bit-strings w) w)))

(defthm state-arrayp-of-bits-to-state-array
  (implies (and (posp w)
                (bit-stringp bits)
                (equal (len bits) (* 25 w)))
           (state-arrayp (bits-to-state-array bits w) w))
  :hints (("Goal" :in-theory (enable state-arrayp bits-to-state-array))))

;; Convert a state-array to a bit-string (Sec 3.1.3)
(defund state-array-to-bits (a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w))
                  :guard-hints (("Goal" :in-theory (enable state-arrayp)))))
  (ungroup (* 5 w) (map-plane-to-bit-string a w)))

(defthm all-unsigned-byte-p-of-ungroup-4
  (implies (and (all-bit-stringp bit-strings)
                (items-have-len w bit-strings))
           (all-unsigned-byte-p 1 (ungroup w bit-strings)))
  :hints (("Goal" :in-theory (enable ungroup))))

(defthm bit-stringp-of-state-array-to-bits
  (implies (and (state-arrayp a w)
                (posp w))
           (bit-stringp (state-array-to-bits a w)))
  :hints (("Goal" :in-theory (enable state-array-to-bits state-arrayp))))

(defthm all-unsigned-byte-p-of-state-array-to-bits
  (implies (and (state-arrayp a w)
                (posp w))
           (all-unsigned-byte-p 1 (state-array-to-bits a w)))
  :hints (("Goal" :use (:instance bit-stringp-of-state-array-to-bits)
           :in-theory (disable bit-stringp-of-state-array-to-bits))))

(defthm len-of-state-array-to-bits
 (implies (and (w-valp w)
               (state-arrayp a w))
          (equal (len (state-array-to-bits a w))
                 (* 25 w)))
 :hints (("Goal" :in-theory (enable state-array-to-bits))))

(defthm map-plane-to-bit-string-of-map-bit-string-to-plane
  (implies (and (posp w)
                (all-bit-stringp bit-strings)
                (true-listp bit-strings)
                (items-have-len (* 5 w) bit-strings))
           (equal (map-plane-to-bit-string (map-bit-string-to-plane bit-strings w) w)
                  bit-strings)))

(defthm map-bit-string-to-plane-of-map-plane-to-bit-string
  (implies (and (posp w)
                (plane-listp planes w))
           (equal (map-bit-string-to-plane (map-plane-to-bit-string planes w) w)
                  planes)))

(defthm state-array-to-bits-of-bits-to-state-array
  (implies (and (posp w)
                (bit-stringp bits)
                (equal (len bits) (* 25 w)))
           (equal (state-array-to-bits (bits-to-state-array bits w) w)
                  bits))
  :hints (("Goal" :in-theory (enable state-array-to-bits bits-to-state-array))))

(defthm bits-to-state-array-of-state-array-to-bits
  (implies (and (posp w)
                (state-arrayp a w))
           (equal (bits-to-state-array (state-array-to-bits a w) w)
                  a))
  :hints (("Goal" :in-theory (enable state-arrayp state-array-to-bits bits-to-state-array))))

(defthm lane-listp-when-planep
  (implies (planep plane w)
           (lane-listp plane w))
  :hints (("Goal" :in-theory (enable planep))))

(theory-invariant (incompatible (:rewrite lane-listp-when-planep) (:definition planep)))

(defthm plane-listp-when-state-arrayp
  (implies (state-arrayp a w)
           (plane-listp a w))
  :hints (("Goal" :in-theory (enable state-arrayp))))

(theory-invariant (incompatible (:rewrite plane-listp-when-state-arrayp) (:definition state-arrayp)))

;; Extracts the single bit A[x,y,z] from the state.
(defund a (x y z a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w)
                              (natp x)
                              (< x 5)
                              (natp y)
                              (< y 5)
                              (natp z)
                              (< z w))))
  (nth-bit z (nth-lane x (nth-plane y a w) w) w))

;needed?
(defthm unsigned-byte-p-1-of-a
  (implies (and (w-valp w)
                (state-arrayp a w)
                (natp x)
                (< x 5)
                (natp y)
                (< y 5)
                (natp z)
                (< z w))
           (unsigned-byte-p 1 (a x y z a w)))
  :hints (("Goal" :in-theory (enable a))))

(defthm bitp-of-a
  (implies (and (w-valp w)
                (state-arrayp a w)
                (natp x)
                (< x 5)
                (natp y)
                (< y 5)
                (natp z)
                (< z w))
           (bitp (a x y z a w)))
  :hints (("Goal" :use (:instance unsigned-byte-p-1-of-a)
           :in-theory (disable unsigned-byte-p-1-of-a))))

(defthm integerp-of-a
  (implies (and (w-valp w)
                (state-arrayp a w)
                (natp x)
                (< x 5)
                (natp y)
                (< y 5)
                (natp z)
                (< z w))
           (integerp (a x y z a w)))
  :hints (("Goal" :use (:instance unsigned-byte-p-1-of-a)
           :in-theory (disable unsigned-byte-p-1-of-a))))

;;todo: explicit section 3.1.3 checks

;;;
;;; the theta step mapping (Sec 3.2.1)
;;;

;; Compute bits z through w-1 of lane x of C.
(defund theta-c-lane (z x a w)
  (declare (xargs :guard (and (w-valp w)
                              (natp z)
                              (natp x)
                              (< x 5)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- w z)))))
  (if (or (not (mbt (natp z)))
          (not (mbt (natp w)))
          (<= w z))
      nil
    (cons (bitxor$ (a x 0 z a w)
                   (bitxor$ (a x 1 z a w)
                            (bitxor$ (a x 2 z a w)
                                     (bitxor$ (a x 3 z a w)
                                              (a x 4 z a w)))))
          (theta-c-lane (+ 1 z) x a w))))

(defthm bit-stringp-of-theta-c-lane
  (implies (and (state-arrayp a w)
                (posp w))
           (bit-stringp (theta-c-lane z x a w)))
  :hints (("Goal" :in-theory (enable theta-c-lane))))

(defthm len-of-theta-c-lane
  (implies (and (state-arrayp a w)
                (posp w)
                (natp z))
           (equal (len (theta-c-lane z x a w))
                  (nfix (- w z))))
  :hints (("Goal" :in-theory (enable theta-c-lane))))

;; Compute lanes x through 4 of the plane representing C.
(defund theta-c-lanes (x a w)
  (declare (xargs :guard (and (natp x)
                              (w-valp w)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- 5 x)))))
  (if (or (not (mbt (natp x)))
          (<= 5 x))
      nil
    (cons (theta-c-lane 0 x a w)
          (theta-c-lanes (+ 1 x) a w))))

(defthm lane-listp-of-theta-c-lanes
  (implies (and (state-arrayp a w)
                (w-valp w))
           (lane-listp (theta-c-lanes x a w) w))
  :hints (("Goal" :in-theory (enable lanep theta-c-lanes))))

(defthm len-of-theta-c-lanes
  (implies (and (w-valp w)
                (natp x))
           (equal (len (theta-c-lanes x a w))
                  (nfix (- 5 x))))
  :hints (("Goal" :in-theory (enable theta-c-lanes))))

;; Step 1 of Algorithm 1
(defun theta-c (a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w))))
  (theta-c-lanes 0 a w))

;; Compute bits z through w-1 of lane x of D.
(defund theta-d-lane (z x c w)
  (declare (xargs :guard (and (natp z)
                              (natp x)
                              (w-valp w)
                              (planep c w))
                  :measure (nfix (+ 1 (- w z)))))
  (if (or (not (mbt (natp z)))
          (not (mbt (natp w)))
          (<= w z))
      nil
    (cons (bitxor$ (nth-bit z               (nth-lane (mod (- x 1) 5) c w) w)
                   (nth-bit (mod (- z 1) w) (nth-lane (mod (+ x 1) 5) c w) w))
          (theta-d-lane (+ 1 z) x c w))))

(defthm bit-stringp-of-theta-d-lane
  (implies (posp w)
           (bit-stringp (theta-d-lane z x c w)))
  :hints (("Goal" :in-theory (enable theta-d-lane))))

(defthm len-of-theta-d-lane
  (implies (and (posp w)
                (natp z))
           (equal (len (theta-d-lane z x c w))
                  (nfix (- w z))))
  :hints (("Goal" :in-theory (enable theta-d-lane))))

;; Compute lanes x through 4 of the plane representing D.
(defund theta-d-lanes (x c w)
  (declare (xargs :guard (and (natp x)
                              (w-valp w)
                              (planep c w))
                  :measure (nfix (+ 1 (- 5 x)))))
  (if (or (not (mbt (natp x)))
          (<= 5 x))
      nil
    (cons (theta-d-lane 0 x c w)
          (theta-d-lanes (+ 1 x) c w))))

(defthm lane-listp-of-theta-d-lanes
  (implies (w-valp w)
           (lane-listp (theta-d-lanes x c w) w))
  :hints (("Goal" :in-theory (e/d (lanep theta-d-lanes)
                                  ( ;bit-stringp
                                   )))))

(defthm len-of-theta-d-lanes
  (implies (and (w-valp w)
                (natp x))
           (equal (len (theta-d-lanes x c w))
                  (nfix (- 5 x))))
  :hints (("Goal" :in-theory (enable theta-d-lanes))))

;; Step 2 of Algorithm 1
(defund theta-d (c w)
  (declare (xargs :guard (and (w-valp w)
                              (planep c w))))
  (theta-d-lanes 0 c w))

(defthm lane-listp-of-theta-d
  (implies (w-valp w)
           (lane-listp (theta-d c w) w))
  :hints (("Goal" :in-theory (e/d (lanep theta-d)
                                  ()))))

(defthm len-of-theta-d
  (implies (w-valp w)
           (equal (len (theta-d c w))
                  5))
  :hints (("Goal" :in-theory (enable theta-d))))

;; Compute bits z through w-1 of lane (x,y) of theta.  Part of Step 3 of Algorithm 1.
(defund theta-lane (z x y a d w)
  (declare (xargs :guard (and (natp x)
                              (< x 5)
                              (natp y)
                              (< y 5)
                              (natp z)
                              (w-valp w)
                              (planep d w)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- w z)))))
  (if (or (not (mbt (natp z)))
          (not (mbt (natp w)))
          (<= w z))
      nil
    (cons (bitxor$ (a x y z a w)
                   (nth-bit z (nth-lane x d w) w))
          (theta-lane (+ 1 z) x y a d w))))

(defthm len-of-theta-lane
  (implies (and (state-arrayp a w)
                (posp w)
                (natp z))
           (equal (len (theta-lane z x y a d w))
                  (nfix (- w z))))
  :hints (("Goal" :in-theory (enable theta-lane))))

(defthm all-unsigned-byte-p-of-theta-lane
  (implies (and (state-arrayp a w)
                (posp w))
           (all-unsigned-byte-p 1 (theta-lane z x y a d w)))
  :hints (("Goal" :in-theory (enable theta-lane))))

(defthm lanep-of-theta-lane
  (implies (and (state-arrayp a w)
                (natp z)
                (posp w))
           (lanep (theta-lane 0 x y a d w) w))
  :hints (("Goal" :in-theory (enable lanep))))

;; Compute lanes x through 4 of plane y of theta.  Part of Step 3 of Algorithm 1.
(defund theta-lanes (x y a d w)
  (declare (xargs :guard (and (w-valp w)
                              (natp x)
                              (natp y)
                              (< y 5)
                              (planep d w)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- 5 x)))))
  (if (or (not (mbt (natp x)))
          (<= 5 x))
      nil
    (cons (theta-lane 0 x y a d w)
          (theta-lanes (+ 1 x) y a d w))))

(defthm len-of-theta-lanes
  (implies (and (w-valp w)
                (natp x))
           (equal (len (theta-lanes x y a d w))
                  (nfix (- 5 x))))
  :hints (("Goal" :in-theory (enable theta-lanes))))

(defthm lane-listp-of-theta-lanes
  (implies (and (w-valp w)
                (natp x)
                (state-arrayp a w))
           (lane-listp (theta-lanes x y a d w) w))
  :hints (("Goal" :in-theory (enable theta-lanes))))

;; Compute planes y through 4 of theta.  Part of Step 3 of Algorithm 1.
(defund theta-planes (y a d w)
  (declare (xargs :guard (and (natp y)
                              (w-valp w)
                              (planep d w)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- 5 y)))))
  (if (or (not (mbt (natp y)))
          (<= 5 y))
      nil
    (cons (theta-lanes 0 y a d w)
          (theta-planes (+ 1 y) a d w))))

(defun planes-n-induct (y a w n)
  (declare (xargs :measure (nfix (+ 1 (- 5 y)))))
  (if (or (not (mbt (natp y)))
          (<= 5 y))
      (list y a w n)
    (planes-n-induct (+ 1 y) a w (+ -1 n))))

(defthm len-of-theta-planes
  (implies (and (w-valp w)
                (state-arrayp a w)
                (natp y)
                (<= y 5))
           (equal (len (theta-planes y a d w))
                  (- 5 y)))
  :hints (("Goal" :induct (planes-n-induct y a w n)
           :in-theory (enable theta-planes))))

(defthm plane-listp-of-theta-planes
  (implies (and (w-valp w)
                (state-arrayp a w))
           (plane-listp (theta-planes y a d w) w))
  :hints (("Goal" :induct (planes-n-induct y a w n)
           :in-theory (e/d (theta-planes planep) (LANE-LISTP-WHEN-PLANEP)))))

;; The step mapping theta, specified in Algorithm 1 (Sec 3.2.1).
(defund theta (a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w))
                  :guard-hints (("Goal" :in-theory (e/d (PLANEP) (LANE-LISTP-WHEN-PLANEP))))
                  ))
  (let* ((c (theta-c a w))
         (d (theta-d c w)))
    (theta-planes 0 a d w)))

(defthm state-arrayp-of-theta
  (implies (and (state-arrayp a w)
                (w-valp w))
           (state-arrayp (theta a w) w))
  :hints (("Goal" :in-theory (e/d (theta STATE-ARRAYP) (PLANE-LISTP-WHEN-STATE-ARRAYP)))))

;;;
;;; the rho step mapping
;;;

;; Get lane (x,y) from the state array.
(defun get-lane (x y a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w)
                              (natp x)
                              (< x 5)
                              (natp y)
                              (< y 5))))
  (nth-lane x (nth-plane y a w) w))

;; Update the value of lane N in the given plane.
(defund update-nth-lane (n lane plane w)
  (declare (xargs :guard (and (w-valp w)
                              (planep plane w)
                              (natp n)
                              (< n 5)
                              (lanep lane w))))
  (declare (ignore w))
  (update-nth n lane plane))

(defthm lane-listp-of-update-nth-lane
  (implies (and (w-valp w)
                (lane-listp plane w)
                (natp n)
                (< n (len plane))
                (lanep lane w))
           (lane-listp (update-nth-lane n lane plane w)
                       w))
  :hints (("Goal" :in-theory (enable update-nth-lane update-nth lane-listp))))

(defthm len-of-update-nth-lane
  (implies (and (w-valp w)
                (equal 5 (len plane))
                (natp n)
                (< n 5)
                (lanep lane w))
           (equal (len (update-nth-lane n lane plane w))
                  5))
  :hints (("Goal" :in-theory (enable update-nth-lane update-nth lane-listp))))

(defthm planep-of-update-nth-lane
  (implies (and (w-valp w)
                (planep plane w)
                (natp n)
                (< n 5)
                (lanep lane w))
           (planep (update-nth-lane n lane plane w)
                   w))
  :hints (("Goal" :in-theory (e/d (planep) (lane-listp-when-planep)))))

;; Update the value of plane N in the state-array.
(defund update-nth-plane (n plane a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w)
                              (natp n)
                              (< n 5)
                              (planep plane w))))
  (declare (ignore w))
  (update-nth n plane a))

;; Set lane (x,y) in the state-array to the given lane.
(defund set-lane (x y lane a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w)
                              (natp x)
                              (< x 5)
                              (natp y)
                              (< y 5)
                              (lanep lane w))))
  (let* ((plane (nth-plane y a w))
         (new-plane (update-nth-lane x lane plane w)))
    (update-nth-plane y new-plane a w)))

(defthm len-of-update-nth-plane
  (implies (and (w-valp w)
                (natp n)
                (< n (len planes))
                )
           (equal (len (update-nth-plane n plane planes w))
                  (len planes)))
  :hints (("Goal" :in-theory (enable update-nth-plane update-nth lane-listp))))

(defthm len-of-set-lane
  (implies (and (natp y)
                (< y (len a))
                (w-valp w))
           (equal (len (set-lane x y lane a w))
                  (len a)))
  :hints (("Goal" :in-theory (enable set-lane))))

(defthm plane-listp-of-append
  (equal (plane-listp (append x y) w)
         (and (plane-listp (true-list-fix x) w)
              (plane-listp y w)))
  :hints (("Goal" :in-theory (enable plane-listp append))))

(defthm plane-listp-of-update-nth-plane
  (implies (and (w-valp w)
                (plane-listp planes w)
                (natp n)
                (< n (len planes))
                (planep plane w))
           (plane-listp (update-nth-plane n plane planes w)
                       w))
  :hints (("Goal" :in-theory (enable update-nth-plane update-nth plane-listp))))

(defthm plane-listp-of-set-lane
  (implies (and (w-valp w)
                (plane-listp a w)
                (natp x)
                (< x 5)
                (natp y)
                (< y (len a))
                (lanep lane w))
           (plane-listp (set-lane x y lane a w) w))
  :hints (("Goal" :in-theory (enable set-lane))))

;; Set bit N of the given lane to the given bit.
(defund update-nth-bit (n bit lane w)
  (declare (xargs :guard (and (w-valp w)
                              (unsigned-byte-p 1 bit)
                              (natp n)
                              (< n w)
                              (lanep lane w))))
  (declare (ignore w))
  (update-nth n bit lane))

(defthm lanep-of-update-nth-bit
  (implies (and (w-valp w)
                (unsigned-byte-p 1 bit)
                (natp n)
                (< n w)
                (lanep lane w))
           (lanep (update-nth-bit n bit lane w) w))
  :hints (("Goal" :in-theory (e/d (lanep update-nth-bit) ()))))

;; Set bit (x,y,z) in the state-array to the given bit.
(defund update-bit (x y z bit a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w)
                              (natp x)
                              (< x 5)
                              (natp y)
                              (< y 5)
                              (natp z)
                              (< z w)
                              (unsigned-byte-p 1 bit))))
  (let* ((lane (get-lane x y a w))
         (new-lane (update-nth-bit z bit lane w)))
    (set-lane x y new-lane a w)))

(defthm state-arrayp-of-update-bit
  (implies (and (w-valp w)
                (state-arrayp a w)
                (natp x)
                (< x 5)
                (natp y)
                (< y 5)
                (natp z)
                (< z w)
                (unsigned-byte-p 1 bit))
           (state-arrayp (update-bit x y z bit a w) w))
  :hints (("Goal" :in-theory (e/d (state-arrayp update-bit)
                                  (plane-listp-when-state-arrayp)))))

;move
(defthm even-helper
  (implies (integerp n)
           (integerp (+ (* 1/2 n) (* 1/2 n n))))
  :hints (("Goal" :in-theory (e/d (acl2::integerp-of-*-three)
                                  (acl2::evenp-of-+-when-odd-and-odd
                                   acl2::oddp-of-*-when-odd-and-odd))
           :use ((:instance acl2::oddp-of-*-when-odd-and-odd
                            (x n)
                            (y n))
                 (:instance acl2::evenp-of-+-when-odd-and-odd (x n)
                            (y (* N N))))
           :cases ((integerp (* 1/2 n))))))

;; Step 3a in Sec 3.2.2.
(defund rho-aux-aux (z t-var x y a-prime a w)
  (declare (xargs :guard (and (w-valp w)
                              (natp z)
                              (natp x)
                              (< x 5)
                              (natp y)
                              (< y 5)
                              (natp t-var)
                              (< t-var 24)
                              (state-arrayp a-prime w)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- w z)))))
  (if (or (not (mbt (natp z)))
          (not (mbt (natp w)))
          (<= w z))
      a-prime
    (let ((a-prime (update-bit x y z (a x y
                                        (mod (- z (* (+ t-var 1) (+ t-var 2) 1/2)) w)
                                        a w) a-prime w)))
      (rho-aux-aux (+ 1 z) t-var x y a-prime a w))))

(defthm state-arrayp-of-rho-aux-aux
  (implies (and (w-valp w)
                (natp z)
                (natp x)
                (< x 5)
                (natp y)
                (< y 5)
                (natp t-var)
                (state-arrayp a-prime w)
                (state-arrayp a w))
           (state-arrayp (rho-aux-aux z t-var x y a-prime a w) w))
  :hints (("Goal" :in-theory (enable rho-aux-aux))))

;; Step 3 in Sec 3.2.2.
(defun rho-aux (t-var x y a-prime a w)
  (declare (xargs :guard (and (w-valp w)
                              (natp t-var)
                              (<= t-var 24)
                              (natp x)
                              (< x 5)
                              (natp y)
                              (< y 5)
                              (state-arrayp a w)
                              (state-arrayp a-prime w))
                  :measure (nfix (+ 1 (- 24 t-var)))))
  (if (or (not (mbt (natp t-var)))
          (<= 24 t-var))
      a-prime
    (let ((a-prime (rho-aux-aux 0 t-var x y a-prime a w)))
      (mv-let (x y)
        (mv y (mod (+ (* 2 x) (* 3 y)) 5))
        (rho-aux (+ 1 t-var) x y a-prime a w)))))

(defthm state-arrayp-of-rho-aux
  (implies (and (w-valp w)
                (natp z)
                (natp x)
                (< x 5)
                (natp y)
                (< y 5)
                (state-arrayp a-prime w)
                (state-arrayp a w))
           (state-arrayp (rho-aux t-var x y a-prime a w) w))
  :hints (("Goal" :in-theory (enable rho-aux))))

;; The rho step mapping specified in Section 3.2.2.
(defund rho (a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w))))
  ;; nothing needs to be done for lane (0,0)
  (let ((a-prime a))
    (mv-let (x y)
      (mv 1 0)
      (rho-aux 0 x y a-prime a w))))

(defthm state-arrayp-of-rho
  (implies (and (w-valp w)
                (state-arrayp a w))
           (state-arrayp (rho a w) w))
  :hints (("Goal" :in-theory (enable rho))))

;;;
;;; The pi step mapping
;;;

;; Compute lanes x through 4 of plane y of pi.  Part of Step 1 of Algorithm 3.
(defund pi-lanes (x y a w)
  (declare (xargs :guard (and (w-valp w)
                              (natp x)
                              (natp y)
                              (< y 5)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- 5 x)))))
  (if (or (not (mbt (natp x)))
          (<= 5 x))
      nil
    (cons (get-lane (mod (+ x (* 3 y)) 5)
                    x a w)
          (pi-lanes (+ 1 x) y a w))))

(defthm len-of-pi-lanes
  (implies (and (w-valp w)
                (natp x))
           (equal (len (pi-lanes x y a w))
                  (nfix (- 5 x))))
  :hints (("Goal" :in-theory (enable pi-lanes))))

(defthm lane-listp-of-pi-lanes
  (implies (and (w-valp w)
                (natp x)
                (natp y)
                (state-arrayp a w))
           (lane-listp (pi-lanes x y a w) w))
  :hints (("Goal" :in-theory (enable pi-lanes))))

;; Compute planes y through 4 of pi. Part of Step 1 of Algorithm 3.
(defund pi-planes (y a w)
  (declare (xargs :guard (and (natp y)
                              (w-valp w)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- 5 y)))))
  (if (or (not (mbt (natp y)))
          (<= 5 y))
      nil
    (cons (pi-lanes 0 y a w)
          (pi-planes (+ 1 y) a w))))

(defthm plane-list-of-pi-planes
  (implies (and (w-valp w)
                (plane-listp a w)
                (state-arrayp a w))
           (plane-listp (pi-planes y a w) w))
  :hints (("Goal" :in-theory (e/d (pi-planes planep)
                                  (lane-listp-when-planep)))))

(defthm len-of-pi-planes
  (implies (and (w-valp w)
                (plane-listp a w)
                (state-arrayp a w)
                (natp y)
                (<= y 5))
           (equal (len (pi-planes y a w))
                  (- 5 y)))
  :hints (("Goal" :in-theory (e/d (pi-planes planep)
                                  (lane-listp-when-planep)))))

;; The step mapping pi (Algorithm 3 in Sec 3.2.3).
;; We use the name pi-fn because pi is not a legal name.
(defund pi-fn (a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w))))
  (pi-planes 0 a w))

(defthm state-arrayp-of-pi-fn
  (implies (and (w-valp w)
                (state-arrayp a w))
           (state-arrayp (pi-fn a w) w))
  :hints (("Goal" :in-theory (e/d (pi-fn state-arrayp)
                                  (plane-listp-when-state-arrayp)))))

;;;
;;; chi
;;;

;; Compute bits z through w-1 of lane (x,y) of chi.  Part of Step 1 of Algorithm 4.
(defund chi-lane (z x y a w)
  (declare (xargs :guard (and (natp x)
                              (< x 5)
                              (natp y)
                              (< y 5)
                              (natp z)
                              (w-valp w)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- w z)))))
  (if (or (not (mbt (natp z)))
          (not (mbt (natp w)))
          (<= w z))
      nil
    (cons (bitxor$ (a x y z a w)
                   (bitand$ (bitxor$ (a (mod (+ x 1) 5) y z a w)
                                     1)
                            (a (mod (+ x 2) 5) y z a w)))
          (chi-lane (+ 1 z) x y a w))))

(defthm bit-stringp-of-chi-lane
  (implies (and (state-arrayp a w)
                (posp w))
           (bit-stringp (chi-lane z x y a w)))
  :hints (("Goal" :in-theory (enable chi-lane))))

(defthm len-of-chi-lane
  (implies (and (state-arrayp a w)
                (posp w)
                (natp z))
           (equal (len (chi-lane z x y a w))
                  (nfix (- w z))))
  :hints (("Goal" :in-theory (enable chi-lane))))

;; Compute lanes x through 4 of plane y of chi.  Part of Step 1 of Algorithm 4.
(defund chi-lanes (x y a w)
  (declare (xargs :guard (and (w-valp w)
                              (natp x)
                              (natp y)
                              (< y 5)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- 5 x)))))
  (if (or (not (mbt (natp x)))
          (<= 5 x))
      nil
    (cons (chi-lane 0 x y a w)
          (chi-lanes (+ 1 x) y a w))))

(defthm len-of-chi-lanes
  (implies (and (w-valp w)
                (natp x))
           (equal (len (chi-lanes x y a w))
                  (nfix (- 5 x))))
  :hints (("Goal" :in-theory (enable chi-lanes))))

(defthm lane-listp-of-chi-lanes
  (implies (and (w-valp w)
                (natp x)
                (natp y)
                (state-arrayp a w))
           (lane-listp (chi-lanes x y a w) w))
  :hints (("Goal" :in-theory (enable chi-lanes lanep))))

;; Compute planes y through 4 of chi. Part of Step 1 of Algorithm 4.
(defund chi-planes (y a w)
  (declare (xargs :guard (and (natp y)
                              (w-valp w)
                              (state-arrayp a w))
                  :measure (nfix (+ 1 (- 5 y)))))
  (if (or (not (mbt (natp y)))
          (<= 5 y))
      nil
    (cons (chi-lanes 0 y a w)
          (chi-planes (+ 1 y) a w))))

(defthm plane-list-of-chi-planes
  (implies (and (w-valp w)
                (plane-listp a w)
                (state-arrayp a w))
           (plane-listp (chi-planes y a w) w))
  :hints (("Goal" :in-theory (e/d (chi-planes planep)
                                  (lane-listp-when-planep)))))

(defthm len-of-chi-planes
  (implies (and (w-valp w)
                (plane-listp a w)
                (state-arrayp a w)
                (natp y)
                (<= y 5))
           (equal (len (chi-planes y a w))
                  (- 5 y)))
  :hints (("Goal" :in-theory (e/d (chi-planes planep)
                                  (lane-listp-when-planep)))))

;; The chi step mapping (Algorithm 4 in Section 3.2.4)
(defund chi (a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w))))
  (chi-planes 0 a w))

(defthm state-arrayp-of-chi
  (implies (and (w-valp w)
                (state-arrayp a w))
           (state-arrayp (chi a w) w))
  :hints (("Goal" :in-theory (e/d (chi state-arrayp)
                                  (plane-listp-when-state-arrayp)))))

;;;
;;; iota
;;;

;; Step 3 in Algorithm 5
(defun rc-aux (i max r)
  (declare (xargs :guard (and (natp i)
                              (natp max)
                              (<= i (+ 1 max))
                              (bit-stringp r)
                              (equal 8 (len r)))
                  :measure (nfix (+ 1 (- max i)))))
  (if (or (not (mbt (natp i)))
          (not (mbt (natp max)))
          (< max i))
      (nth 0 r)
    (let* ((r (cons 0 r))
           (r (update-nth 0 (bitxor$ (nth 0 r) (nth 8 r)) r))
           (r (update-nth 4 (bitxor$ (nth 4 r) (nth 8 r)) r))
           (r (update-nth 5 (bitxor$ (nth 5 r) (nth 8 r)) r))
           (r (update-nth 6 (bitxor$ (nth 6 r) (nth 8 r)) r))
           (r (take 8 r)))
      (rc-aux (+ 1 i) max r))))

(defthm unsigned-byte-p-of-rc-aux
  (implies (and (bit-stringp r)
                (equal (len r) 8))
           (unsigned-byte-p 1 (rc-aux i max r))))

;; Algorithm 5
(defund rc (t-var)
  (declare (xargs :guard (integerp t-var)))
  (let ((t-mod-255 (mod t-var 255)))
    (if (equal t-mod-255 0)
        1
      (let ((r '(1 0 0 0 0 0 0 0)))
        (rc-aux 1 t-mod-255 r)))))

(defthm unsigned-byte-p-of-rc
  (unsigned-byte-p 1 (rc t-var))
  :hints (("Goal" :in-theory (enable rc))))

(defthm <=-of-expt-when-<=-linear
  (implies (and (<= J k)
                (syntaxp (quotep k))
                (natp j)
                (natp k))
           (<= (expt 2 j) (expt 2 k)))
  :rule-classes ((:linear :trigger-terms ((expt 2 j)))))

;; Step 3 of Algorithm 6 (Sec 3.2.5)
(defun iota-aux (j l rc i_r w)
  (declare (xargs :guard (and (natp j)
                              (natp l)
                              (<= j (+ 1 l))
                              (bit-stringp rc)
                              (equal (len rc) w)
                              (integerp i_r) ;todo: strengthen?
                              (w-valp w)
                              (equal l (lg w)))
                  :guard-hints (("Goal" :in-theory (enable W-VALP)))
                  :measure (nfix (+ 1 (- l j)))))
  (if (or (not (mbt (natp j)))
          (not (mbt (natp l)))
          (< l j))
      rc
    (let ((rc (update-nth (- (expt 2 j) 1)
                          (rc (+ j (* 7 i_r)))
                          rc)))
      (iota-aux (+ 1 j) l rc i_r w))))

(defthm all-unsigned-byte-p-of-iota-aux
  (implies (and (bit-stringp rc)
                (equal (len rc) w)
                (equal l (lg w))
                (w-valp w))
           (all-unsigned-byte-p 1 (iota-aux j l rc i_r w)))
  :hints (("Goal" :induct (iota-aux j l rc i_r w)
           :expand ((:free (k w) (IOTA-AUX k k RC I_R w)))
           :in-theory (enable w-valp))))

(defthm true-listp-of-iota-aux
  (implies (and (bit-stringp rc)
                (equal (len rc) w)
                (equal l (lg w))
                (w-valp w))
           (true-listp (iota-aux j l rc i_r w)))
  :hints (("Goal" :induct (iota-aux j l rc i_r w)
           :expand ((:free (k w) (IOTA-AUX k k RC I_R w)))
           :in-theory (enable w-valp))))

(defthm len-of-iota-aux
  (implies (and (bit-stringp rc)
                (equal (len rc) w)
                (equal l (lg w))
                (w-valp w))
           (equal (len (iota-aux j l rc i_r w))
                  w))
  :hints (("Goal" :induct (iota-aux j l rc i_r w)
           :expand ((:free (k w) (IOTA-AUX k k RC I_R w)))
           :in-theory (enable w-valp))))

;; Step 4 of Algorithm 6 (Sec 3.2.5)
(defund iota-aux2 (z a-prime a rc w)
  (declare (xargs :guard (and (w-valp w)
                              (natp z)
                              (state-arrayp a-prime w)
                              (state-arrayp a w)
                              (bit-stringp rc)
                              (equal (len rc) w))
                  :measure (nfix (+ 1 (- w z)))))
   (if (or (not (mbt (natp z)))
          (not (mbt (natp w)))
          (<= w z))
      a-prime
    (let ((a-prime (update-bit 0 0 z (bitxor$ (a 0 0 z a w) (nth z rc)) a-prime w)))
      (iota-aux2 (+ 1 z) a-prime a rc w))))

(defthm state-arrayp-of-iota-aux2
  (implies (and (w-valp w)
                (state-arrayp a-prime w))
           (state-arrayp (iota-aux2 z a-prime a rc w) w))
  :hints (("Goal" :in-theory (enable IOTA-aux2))))

;; The iota step mapping (Algorithm 6 in Section 3.2.5)
(defund iota (a i_r w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w)
                              (integerp i_r) ;todo: strengthen?
                              )
                  :guard-hints (("Goal" :in-theory (enable w-valp)))))
  (let* ((a-prime a)
         (rc (repeat w 0))
         (l (lg w))
         (rc (iota-aux 0 l rc i_r w))
         (a-prime (iota-aux2 0 a-prime a rc w)))
    a-prime))

(defthm state-arrayp-of-iota
  (implies (and (w-valp w)
                (state-arrayp a w))
           (state-arrayp (iota a i_r w) w))
  :hints (("Goal" :in-theory (enable IOTA))))

;; Section 3.3
(defun rnd (a i_r w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w)
                              (integerp i_r) ;todo: strengthen?
                              )))
  (iota (chi (pi-fn (rho (theta a w) w) w) w) i_r w))

;; Step 2 of Algorithm 7
(defun keccak-p-aux (i_r max a w)
  (declare (xargs :guard (and (w-valp w)
                              (state-arrayp a w)
                              (integerp i_r) ;todo: strengthen?
                              (integerp max))
                  :measure (nfix (+ 1 (- max i_r)))))
  (if (or (not (mbt (integerp i_r)))
          (not (mbt (integerp max)))
          (< max i_r))
      a
    (let ((a (rnd a i_r w)))
      (keccak-p-aux (+ 1 i_r) max a w))))

(defthm state-arrayp-of-keccak-p-aux
  (implies (and (state-arrayp a w)
                (w-valp w))
           (state-arrayp (keccak-p-aux i_r max a w) w)))

;; Algorithm 7
;; Passing in b is not strictly needed, since we pass in w.  But we include it
;; as a parameter to match the spec document.
(defund keccak-p (b n_r s w)
  (declare (xargs :guard (and (w-valp w)
                              (equal b (* 25 w))
                              (bit-stringp s)
                              (equal (len s) b)
                              (natp n_r)))
           (ignore b))
  (let* ((a (bits-to-state-array s w))
         (l (lg w))
         (a (keccak-p-aux (+ 12 (* 2 l) (- n_r))
                          (+ 12 (* 2 l) -1)
                          a
                          w))
         (s-prime (state-array-to-bits a w)))
    s-prime))

(defthm all-unsigned-byte-p-of-keccak-p
  (implies (and (w-valp w)
                (bit-stringp s)
                (equal (len s) (* 25 w)))
           (all-unsigned-byte-p 1 (keccak-p b n_r s w)))
  :hints (("Goal" :in-theory (enable keccak-p))))

(defthm len-of-keccak-p
  (implies (and (w-valp w)
                (bit-stringp s)
                (equal (len s) b)
                (equal b (* 25 w)))
           (equal (len (keccak-p b n_r s w))
                  b))
  :hints (("Goal" :in-theory (enable keccak-p))))

;; ;omit?
;; ;; Passing in b is not strictly needed, since we pass in w.  But we include it
;; ;; as a parameter to match the spec document.
;; (defun keccak-f (b s w)
;;   (declare (xargs :guard (and (w-valp w)
;;                               (equal b (* 25 w))
;;                               (bit-stringp s)
;;                               (equal (len s) b))
;;                   :guard-hints (("Goal" :in-theory (enable W-VALP)))))
;;   (let ((l (lg w)))
;;     (keccak-p b (+ 12 (* 2 l)) s w)))

;;;
;;; pad10*1
;;;

;; Algorithm 9 in Sec 5.1
(defund pad10*1 (x m)
  (declare (xargs :guard (and (posp x)
                              (natp m))))
  (let* ((j (mod (- (- m) 2) x)))
    (append '(1) (repeat j 0) '(1))))

;; Prove that m+len(P) is a multiple of x
(defthm pad10*1-correct-1
  (implies (and (posp x)
                (natp m))
           (equal (mod (+ m (len (pad10*1 x m))) x)
                  0))
  :hints (("Goal" :in-theory (enable pad10*1 acl2::mod-sum-cases))))

;; Prove that m+len(P) is a positive multiple of x (given the above result).
(defthm pad10*1-correct-2
  (implies (and (posp x)
                (natp m))
           (< 0 (/ (+ m (len (pad10*1 x m))) x)))
  :hints (("Goal" :in-theory (enable pad10*1 acl2::mod-sum-cases))))

(defthm all-unsigned-byte-p-of-pad10*1
  (all-unsigned-byte-p 1 (pad10*1 x m))
  :hints (("Goal" :in-theory (enable pad10*1))))

(defthmd len-of-pad10*1
  (implies (and (posp x)
                (natp m))
           (equal (len (pad10*1 x m))
                  (+ 2 (mod (- (- m) 2) x))))
  :hints (("Goal" :in-theory (enable pad10*1))))

(defthm mod-of-len-of-pad10*1
  (implies (and (posp x)
                (natp m))
           (equal (mod (len (pad10*1 x m)) x)
                  (mod (- m) x)))
  :hints (("Goal" :in-theory (enable pad10*1))))

;; Step 6 of Algorithm 8 except we fix f to be keccak-p.
(defun keccak-sponge-aux (b n_r r i n-1 s p-strings c w)
  (declare (xargs :guard (and (w-valp w)
                              (equal b (* 25 w))
                              (natp n_r)
                              (natp i)
                              (natp n-1)
                              (bit-stringp s)
                              (equal (len s) b)
                              (all-bit-stringp p-strings)
                              (true-listp p-strings)
                              (items-have-len r p-strings)
                              (equal (len p-strings)
                                     (+ 1 n-1))
                              (natp r)
                              (< r b)
                              (equal c (- b r)))
                  :measure (nfix (+ 1 (- n-1 i)))))
  (if (or (not (mbt (integerp i)))
          (not (mbt (integerp n-1)))
          (< n-1 i))
      s
    (let ((s (keccak-p b
                       n_r
                       (bvxor-list 1 s
                                   (append (nth i p-strings)
                                           (repeat c 0)))
                       w)))
      (keccak-sponge-aux b n_r r (+ 1 i) n-1 s p-strings c w))))

(defthm len-of-keccak-sponge-aux
  (implies (and (equal (len s) b)
                (equal b (* 25 w))
                (w-valp w))
           (equal (len (keccak-sponge-aux b n_r r i n-1 s p-strings c w))
                  b)))

(defthm bit-stringp-of-bvxor-list
  (bit-stringp (bvxor-list 1 x y))
  :hints (("Goal" :in-theory (enable bit-stringp))))

(defthm all-unsigned-byte-p-of-keccak-sponge-aux
  (implies (and (all-unsigned-byte-p 1 s)
                (equal b (* 25 w))
                (equal (len s) b)
                (w-valp w))
           (all-unsigned-byte-p 1 (keccak-sponge-aux b n_r r i n-1 s p-strings c w))))

(defthm bit-stringp-of-keccak-sponge-aux
  (implies (and (bit-stringp s)
                (equal b (* 25 w))
                (equal (len s) b)
                (w-valp w))
           (bit-stringp (keccak-sponge-aux b n_r r i n-1 s p-strings c w))))

;; Steps 8-10 of Algorithm 8 except we fix f to be keccak-p.
(defund keccak-sponge-aux2 (b n_r r z s d w)
  (declare (xargs :guard (and (w-valp w)
                              (equal b (* 25 w))
                              (natp n_r)
                              (bit-stringp z)
                              (posp r) ;must be positive for termination
                              (< r b)
                              (bit-stringp s)
                              (equal (len s) b)
                              (natp d))
                  :measure (nfix (+ 1 (- d (len z))))))
  (if (or (not (mbt (posp r)))
          (not (mbt (natp d))))
      :error
      (let ((z (append z (take r s))))
        (if (<= d (len z))
            (take d z)
          (let ((s (keccak-p b
                             n_r
                             s
                             w)))
            (keccak-sponge-aux2 b n_r r z s d w))))))

(defthm len-of-keccak-sponge-aux2
  (implies (and (natp d)
                (posp r))
           (equal (len (keccak-sponge-aux2 b n_r r z s d w))
                  d))
  :hints (("Goal" :in-theory (enable keccak-sponge-aux2))))

(defthm true-listp-of-keccak-sponge-aux2
  (implies (and (natp d)
                (posp r)
                (true-listp z))
           (true-listp (keccak-sponge-aux2 b n_r r z s d w)))
  :hints (("Goal" :in-theory (enable keccak-sponge-aux2))))

(defthm all-unsigned-byte-p-of-keccak-sponge-aux2
  (implies (and (natp d)
                (posp r)
                (all-unsigned-byte-p 1 z)
                (bit-stringp s)
                (< r (len s))
                (equal (len s) b)
                (equal b (* 25 w))
                (w-valp w))
           (all-unsigned-byte-p 1 (keccak-sponge-aux2 b n_r r z s d w)))
  :hints (("Goal" :in-theory (enable keccak-sponge-aux2))))

;; (defthm padding-hack
;;   (implies  (and (posp x)
;;                  (natp m))
;;             (equal (equal (+ (mod m x)
;;                              (mod (len (pad10*1 x m)) x))
;;                           x)
;;                    (not (equal 0 (mod m x))))))

;; (defthm padding-hack2
;;   (implies  (and (posp x)
;;                  (natp m))
;;             (equal (< (+ (mod m x)
;;                          (mod (len (pad10*1 x m)) x))
;;                       x)
;;                    (equal 0 (mod m x)))))

(defthm padding-hack3
  (implies  (and (posp x)
                 (natp m))
            (INTEGERP (+ (* (/ x) m)
                         (* (/ x) (LEN (PAD10*1 x m ))))))
  :hints (("Goal" :use (:instance pad10*1-correct-1)
           :in-theory (e/d (acl2::equal-of-0-and-mod)
                           (pad10*1-correct-1)))))

(defthm padding-hack4
  (implies  (and (posp x)
                 (natp m))
            (<= 1
                (+ (* (/ x) m)
                   (* (/ x) (LEN (PAD10*1 x m))))))
  :hints (("Goal" :use (pad10*1-correct-1
                        pad10*1-correct-2)
           :in-theory (e/d (acl2::equal-of-0-and-mod)
                           (pad10*1-correct-1
                            pad10*1-correct-2)))))

;; SPONGE[keccak-p(b,n_r),pad10*1,r].  Algorithm 8 except we fix f to be
;; keccak-p and pad to be pad10*1.
(defund keccak-sponge (b ; a param of keccak-p since we fixed f to be keccak-p
                      n_r ; a param of keccak-p since we fixed f to be keccak-p
                      r n d w)
  (declare (xargs :guard (and (w-valp w)
                              (equal b (* 25 w))
                              (natp n_r)
                              (bit-stringp n)
                              (natp d)
                              (posp r) ;can't be 0 since we divide by it
                              (< r b))
                  :guard-hints (("Goal" :in-theory (e/d (acl2::mod-sum-cases
                                                         acl2::equal-of-0-and-mod
                                                         ;;len-of-pad10*1
                                                         )
                                                        (acl2::group-of-append-new2
                                                         acl2::group-of-append
                                                         mod-of-len-of-pad10*1))))))
  (let* ((p (append n (pad10*1 r (len n))))
         (n (/ (len p) r))
         (c (- b r))
         (p-strings (group r p))
         (s (repeat b 0))
         (s (keccak-sponge-aux b n_r r 0 (- n 1) s p-strings c w))
         (z '()))
    (keccak-sponge-aux2 b n_r r z s d w)))

(defthm len-of-keccak-sponge
  (implies (and (natp d)
                (posp r))
           (equal (len (keccak-sponge b n_r r n d w))
                  d))
  :hints (("Goal" :in-theory (enable keccak-sponge))))

(defthm bit-stringp-of-keccak-sponge
  (implies (and (natp d)
                (posp r)
                (equal b (* 25 w))
                (< r b)
                (w-valp w))
           (bit-stringp (keccak-sponge b n_r r n d w)))
  :hints (("Goal" :in-theory (enable keccak-sponge))))

;; Sec 5.2.  Defines Keccak[c].
(defund keccak (c n d)
  (declare (xargs :guard (and (posp c)
                              (< c 1600)
                              (bit-stringp n)
                              (natp d))))
  (let ((r (- 1600 c))
        (w 64))
    (keccak-sponge 1600 24 r n d w)))

(defthm len-of-keccak
  (implies (and (natp d)
                (< c 1600)
                (natp c))
           (equal (len (keccak c n d))
                  d))
  :hints (("Goal" :in-theory (enable keccak))))

(defthm bit-stringp-of-keccak
  (implies (and (natp d)
                (< c 1600)
                (posp c))
           (bit-stringp (keccak c n d)))
  :hints (("Goal" :in-theory (e/d (keccak) (bit-stringp)))))

(defthm true-listp-of-keccak
  (implies (and (natp d)
                (< c 1600)
                (posp c))
           (true-listp (keccak c n d)))
  :hints (("Goal" :use (:instance bit-stringp-of-keccak)
           :in-theory (disable bit-stringp-of-keccak))))

(defthm all-unsigned-byte-p-1-of-keccak
  (implies (and (natp d)
                (< c 1600)
                (posp c))
           (all-unsigned-byte-p 1 (keccak c n d)))
  :hints (("Goal" :use (:instance bit-stringp-of-keccak)
           :in-theory (disable bit-stringp-of-keccak))))


;;;
;;; The Keccak functions
;;;

(defun keccak-256 (m)
  (declare (xargs :guard (bit-stringp m)))
  (keccak 512 m 256))

;;;
;;; The SHA-3 functions
;;;

;; Returns a list of bits
(defund sha3-224 (m)
  (declare (xargs :guard (bit-stringp m)))
  (keccak 448 (append m '(0 1)) 224))

(defthm len-of-sha3-224
  (equal (len (sha3-224 m))
         224)
  :hints (("Goal" :in-theory (enable sha3-224))))

(defthm bit-stringp-of-sha3-224
  (bit-stringp (sha3-224 m))
  :hints (("Goal" :in-theory (e/d (sha3-224) (bit-stringp)))))

;; Returns a list of bytes
(defun sha3-224-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))
                  :guard-hints (("Goal" :use (:instance bit-stringp-of-sha3-224
                                                        (m (acl2::bytes-to-bits-little bytes)))
                                 :in-theory (e/d (acl2::len-mult-of-8p) (bit-stringp-of-sha3-224))))))
  ;; Note little-endian packing/unpacking:
  (acl2::bits-to-bytes-little (sha3-224 (acl2::bytes-to-bits-little bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of bits
(defund sha3-256 (m)
  (declare (xargs :guard (bit-stringp m)))
  (keccak 512 (append m '(0 1)) 256))

(defthm len-of-sha3-256
  (equal (len (sha3-256 m))
         256)
  :hints (("Goal" :in-theory (enable sha3-256))))

(defthm bit-stringp-of-sha3-256
  (bit-stringp (sha3-256 m))
  :hints (("Goal" :in-theory (e/d (sha3-256) (bit-stringp)))))

;; Returns a list of bytes
(defun sha3-256-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))
                  :guard-hints (("Goal" :use (:instance bit-stringp-of-sha3-256
                                                        (m (acl2::bytes-to-bits-little bytes)))
                                 :in-theory (e/d (acl2::len-mult-of-8p) (bit-stringp-of-sha3-256))))))
  ;; Note little-endian packing/unpacking:
  (acl2::bits-to-bytes-little (sha3-256 (acl2::bytes-to-bits-little bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of bits
(defund sha3-384 (m)
  (declare (xargs :guard (bit-stringp m)))
  (keccak 768 (append m '(0 1)) 384))

(defthm len-of-sha3-384
  (equal (len (sha3-384 m))
         384)
  :hints (("Goal" :in-theory (enable sha3-384))))

(defthm bit-stringp-of-sha3-384
  (bit-stringp (sha3-384 m))
  :hints (("Goal" :in-theory (e/d (sha3-384) (bit-stringp)))))

;; Returns a list of bytes
(defun sha3-384-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))
                  :guard-hints (("Goal" :use (:instance bit-stringp-of-sha3-384
                                                        (m (acl2::bytes-to-bits-little bytes)))
                                 :in-theory (e/d (acl2::len-mult-of-8p) (bit-stringp-of-sha3-384))))))
  ;; Note little-endian packing/unpacking:
  (acl2::bits-to-bytes-little (sha3-384 (acl2::bytes-to-bits-little bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of bits
(defund sha3-512 (m)
  (declare (xargs :guard (bit-stringp m)))
  (keccak 1024 (append m '(0 1)) 512))

(defthm len-of-sha3-512
  (equal (len (sha3-512 m))
         512)
  :hints (("Goal" :in-theory (enable sha3-512))))

(defthm bit-stringp-of-sha3-512
  (bit-stringp (sha3-512 m))
  :hints (("Goal" :in-theory (e/d (sha3-512) (bit-stringp)))))

;; Returns a list of bytes
(defun sha3-512-bytes (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))
                  :guard-hints (("Goal" :use (:instance bit-stringp-of-sha3-512
                                                        (m (acl2::bytes-to-bits-little bytes)))
                                 :in-theory (e/d (acl2::len-mult-of-8p) (bit-stringp-of-sha3-512))))))
  ;; Note little-endian packing/unpacking:
  (acl2::bits-to-bytes-little (sha3-512 (acl2::bytes-to-bits-little bytes))))
