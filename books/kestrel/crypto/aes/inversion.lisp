(in-package "AES")

(include-book "aes-spec")
(local (include-book "kestrel/bv/bvchop" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; for bvxor-blast
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (in-theory (disable true-listp
                           ;; for speed:
                           acl2::rewrite-unsigned-byte-p-when-term-size-is-larger
                           acl2::slice-too-high-is-0
                           acl2::slice-upper-bound-linear)))

;todo: push back to aes-spec
(in-theory (disable cipher invcipher inp keyp binary-gf256add))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(local
  (defthm unsigned-bytep-of-gf256add
    (acl2::unsigned-byte-p 8 (binary-gf256add x y))
    :hints (("Goal" :in-theory (enable binary-gf256add)))))

(local
  (defthm gf256add-of-0-arg1
    (equal (gf256add 0 y)
           (bvchop 8 y))
    :hints (("Goal" :in-theory (enable binary-gf256add)))))

(local
  (defthm gf256add-same
    (equal (gf256add x x)
           0)
    :hints (("Goal" :in-theory (enable binary-gf256add)))))

(local
  (defthm gf256add-same-alt
    (equal (gf256add x x y)
           (bvchop 8 y))
    :hints (("Goal" :in-theory (enable binary-gf256add)))))

(local
  (defthm gf256add-associative
    (equal (gf256add (gf256add x y) z)
           (gf256add x (gf256add y z)))
    :hints (("Goal" :in-theory (enable binary-gf256add)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Custom scheme for commuting nests of calls of binary-gf256add

;; If TERM is a call of operator-name, strip off the call, replacing it with
;; argument ARGNUM (0-based).
(local
  (defun acl2::strip-off (operator-name term argnum)
    (if (and (consp term)
             (equal operator-name (car term)))
        (nth argnum term)
      term)))

;; Orders terms like (gf256mult 9 (nth 0 col)) to bring all factors of (nth 0 col) together.
(local
  (defun smaller-gf256add-arg-special (term1 term2)
    (acl2::smaller-termp (acl2::strip-off 'gf256mult term1 2)
                         (acl2::strip-off 'gf256mult term2 2))))

(local
  (defthm acl2::gf256add-commutative-special
    (implies (syntaxp (smaller-gf256add-arg-special a b))
             (equal (gf256add b a)
                    (gf256add a b)))
    :rule-classes ((:rewrite :loop-stopper nil))
    :hints (("Goal" :in-theory (enable binary-gf256add)))))

(local
  (defthm acl2::gf256add-commutative-2-special
    (implies (syntaxp (smaller-gf256add-arg-special a b))
             (equal (gf256add b (gf256add a c))
                    (gf256add a (gf256add b c))))
    :rule-classes ((:rewrite :loop-stopper nil))
    :hints (("Goal" :in-theory (enable binary-gf256add)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm copyarraytostate-of-copy-state-to-array
  (implies (statep state)
           (equal (copyarraytostate (copy-state-to-array state))
                  state))
  :hints (("Goal" :in-theory (enable copy-state-to-array copyarraytostate array-elem-2d))))

(defthm copy-state-to-array-of-copyarraytostate
  (implies (inp input)
           (equal (copy-state-to-array (copyarraytostate input))
                  input))
  :hints (("Goal" :in-theory (e/d (inp
                                   copy-state-to-array
                                   copyarraytostate)
                                  (;; for speed:
                                   true-listp
                                   acl2::len-of-cddr-when-equal-of-len
                                   acl2::default-car
                                   acl2::default-cdr
                                   acl2::len-when-2d-bv-arrayp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm addroundkey-of-addroundkey
  (implies (and (statep state)
                (statep roundkey))
           (equal (addroundkey (addroundkey state roundkey) roundkey)
                  state))
  :hints (("Goal" :in-theory (enable acl2::true-listp-of-cdr
                                     array-elem-2d
                                     addroundkey addroundkey-elem
                                     acl2::car-becomes-nth-of-0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm invshiftrows-of-shiftrows
  (implies (statep state)
           (equal (invshiftrows (shiftrows state))
                  state))
  :hints (("Goal" :in-theory (enable acl2::true-listp-of-cdr
                                     array-elem-2d
                                     shiftrows invshiftrows))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion of SubBytes

;; Checks the sbox inversion property for all the values from val down to 0.
(local
  (defun check-vals (val)
    (declare (xargs :measure (nfix (+ 1 val))))
    (if (not (natp val))
        t
      (and (equal val (nth (nth val (sbox)) (invsbox)))
           (check-vals (+ -1 val))))))

;it works!
;(check-vals 255 (sbox) (invsbox))

(local
  (defthm check-vals-works
    (implies (and (check-vals max)
                  (<= n max)
                  (natp n)
                  (natp max))
             (equal (nth (nth n (sbox)) (invsbox))
                    n))
    :hints (("Goal" :induct (check-vals max)))))

(local
  (defthm nth-nth-sbox-invsbox
    (implies (bytep n)
             (equal (nth (nth n (sbox)) (invsbox))
                    n))
    :hints (("Goal"
             :use (:instance check-vals-works (max 255))
             :in-theory (disable check-vals-works)))))

(local
  (defthm invsubbytes-of-subbytes
    (implies (statep state)
             (equal (invsubbytes (subbytes state))
                    state))
    :hints (("Goal" :in-theory (enable acl2::true-listp-of-cdr
                                       array-elem-2d
                                       subbytes invsubbytes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inversion of MixColumns

;; todo: convert some rules to use gf256add instead of bvxor
(local
  (defthm xtime-of-bvxor
    (equal (xtime (bvxor 8 a b))
           (bvxor 8 (xtime a) (xtime b)))
    :hints (("Goal" :in-theory (e/d (xtime acl2::bvshl acl2::bvxor-blast)
                                    (;acl2::rewrite-bv-equality-when-sizes-dont-match-1 ; todo: loop if we don't use acl2::bvxor-blast
                                     ))))))

(local
  (defthm gf256mult-aux-of-bvxor-in-acc
    (equal (gf256mult-aux d n ctxn (bvxor 8 acc val))
           (bvxor 8 val (gf256mult-aux d n ctxn acc)))
    :hints (("Goal" :in-theory (enable gf256mult-aux binary-gf256add)))))

(local
  (defthm gf256mult-aux-pull-out-acc
    (implies (and (syntaxp (not (equal acc ''0))) ;prevents loops
                  (unsigned-byte-p 8 acc)
                  (unsigned-byte-p 8 ctxn))
             (equal (gf256mult-aux d n ctxn acc)
                    (bvxor 8 acc (gf256mult-aux d n ctxn 0))))
    :hints (("Goal" :use (:instance gf256mult-aux-of-bvxor-in-acc (acc 0) (val acc))
             :in-theory (disable gf256mult-aux-of-bvxor-in-acc)))))

(local
  (defthm gf256mult-aux-of-bvxor-arg1
    (implies (and (bytep d1)
                  (bytep d2)
                  (bytep c-times-x-to-the-n)
                  (natp n)
                  (bytep acc))
             (equal (gf256mult-aux (bvxor 8 d1 d2) n c-times-x-to-the-n acc)
                    (bvxor 8 (gf256mult-aux d1 n c-times-x-to-the-n acc)
                           (gf256mult-aux d2 n c-times-x-to-the-n 0))))
    :hints (("Goal" :in-theory (enable gf256mult-aux)))))

(local
  (defthm gf256mult-of-gf256add-arg2
    (implies (and (unsigned-byte-p 8 x)
                  (unsigned-byte-p 8 y)
                  (unsigned-byte-p 8 z))
             (equal (gf256mult x (gf256add y z))
                    (gf256add (gf256mult x y)
                              (gf256mult x z))))
    :hints (("Goal" :in-theory (enable gf256mult binary-gf256add)))))

(local
  (defthm gf256mult-aux-of-bvxor-arg3
    (implies (and (bytep d)
                  (bytep ctxn1)
                  (bytep ctxn2)
                  (natp n)
                  (bytep acc))
             (equal (gf256mult-aux d n (bvxor 8 ctxn1 ctxn2) acc)
                    (bvxor 8 (gf256mult-aux d n ctxn1 acc)
                           (gf256mult-aux d n ctxn2 0))))
    :hints (("Goal" :in-theory (enable gf256mult-aux binary-gf256add)))))

(local
  (defthm gf256mult-of-gf256add-distributivity
    (implies (and (unsigned-byte-p 8 x)
                  (unsigned-byte-p 8 y)
                  (unsigned-byte-p 8 z))
             (equal (gf256mult (gf256add x y) z)
                    (gf256add (gf256mult x z) (gf256mult y z))))
    :hints (("Goal" :in-theory (enable binary-gf256add gf256mult)))))

(local
  (defthm gf256mult-of-gf256add-distributivity-back
    (implies (and (syntaxp (quotep x))
                  (syntaxp (quotep y))
                  (unsigned-byte-p 8 x)
                  (unsigned-byte-p 8 y)
                  (unsigned-byte-p 8 z))
             (equal (gf256add (gf256mult x z) (gf256mult y z))
                    (gf256mult (gf256add x y) z)))
    :hints (("Goal" :use (:instance gf256mult-of-gf256add-distributivity)
             :in-theory (disable  gf256mult-of-gf256add-distributivity)))))

(local
  (defthm gf256mult-of-gf256add-distributivity-back-with-rest
    (implies (and (syntaxp (and (quotep x)
                                (quotep y)))
                  (unsigned-byte-p 8 x)
                  (unsigned-byte-p 8 y)
                  (unsigned-byte-p 8 z))
             (equal (gf256add (gf256mult x z) (gf256add (gf256mult y z) rest))
                    (gf256add (gf256mult (gf256add x y) z) rest)))
    :hints (("Goal"))))

;;;

(local
  (defun cases-terms (var val)
    (if (zp val)
        (list `(equal ,var 0))
      (cons `(equal ,var ,val)
            (cases-terms var (+ -1 val))))))

(local
  (defmacro cases-for-var (var max)
    `(or ,@(cases-terms var max))))

;; Turns the unsigned-byte-p into a disjunction with 256 cases.
(local
  (defthmd usbp-8-cases
    (equal (unsigned-byte-p 8 x)
           (cases-for-var x 255))))

(local
  (defthm gf256mult-hack-1
    (implies (unsigned-byte-p 8 x)
             (equal (gf256mult 9 (gf256mult 3 x))
                    (gf256mult 27 x)))
    :hints (("Goal" :in-theory (enable usbp-8-cases)))))

(local
  (defthm gf256mult-hack-2
    (implies (unsigned-byte-p 8 x)
             (equal (gf256mult 9 (gf256mult 2 x))
                    (gf256mult 18 x)))
    :hints (("Goal" :in-theory (enable usbp-8-cases)))))

(local
  (defthm gf256mult-hack-3
    (implies (unsigned-byte-p 8 x)
             (equal (gf256mult 11 (gf256mult 3 x))
                    (gf256mult 29 x)))
    :hints (("Goal" :in-theory (enable usbp-8-cases)))))

(local
  (defthm gf256mult-hack-4
    (implies (unsigned-byte-p 8 x)
             (equal (gf256mult 13 (gf256mult 2 x))
                    (gf256mult 26 x)))
    :hints (("Goal" :in-theory (enable usbp-8-cases)))))

(local
  (defthm gf256mult-hack-5
    (implies (unsigned-byte-p 8 x)
             (equal (gf256mult 13 (gf256mult 3 x))
                    (gf256mult 23 x)))
    :hints (("Goal" :in-theory (enable usbp-8-cases)))))

(local
  (defthm gf256mult-hack-6
    (implies (unsigned-byte-p 8 x)
             (equal (gf256mult 14 (gf256mult 2 x))
                    (gf256mult 28 x)))
    :hints (("Goal" :in-theory (enable usbp-8-cases)))))

(local
  (defthm gf256mult-hack-7
    (implies (unsigned-byte-p 8 x)
             (equal (gf256mult 14 (gf256mult 3 x))
                    (gf256mult 18 x)))
    :hints (("Goal" :in-theory (enable usbp-8-cases)))))

(local
  (defthm gf256mult-hack-8
    (implies (unsigned-byte-p 8 x)
             (equal (gf256mult 11 (gf256mult 2 x))
                    (gf256mult 22 x)))
    :hints (("Goal" :in-theory (enable usbp-8-cases)))))


(local
  (defthm gf256mult-of-1-arg1
    (implies (unsigned-byte-p 8 x)
             (equal (gf256mult 1 x)
                    x))
    :hints (("Goal" :in-theory (enable usbp-8-cases)))))

(local
  (defthm gf256mult-of-0-arg1
    (implies (unsigned-byte-p 8 x)
             (equal (gf256mult 0 x)
                    0))
    :hints (("Goal" :in-theory (enable usbp-8-cases)))))


;; First gf256mult-of-gf256add-arg2 fires to distribute.  Then we collect like addends (using the special commute rules) and combine.
(local
  (defthm invmixcolumn-of-mixcolumn
    (implies (byte-arrayp *nb* col)
             (equal (invmixcolumn (mixcolumn col))
                    col))
    :hints (("Goal" :in-theory (enable mixcolumn invmixcolumn)))))

(local
  (defthmd reconstruct-column
    (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x))
           (acl2::take 4 x))))

(defthm invmixcolumns-of-mixcolumns
  (implies (statep state)
           (equal (invmixcolumns (mixcolumns state))
                  state))
  :hints (("Goal" :in-theory (e/d (invmixcolumns mixcolumns reconstruct-column acl2::get-columns)
                                  (acl2::nth-of-get-column)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthm inversion-helper
    (implies (and (inp input)
                  (acl2::member nk '(4 6 8))
                  (expanded-keyp w nk)
                  (keyp key nk))
             (equal (invcipher (cipher input w nk) w nk)
                    input))
    :hints (("Goal" :expand ((:free (round max state nk w) (apply-rounds round max state nk w))
                             (:free (a b c nk) (invapply-rounds a b c nk)))
             :in-theory (enable inp
                                cipher
                                invcipher
                                cipher-core
                                invcipher-core
                                apply-round
                                invapply-round
                                expanded-keyp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm aes-128-decrypt-of-aes-128-encrypt
  (implies (and (inp plaintext)
                (keyp key 4))
           (equal (aes-128-decrypt (aes-128-encrypt plaintext key) key)
                  plaintext)))

(defthm aes-192-decrypt-of-aes-192-encrypt
  (implies (and (inp plaintext)
                (keyp key 6))
           (equal (aes-192-decrypt (aes-192-encrypt plaintext key) key)
                  plaintext)))

(defthm aes-256-decrypt-of-aes-256-encrypt
  (implies (and (inp plaintext)
                (keyp key 8))
           (equal (aes-256-decrypt (aes-256-encrypt plaintext key) key)
                  plaintext)))
