(in-package "ACL2")

;  hifat.lisp                                          Mihir Mehta

; HiFAT, a model which abstracts LoFAT.

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/io/read-ints" :dir :system)
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "rtl/rel9/arithmetic/top" :dir :system))
(include-book "kestrel/utilities/strings/top" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)

(include-book "insert-text")
(include-book "fat32")

;; Some code from Matt, illustrating a technique to get a definition without
;; all the accompanying events.
#!bitops
(encapsulate
  ()

  (local (include-book "centaur/bitops/extra-defs" :dir :system))

; Redundant; copied from the book above.
  (define install-bit ((n natp) (val bitp) (x integerp))
    :parents (bitops)
    :short "@(call install-bit) sets @('x[n] = val'), where @('x') is an integer,
@('n') is a bit position, and @('val') is a bit."

    (mbe :logic
         (b* ((x     (ifix x))
              (n     (nfix n))
              (val   (bfix val))
              (place (ash 1 n))
              (mask  (lognot place)))
           (logior (logand x mask)
                   (ash val n)))
         :exec
         (logior (logand x (lognot (ash 1 n)))
                 (ash val n)))
    ///

    (defthmd install-bit**
      (equal (install-bit n val x)
             (if (zp n)
                 (logcons val (logcdr x))
               (logcons (logcar x)
                        (install-bit (1- n) val (logcdr x)))))
      :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs)))
      :rule-classes
      ((:definition
        :clique (install-bit)
        :controller-alist ((install-bit t nil nil)))))

    (add-to-ruleset ihsext-redefs install-bit**)
    (add-to-ruleset ihsext-recursive-redefs install-bit**)

    (defthm natp-install-bit
      (implies (not (and (integerp x)
                         (< x 0)))
               (natp (install-bit n val x)))
      :rule-classes :type-prescription)

    (defcong nat-equiv equal (install-bit n val x) 1)
    (defcong bit-equiv equal (install-bit n val x) 2)
    (defcong int-equiv equal (install-bit n val x) 3)

    (defthmd logbitp-of-install-bit-split
      ;; Disabled by default since it can cause case splits.
      (equal (logbitp m (install-bit n val x))
             (if (= (nfix m) (nfix n))
                 (equal val 1)
               (logbitp m x)))
      :hints(("Goal" :in-theory (enable logbitp-of-ash-split))))

    (add-to-ruleset ihsext-advanced-thms logbitp-of-install-bit-split)
    (acl2::add-to-ruleset! logbitp-case-splits logbitp-of-install-bit-split)

    (local (in-theory (e/d (logbitp-of-install-bit-split)
                           (install-bit))))

    (defthm logbitp-of-install-bit-same
      (equal (logbitp m (install-bit m val x))
             (equal val 1)))

    (defthm logbitp-of-install-bit-diff
      (implies (not (equal (nfix m) (nfix n)))
               (equal (logbitp m (install-bit n val x))
                      (logbitp m x))))

    (local
     (defthm install-bit-induct
       t
       :rule-classes ((:induction
                       :pattern (install-bit pos v i)
                       :scheme (logbitp-ind pos i)))))

    (defthm install-bit-of-install-bit-same
      (equal (install-bit a v (install-bit a v2 x))
             (install-bit a v x))
      :hints(("Goal" :in-theory (enable install-bit**))))

    (defthm install-bit-of-install-bit-diff
      (implies (not (equal (nfix a) (nfix b)))
               (equal (install-bit a v (install-bit b v2 x))
                      (install-bit b v2 (install-bit a v x))))
      :hints(("Goal" :in-theory (enable install-bit**)))
      :rule-classes ((:rewrite :loop-stopper ((a b install-bit)))))

    (add-to-ruleset ihsext-basic-thms
                    '(logbitp-of-install-bit-same
                      logbitp-of-install-bit-diff
                      install-bit-of-install-bit-same
                      install-bit-of-install-bit-diff))

    (defthm install-bit-when-redundant
      (implies (equal (logbit n x) b)
               (equal (install-bit n b x)
                      (ifix x)))
      :hints(("Goal" :in-theory (enable install-bit**))))

    (defthm unsigned-byte-p-of-install-bit
      (implies (and (unsigned-byte-p n x)
                    (< (nfix i) n))
               (unsigned-byte-p n (install-bit i v x)))
      :hints(("Goal" :in-theory (e/d (install-bit** unsigned-byte-p**)
                                     (unsigned-byte-p))))))
  )

(defthm
  down-alpha-p-of-upcase-char
  (not (str::down-alpha-p (str::upcase-char x)))
  :hints
  (("goal"
    :in-theory (enable str::upcase-char str::down-alpha-p))))

(defthm
  charlist-has-some-down-alpha-p-of-upcase-charlist
  (not (str::charlist-has-some-down-alpha-p
        (str::upcase-charlist x)))
  :hints
  (("goal"
    :in-theory (enable str::charlist-has-some-down-alpha-p
                       str::upcase-charlist))))

(defthmd integer-listp-when-unsigned-byte-listp
  (implies (not (integer-listp x))
           (not (unsigned-byte-listp n x))))

(defthmd rational-listp-when-unsigned-byte-listp
  (implies (not (rational-listp x))
           (not (unsigned-byte-listp n x))))

;; These two theorems cannot be moved to to file-system-lemmas.lisp, because
;; they're expressed in terms of explode, which is not a built-in function.
(defthm len-of-explode-of-string-append
  (equal (len (explode (string-append str1 str2)))
         (+ (len (explode str1))
            (len (explode str2)))))

(defthmd
  length-of-empty-list
  (implies (stringp x)
           (iff (equal (len (explode x)) 0)
                (equal x "")))
  :hints (("goal" :expand (len (explode x)))))

(defthm
  unsigned-byte-listp-of-make-list-ac
  (equal (unsigned-byte-listp n1 (make-list-ac n2 val ac))
         (and (unsigned-byte-listp n1 ac)
              (or (zp n2) (unsigned-byte-p n1 val)))))

(defcong
  str::charlisteqv equal (chars=>nats x)
  1
  :hints
  (("goal" :in-theory (enable chars=>nats fast-list-equiv)
    :induct (fast-list-equiv x x-equiv))))

(defthm nats=>chars-of-take
  (implies (<= (nfix n) (len nats))
           (equal (nats=>chars (take n nats))
                  (take n (nats=>chars nats))))
  :hints (("goal" :in-theory (enable nats=>chars take))))

(defthm
  consecutive-read-file-into-string-1
  (implies
   (and
    (natp bytes1)
    (natp bytes2)
    (natp start1)
    (stringp (read-file-into-string2 filename (+ start1 bytes1)
                                     bytes2 state))
    (<=
     bytes2
     (len
      (explode
       (read-file-into-string2 filename (+ start1 bytes1)
                               bytes2 state)))))
   (equal
    (string-append
     (read-file-into-string2 filename start1 bytes1 state)
     (read-file-into-string2 filename (+ start1 bytes1)
                             bytes2 state))
    (read-file-into-string2 filename start1 (+ bytes1 bytes2)
                            state)))
  :hints
  (("goal"
    :in-theory (e/d (take-of-nthcdr)
                    (binary-append-take-nthcdr))
    :use
    ((:theorem (implies (natp bytes1)
                        (equal (+ bytes1 bytes1 (- bytes1)
                                  bytes2 start1)
                               (+ bytes1 bytes2 start1))))
     (:instance
      binary-append-take-nthcdr (i bytes1)
      (l
       (nthcdr
        start1
        (take
         (+ bytes1 bytes2 start1)
         (explode
          (mv-nth
           0
           (read-file-into-string1
            (mv-nth 0
                    (open-input-channel filename
                                        :character state))
            (mv-nth 1
                    (open-input-channel filename
                                        :character state))
            nil 1152921504606846975))))))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (natp bytes1)
      (natp bytes2)
      (natp start1)
      (stringp
       (read-file-into-string2 filename (+ start1 bytes1)
                               bytes2 state))
      (<=
       bytes2
       (len
        (explode
         (read-file-into-string2 filename (+ start1 bytes1)
                                 bytes2 state))))
      (equal start2 (+ start1 bytes1)))
     (equal
      (string-append
       (read-file-into-string2 filename start1 bytes1 state)
       (read-file-into-string2 filename start2 bytes2 state))
      (read-file-into-string2 filename start1 (+ bytes1 bytes2)
                              state))))))

(defthm
  consecutive-read-file-into-string-2
  (implies
   (and
    (natp bytes1)
    (natp start1)
    (stringp (read-file-into-string2 filename (+ start1 bytes1)
                                     nil state)))
   (equal
    (string-append
     (read-file-into-string2 filename start1 bytes1 state)
     (read-file-into-string2 filename (+ start1 bytes1)
                             nil state))
    (read-file-into-string2 filename start1 nil state)))
  :hints
  (("goal"
    :in-theory (e/d (take-of-nthcdr)
                    (binary-append-take-nthcdr))
    :do-not-induct t
    :use
    ((:instance
      binary-append-take-nthcdr (i bytes1)
      (l
       (nthcdr
        start1
        (explode
         (mv-nth
          0
          (read-file-into-string1
           (mv-nth 0
                   (open-input-channel filename
                                       :character state))
           (mv-nth 1
                   (open-input-channel filename
                                       :character state))
           nil 1152921504606846975))))))
     (:theorem
      (implies
       (and (natp bytes1) (natp start1))
       (equal
        (+
         bytes1 (- bytes1)
         start1 (- start1)
         (len
          (explode
           (mv-nth
            0
            (read-file-into-string1
             (mv-nth 0
                     (open-input-channel filename
                                         :character state))
             (mv-nth 1
                     (open-input-channel filename
                                         :character state))
             nil 1152921504606846975)))))
        (len
         (explode
          (mv-nth
           0
           (read-file-into-string1
            (mv-nth 0
                    (open-input-channel filename
                                        :character state))
            (mv-nth 1
                    (open-input-channel filename
                                        :character state))
            nil 1152921504606846975)))))))
     (:theorem
      (implies
       (natp start1)
       (equal
        (+
         start1 (- start1)
         (len
          (explode
           (mv-nth
            0
            (read-file-into-string1
             (mv-nth 0
                     (open-input-channel filename
                                         :character state))
             (mv-nth 1
                     (open-input-channel filename
                                         :character state))
             nil 1152921504606846975)))))
        (len
         (explode
          (mv-nth
           0
           (read-file-into-string1
            (mv-nth 0
                    (open-input-channel filename
                                        :character state))
            (mv-nth 1
                    (open-input-channel filename
                                        :character state))
            nil 1152921504606846975))))))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (natp bytes1)
      (natp start1)
      (stringp
       (read-file-into-string2 filename (+ start1 bytes1)
                               nil state))
      (equal start2 (+ start1 bytes1)))
     (equal
      (string-append
       (read-file-into-string2 filename start1 bytes1 state)
       (read-file-into-string2 filename start2 nil state))
      (read-file-into-string2 filename start1 nil state))))))

;; This is to get the theorem about the nth element of a list of unsigned
;; bytes.
(local (include-book "std/typed-lists/integer-listp" :dir :system))

(defthm unsigned-byte-listp-of-revappend
  (equal (unsigned-byte-listp width (revappend x y))
         (and (unsigned-byte-listp width (list-fix x))
              (unsigned-byte-listp width y)))
  :hints (("goal" :induct (revappend x y))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthmd
    painful-debugging-lemma-14
    (implies (not (zp cluster-size))
             (and
              (equal (ceiling cluster-size cluster-size) 1)
              (equal (ceiling 0 cluster-size) 0))))

  (defthm painful-debugging-lemma-15
    (implies (and (not (zp j)) (integerp i) (> i j))
             (> (floor i j) 0))
    :rule-classes :linear)

  (defthmd painful-debugging-lemma-16
    (implies (and (<= i1 i2)
                  (integerp i1)
                  (integerp i2)
                  (not (zp j)))
             (and
              (<= (floor i1 j) (floor i2 j))
              (<= (ceiling i1 j) (ceiling i2 j))))
    :rule-classes :linear)

  (defthm painful-debugging-lemma-17 (equal (mod (* y (len x)) y) 0))

  (defthm painful-debugging-lemma-19
    (implies (and (not (zp j)) (integerp i) (>= i 0))
             (>= (ceiling i j) 0))
    :rule-classes :linear)

  (defthm painful-debugging-lemma-20
    (implies (and (not (zp j)) (integerp i) (> i 0))
             (> (ceiling i j) 0))
    :rule-classes :linear))

(defund dir-ent-p (x)
  (declare (xargs :guard t))
  (and (unsigned-byte-listp 8 x)
       (equal (len x) *ms-dir-ent-length*)))

(defthm dir-ent-p-correctness-1
  (implies (dir-ent-p x)
           (not (stringp x)))
  :hints (("goal" :in-theory (enable dir-ent-p)))
  :rule-classes :forward-chaining)

(defthmd len-when-dir-ent-p
  (implies (dir-ent-p dir-ent)
           (equal (len dir-ent)
                  *ms-dir-ent-length*))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthmd
  integer-listp-when-dir-ent-p
  (implies (dir-ent-p x)
           (integer-listp x))
  :hints
  (("goal" :in-theory
    (enable dir-ent-p
            integer-listp-when-unsigned-byte-listp))))

(defthmd
  rational-listp-when-dir-ent-p
  (implies (dir-ent-p x)
           (rational-listp x))
  :hints
  (("goal" :in-theory
    (enable dir-ent-p
            rational-listp-when-unsigned-byte-listp))))

(defthm unsigned-byte-listp-when-dir-ent-p
  (implies (dir-ent-p dir-ent)
           (unsigned-byte-listp 8 dir-ent))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthm true-listp-when-dir-ent-p
  (implies (dir-ent-p dir-ent)
           (true-listp dir-ent)))

(defthm dir-ent-p-of-update-nth
  (implies (dir-ent-p l)
           (equal (dir-ent-p (update-nth key val l))
                  (and (< (nfix key) *ms-dir-ent-length*)
                       (unsigned-byte-p 8 val))))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthmd dir-ent-p-of-append
  (equal (dir-ent-p (binary-append x y))
         (and (equal (+ (len x) (len y))
                     *ms-dir-ent-length*)
              (unsigned-byte-listp 8 y)
              (unsigned-byte-listp 8 (true-list-fix x))))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthm
  nth-when-dir-ent-p
  (implies (dir-ent-p dir-ent)
           (equal (unsigned-byte-p 8 (nth n dir-ent))
                  (< (nfix n) *ms-dir-ent-length*)))
  :hints (("Goal"
           :in-theory
           (enable len-when-dir-ent-p)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (dir-ent-p dir-ent)
             (equal (integerp (nth n dir-ent))
                    (< (nfix n) *ms-dir-ent-length*)))
    :hints
    (("goal" :in-theory (enable integer-listp-when-dir-ent-p))))
   (:rewrite
    :corollary
    (implies (dir-ent-p dir-ent)
             (equal (rationalp (nth n dir-ent))
                    (< (nfix n) *ms-dir-ent-length*)))
    :hints
    (("goal" :in-theory (enable rational-listp-when-dir-ent-p
                                rationalp-of-nth-when-rational-listp))))
   (:linear
    :corollary (implies (and (dir-ent-p dir-ent)
                             (< (nfix n) *ms-dir-ent-length*))
                        (and (<= 0 (nth n dir-ent))
                             (< (nth n dir-ent) (ash 1 8))))
    :hints
    (("goal"
      :in-theory
      (e/d ()
           (unsigned-byte-p-of-nth-when-unsigned-byte-listp nth)))))))

(defthm dir-ent-p-of-chars=>nats
  (implies (equal (len chars) *ms-dir-ent-length*)
           (dir-ent-p (chars=>nats chars)))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defund dir-ent-fix (x)
  (declare (xargs :guard t))
  (if
      (dir-ent-p x)
      x
    (make-list *ms-dir-ent-length* :initial-element 0)))

(defthm dir-ent-p-of-dir-ent-fix
  (dir-ent-p (dir-ent-fix x))
  :hints (("Goal" :in-theory (enable dir-ent-fix))))

(defthm dir-ent-fix-of-dir-ent-fix
  (equal (dir-ent-fix (dir-ent-fix x))
         (dir-ent-fix x))
  :hints (("Goal" :in-theory (enable dir-ent-fix))))

(defthm dir-ent-fix-when-dir-ent-p
  (implies (dir-ent-p x)
           (equal (dir-ent-fix x) x))
  :hints (("Goal" :in-theory (enable dir-ent-fix))))

(fty::deffixtype
 dir-ent
 :pred dir-ent-p
 :fix dir-ent-fix
 :equiv dir-ent-equiv
 :define t
 :forward t)

(defthm
  dir-ent-p-of-take
  (implies (and (unsigned-byte-listp 8 dir-contents)
                (<= 32 (len dir-contents)))
           (dir-ent-p (take 32 dir-contents)))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(fty::deflist dir-ent-list
              :elt-type dir-ent
              :true-listp t
              )

(defthm dir-ent-first-cluster-guard-lemma-1
  (implies (and (unsigned-byte-p 8 a3)
                (unsigned-byte-p 8 a2)
                (unsigned-byte-p 8 a1)
                (unsigned-byte-p 8 a0))
           (fat32-entry-p (combine32u a3 a2 a1 a0)))
  :hints (("goal" :in-theory (e/d (fat32-entry-p)
                                  (unsigned-byte-p)))))

(defund dir-ent-first-cluster (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)
          :guard-hints (("Goal" :in-theory (enable dir-ent-p)))))
  (fat32-entry-mask
   (combine32u (nth 21 dir-ent)
               (nth 20 dir-ent)
               (nth 27 dir-ent)
               (nth 26 dir-ent))))

(defthm fat32-masked-entry-p-of-dir-ent-first-cluster
  (implies
   (dir-ent-p dir-ent)
   (fat32-masked-entry-p (dir-ent-first-cluster dir-ent)))
  :hints (("goal" :in-theory (e/d (dir-ent-first-cluster dir-ent-p)))))

(defund dir-ent-file-size (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)
          :guard-hints (("Goal" :in-theory (enable dir-ent-p)))))
  (combine32u (nth 31 dir-ent)
              (nth 30 dir-ent)
              (nth 29 dir-ent)
              (nth 28 dir-ent)))

(defthm
  dir-ent-file-size-correctness-1
  (implies (dir-ent-p dir-ent)
           (and (<= 0 (dir-ent-file-size dir-ent))
                (< (dir-ent-file-size dir-ent)
                   (ash 1 32))))
  :rule-classes :linear
  :hints (("goal" :in-theory (e/d (dir-ent-file-size)
                                  (combine32u-unsigned-byte))
           :use (:instance combine32u-unsigned-byte
                           (a3 (nth 31 dir-ent))
                           (a2 (nth 30 dir-ent))
                           (a1 (nth 29 dir-ent))
                           (a0 (nth 28 dir-ent))))))

(defund
  dir-ent-set-first-cluster-file-size
  (dir-ent first-cluster file-size)
  (declare
   (xargs
    :guard (and (dir-ent-p dir-ent)
                (fat32-masked-entry-p first-cluster)
                (unsigned-byte-p 32 file-size))
    :guard-hints
    (("goal" :in-theory (enable dir-ent-p)))))
  (let*
      ((dir-ent (mbe :logic (dir-ent-fix dir-ent) :exec dir-ent))
       (old-first-cluster (combine32u (nth 21 dir-ent)
                                      (nth 20 dir-ent)
                                      (nth 27 dir-ent)
                                      (nth 26 dir-ent)))
       (first-cluster (mbe :exec first-cluster :logic (fat32-masked-entry-fix first-cluster)))
       (new-first-cluster (fat32-update-lower-28 old-first-cluster first-cluster))
       (file-size (if (not (unsigned-byte-p 32 file-size))
                      0 file-size)))
    (append
     (subseq dir-ent 0 20)
     (list*
      (logtail 16 (loghead 24 new-first-cluster))
      (logtail 24 new-first-cluster)
      (append (subseq dir-ent 22 26)
              (list (loghead 8 new-first-cluster)
                    (logtail 8 (loghead 16 new-first-cluster))
                    (loghead 8 file-size)
                    (logtail 8 (loghead 16 file-size))
                    (logtail 16 (loghead 24 file-size))
                    (logtail 24 file-size)))))))

(defthm true-listp-of-dir-ent-fix
 (true-listp (dir-ent-fix dir-ent))
  :hints (("goal" :in-theory (enable dir-ent-p dir-ent-fix)))
  :rule-classes :type-prescription)

(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size-lemma-1
  (implies (fat32-masked-entry-p masked-entry)
           (equal (logtail 16
                           (fat32-update-lower-28 entry masked-entry))
                  (logapp 12 (logtail 16 masked-entry)
                          (logtail 28 (fat32-entry-fix entry)))))
  :hints (("goal" :in-theory (e/d (fat32-update-lower-28)
                                  (logapp loghead logtail)))))

(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size-lemma-2
  (implies (fat32-masked-entry-p masked-entry)
           (equal (logtail 24
                           (fat32-update-lower-28 entry masked-entry))
                  (logapp 4 (logtail 24 masked-entry)
                          (logtail 28 (fat32-entry-fix entry)))))
  :hints (("goal" :in-theory (e/d (fat32-update-lower-28)
                                  (logapp loghead logtail)))))

(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size-lemma-3
  (implies (fat32-masked-entry-p masked-entry)
           (equal (logtail 8
                           (fat32-update-lower-28 entry masked-entry))
                  (logapp 20 (logtail 8 masked-entry)
                          (logtail 28 (fat32-entry-fix entry)))))
  :hints (("goal" :in-theory (e/d (fat32-update-lower-28)
                                  (logapp loghead logtail)))))

(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size-lemma-4
  (implies (fat32-masked-entry-p masked-entry)
           (equal (loghead 8
                           (fat32-update-lower-28 entry masked-entry))
                  (loghead 8 masked-entry)))
  :hints (("goal" :in-theory (e/d (fat32-update-lower-28)
                                  (logapp loghead logtail)))))

(encapsulate
  ()

  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))

  (defthm logtail-of-logior
    (equal (logtail pos (logior i j))
           (logior (logtail pos i)
                   (logtail pos j)))
    :hints (("goal" :in-theory (enable* ihsext-recursive-redefs
                                        ihsext-inductions))))

  (defthm loghead-of-logior
    (equal (loghead pos (logior i j))
           (logior (loghead pos i)
                   (loghead pos j)))
    :hints (("goal" :in-theory (enable* ihsext-recursive-redefs
                                        ihsext-inductions))))

  ;; The following two lemmas are redundant with the eponymous lemmas from
  ;; books/centaur/bitops/ihsext-basics.lisp, from where they were taken with
  ;; thanks.
  (defthm bitops::logtail-of-ash
    (equal (logtail bitops::sh2 (ash x bitops::sh1))
           (ash x
                (+ (ifix bitops::sh1)
                   (- (nfix bitops::sh2))))))

  (defthm bitops::loghead-of-ash
    (equal (loghead n (ash x m))
           (ash (loghead (nfix (- (nfix n) (ifix m))) x) m))))

;; The hypotheses are somewhat weaker than this, but getting to them needs the
;; unsigned-byte-p terms to be expanded...
(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size-lemma-5
  (implies (and (unsigned-byte-p 8 a3)
                (unsigned-byte-p 8 a2)
                (unsigned-byte-p 8 a1)
                (unsigned-byte-p 8 a0))
           (equal (logtail 28 (combine32u a3 a2 a1 a0))
                  (logtail 4 a3)))
  :hints
  (("goal" :in-theory (e/d (combine32u unsigned-byte-p-unsigned-byte-p)
                           (logior ash loghead logtail unsigned-byte-p)))
   ("goal''" :in-theory (enable logtail ash))))

(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size
  (implies (and (fat32-masked-entry-p first-cluster1)
                (fat32-masked-entry-p first-cluster2))
           (equal (dir-ent-set-first-cluster-file-size
                   (dir-ent-set-first-cluster-file-size
                    dir-ent first-cluster1 file-size1)
                   first-cluster2 file-size2)
                  (dir-ent-set-first-cluster-file-size
                   dir-ent first-cluster2 file-size2)))
  :hints
  (("goal" :in-theory
    (e/d (dir-ent-set-first-cluster-file-size
          dir-ent-p-of-append len-when-dir-ent-p)
         (logapp loghead logtail)))))

(defthm fat32-masked-entry-p-of-fat32-masked-entry-fix
  (fat32-masked-entry-p (fat32-masked-entry-fix x))
  :hints (("goal" :in-theory (enable fat32-masked-entry-fix))))

(defthm
  dir-ent-set-first-cluster-file-size-of-fat32-masked-entry-fix
  (equal (dir-ent-set-first-cluster-file-size
          dir-ent
          (fat32-masked-entry-fix first-cluster)
          file-size)
         (dir-ent-set-first-cluster-file-size
          dir-ent first-cluster file-size))
  :hints
  (("goal"
    :in-theory (enable dir-ent-set-first-cluster-file-size))))

(defthm
  dir-ent-first-cluster-of-dir-ent-set-first-cluster-file-size-lemma-1
  (implies (and (unsigned-byte-p 8 a3)
                (unsigned-byte-p 8 a2)
                (unsigned-byte-p 8 a1)
                (unsigned-byte-p 8 a0))
           (equal (loghead 28 (combine32u a3 a2 a1 a0))
                  (combine32u (loghead 4 a3) a2 a1 a0)))
  :hints (("goal" :in-theory (e/d (combine32u) (logior ash loghead logtail)))))

(defthm
  dir-ent-first-cluster-of-dir-ent-set-first-cluster-file-size
  (equal
   (dir-ent-first-cluster
    (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-size))
   (fat32-masked-entry-fix first-cluster))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-set-first-cluster-file-size
                     dir-ent-first-cluster dir-ent-p
                     fat32-entry-mask fat32-masked-entry-p)
                    (loghead logtail
                             fat32-update-lower-28-correctness-1
                             logapp ash (:rewrite loghead-identity)
                             unsigned-byte-p
                             fat32-masked-entry-p-of-fat32-masked-entry-fix))
    :use ((:instance fat32-update-lower-28-correctness-1
                     (masked-entry (fat32-masked-entry-fix first-cluster))
                     (entry (combine32u (nth 21 dir-ent)
                                        (nth 20 dir-ent)
                                        (nth 27 dir-ent)
                                        (nth 26 dir-ent))))
          (:instance (:rewrite loghead-identity)
                     (i (logtail 24
                                 (fat32-masked-entry-fix first-cluster)))
                     (size 4))
          (:instance fat32-masked-entry-p-of-fat32-masked-entry-fix
                     (x first-cluster))))))

(defthm
  dir-ent-file-size-of-dir-ent-set-first-cluster-file-size
  (implies
   (unsigned-byte-p 32 file-size)
   (equal
    (dir-ent-file-size
     (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-size))
    file-size))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-set-first-cluster-file-size dir-ent-file-size)
                    (loghead logtail)))))

(defthm
  dir-ent-p-of-dir-ent-set-first-cluster-file-size
  (implies
   (and (fat32-masked-entry-p first-cluster)
        (unsigned-byte-p 32 file-size))
   (and
    (unsigned-byte-listp 8
                         (dir-ent-set-first-cluster-file-size
                          dir-ent first-cluster file-size))
    (equal (len (dir-ent-set-first-cluster-file-size
                 dir-ent first-cluster file-size))
           *ms-dir-ent-length*)))
  :hints
  (("goal"
    :in-theory
    (e/d (dir-ent-p dir-ent-set-first-cluster-file-size
                    fat32-masked-entry-p fat32-entry-p)
         (fat32-update-lower-28-correctness-1))
    :use
    (:instance
     fat32-update-lower-28-correctness-1
     (masked-entry first-cluster)
     (entry (combine32u (nth 21 (dir-ent-fix dir-ent))
                        (nth 20 (dir-ent-fix dir-ent))
                        (nth 27 (dir-ent-fix dir-ent))
                        (nth 26 (dir-ent-fix dir-ent)))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (fat32-masked-entry-p first-cluster)
                  (unsigned-byte-p 32 file-size))
             (dir-ent-p (dir-ent-set-first-cluster-file-size
                         dir-ent first-cluster file-size)))
    :hints (("goal" :in-theory (enable dir-ent-p))))))

(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-fix
  (equal
   (dir-ent-set-first-cluster-file-size
    (dir-ent-fix dir-ent) first-cluster file-size)
   (dir-ent-set-first-cluster-file-size
    dir-ent first-cluster file-size))
  :hints (("goal" :in-theory (enable dir-ent-set-first-cluster-file-size))))

(defcong
  dir-ent-equiv equal
  (dir-ent-set-first-cluster-file-size
   dir-ent first-cluster file-size)
  1
  :hints
  (("goal"
    :in-theory
    (e/d
     (dir-ent-equiv)
     ((:rewrite
       dir-ent-set-first-cluster-file-size-of-dir-ent-fix)))
    :use
    ((:rewrite
      dir-ent-set-first-cluster-file-size-of-dir-ent-fix)
     (:instance
      (:rewrite
       dir-ent-set-first-cluster-file-size-of-dir-ent-fix)
      (dir-ent dir-ent-equiv))))))

(defund
  dir-ent-filename (dir-ent)
  (declare
   (xargs
    :guard (dir-ent-p dir-ent)
    :guard-hints (("goal" :in-theory (enable dir-ent-p)))))
  (nats=>string (subseq (mbe :exec dir-ent
                             :logic (dir-ent-fix dir-ent))
                        0 11)))

(defthm dir-ent-filename-of-dir-ent-fix
  (equal (dir-ent-filename (dir-ent-fix dir-ent))
         (dir-ent-filename dir-ent))
  :hints (("goal" :in-theory (enable dir-ent-filename))))

(defthm
  dir-ent-filename-of-dir-ent-set-first-cluster-file-size
  (equal
   (dir-ent-filename
    (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-size))
   (dir-ent-filename dir-ent))
  :hints
  (("goal"
    :in-theory
    (e/d (dir-ent-set-first-cluster-file-size dir-ent-filename
                                              (:rewrite dir-ent-p-of-append)
                                              len-when-dir-ent-p)
         (loghead logtail logapp unsigned-byte-p)))))

(defthm explode-of-dir-ent-filename
  (equal (explode (dir-ent-filename dir-ent))
         (nats=>chars (take 11 (dir-ent-fix dir-ent))))
  :hints (("goal" :in-theory (enable dir-ent-filename))))

(defund
  dir-ent-set-filename (dir-ent filename)
  (declare
   (xargs
    :guard (and (dir-ent-p dir-ent)
                (stringp filename)
                (equal (length filename) 11))
    :guard-hints
    (("goal"
      :in-theory (enable dir-ent-p-of-append
                         len-when-dir-ent-p string=>nats)))))
  (append
   (mbe :logic (chars=>nats (take 11 (coerce filename 'list)))
        :exec (string=>nats filename))
   (subseq (mbe :exec dir-ent
                :logic (dir-ent-fix dir-ent))
           11 *ms-dir-ent-length*)))

(defthm
  dir-ent-p-of-dir-ent-set-filename
  (dir-ent-p (dir-ent-set-filename dir-ent filename))
  :hints
  (("goal" :in-theory (enable dir-ent-set-filename
                              dir-ent-fix dir-ent-p-of-append)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (unsigned-byte-listp
                8
                (dir-ent-set-filename dir-ent filename))
    :hints (("goal" :in-theory (enable dir-ent-p))))
   (:rewrite
    :corollary
    (true-listp (dir-ent-set-filename dir-ent filename))
    :hints (("goal" :in-theory (enable dir-ent-p))))))

(defthm
  dir-ent-set-filename-of-constant-1
  (implies
   (and (dir-ent-p dir-ent)
        (or (equal filename *current-dir-fat32-name*)
            (equal filename *parent-dir-fat32-name*)))
   (not (equal (nth 0
                    (dir-ent-set-filename dir-ent filename))
               0)))
  :hints
  (("goal" :in-theory (e/d (dir-ent-set-filename dir-ent-p)
                           (nth)))))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (local
   (defthm
     dir-ent-p-of-set-first-cluster-file-size-lemma-1
     (< (* 16
           (logtail 4 (nth 21 (dir-ent-fix dir-ent))))
        256)))

  (defthm
    dir-ent-p-of-set-first-cluster-file-size
    (dir-ent-p (dir-ent-set-first-cluster-file-size
                dir-ent first-cluster file-size))
    :hints
    (("goal" :in-theory
      (e/d (dir-ent-p dir-ent-set-first-cluster-file-size
                      fat32-masked-entry-fix
                      fat32-masked-entry-p)
           (loghead logtail logapp ash))))))

;; per table on page 24 of the spec.
(defund
  dir-ent-directory-p (dir-ent)
  (declare
   (xargs
    :guard (dir-ent-p dir-ent)
    :guard-hints
    (("goal"
      :in-theory (enable integer-listp-when-dir-ent-p)))))
  (logbitp 4 (nth 11 dir-ent)))

(defund
  dir-ent-install-directory-bit
  (dir-ent val)
  (declare
   (xargs
    :guard (and (dir-ent-p dir-ent) (booleanp val))
    :guard-hints
    (("goal"
      :in-theory (enable integer-listp-when-dir-ent-p)))))
  (update-nth 11
              (install-bit 4 (if val 1 0)
                           (nth 11 dir-ent))
              dir-ent))

(defthm
  dir-ent-p-of-dir-ent-install-directory-bit
  (implies
   (dir-ent-p dir-ent)
   (dir-ent-p
    (dir-ent-install-directory-bit dir-ent val)))
  :hints
  (("goal"
    :in-theory
    (e/d (dir-ent-install-directory-bit dir-ent-p))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (dir-ent-p dir-ent)
     (and
      (unsigned-byte-listp
       8
       (dir-ent-install-directory-bit dir-ent val))
      (equal
       (len
        (dir-ent-install-directory-bit dir-ent val))
       *ms-dir-ent-length*)))
    :hints
    (("goal"
      :in-theory
      (e/d (dir-ent-p)))))))

(defthm
  true-listp-of-dir-ent-install-directory-bit
  (implies
   (dir-ent-p dir-ent)
   (true-listp (dir-ent-install-directory-bit dir-ent val))))

(defthm
  dir-ent-install-directory-bit-correctness-1
  (equal (nth 0
              (dir-ent-install-directory-bit dir-ent val))
         (nth 0 dir-ent))
  :hints
  (("goal" :in-theory (enable dir-ent-install-directory-bit))))

(defthm
  dir-ent-directory-p-of-dir-ent-install-directory-bit
  (equal (dir-ent-directory-p
          (dir-ent-install-directory-bit dir-ent val))
         (if val t nil))
  :hints
  (("goal"
    :in-theory
    (e/d (dir-ent-install-directory-bit dir-ent-directory-p)
         (logbitp)))))

(defthm
  dir-ent-first-cluster-of-dir-ent-install-directory-bit
  (equal (dir-ent-first-cluster
          (dir-ent-install-directory-bit dir-ent val))
         (dir-ent-first-cluster dir-ent))
  :hints
  (("goal" :in-theory (enable dir-ent-first-cluster
                              dir-ent-install-directory-bit))))

(defthm
  dir-ent-file-size-of-dir-ent-install-directory-bit
  (equal (dir-ent-file-size
          (dir-ent-install-directory-bit dir-ent val))
         (dir-ent-file-size dir-ent))
  :hints
  (("goal" :in-theory (enable dir-ent-file-size
                              dir-ent-install-directory-bit))))

(defthm
  dir-ent-filename-of-dir-ent-install-directory-bit
  (implies
   (dir-ent-p dir-ent)
   (equal (dir-ent-filename
           (dir-ent-install-directory-bit dir-ent val))
          (dir-ent-filename dir-ent)))
  :hints
  (("goal" :in-theory (enable dir-ent-filename
                              dir-ent-install-directory-bit))))

(defund fat32-filename-p (x)
  (declare (xargs :guard t))
  (and (stringp x)
       (equal (length x) 11)
       (not (equal (char x 0) (code-char #x00)))
       (not (equal (char x 0) (code-char #xe5)))
       (not (equal x *current-dir-fat32-name*))
       (not (equal x *parent-dir-fat32-name*))))

(defun
    fat32-filename-fix (x)
  (declare (xargs :guard (fat32-filename-p x)))
  (mbe
   :logic (if (fat32-filename-p x)
              x
            (coerce (make-list 11 :initial-element #\space)
                    'string))
   :exec x))

(defthm fat32-filename-p-of-fat32-filename-fix
  (fat32-filename-p (fat32-filename-fix x)))

(defthm fat32-filename-p-when-fat32-filename-p
  (implies (fat32-filename-p x)
           (equal (fat32-filename-fix x) x)))

(fty::deffixtype
 fat32-filename
 :pred fat32-filename-p
 :fix fat32-filename-fix
 :equiv fat32-filename-equiv
 :define t
 :forward t)

(defthm
  fat32-filename-p-correctness-1
  (implies (fat32-filename-p x)
           (and (stringp x)
                (equal (len (explode x)) 11)
                (not (equal (nth 0 (explode x)) (code-char #x00)))
                (not (equal (nth 0 (explode x)) (code-char #xe5)))
                (not (equal x *current-dir-fat32-name*))
                (not (equal x *parent-dir-fat32-name*))))
  :hints (("Goal" :in-theory (enable fat32-filename-p))))

(defthm dir-ent-set-filename-correctness-1
  (implies
   (and (fat32-filename-p filename)
        (dir-ent-p dir-ent))
   (and
    (not (equal (nth 0
                     (dir-ent-set-filename dir-ent filename))
                #x00))
    (not (equal (nth 0
                     (dir-ent-set-filename dir-ent filename))
                #xe5))))
  :hints
  (("goal" :in-theory (e/d (dir-ent-set-filename dir-ent-p)
                           (nth)))))

(defthm
  dir-ent-directory-p-of-dir-ent-set-filename
  (implies (and (dir-ent-p dir-ent)
                (fat32-filename-p filename))
           (equal (dir-ent-directory-p
                   (dir-ent-set-filename dir-ent filename))
                  (dir-ent-directory-p dir-ent)))
  :hints (("goal" :in-theory (e/d (dir-ent-directory-p
                                   dir-ent-set-filename
                                   dir-ent-p)
                                  (logbitp)))))

(defthm
  dir-ent-first-cluster-of-dir-ent-set-filename
  (implies (and (dir-ent-p dir-ent)
                (stringp filename)
                (equal (length filename) 11))
           (equal (dir-ent-first-cluster
                   (dir-ent-set-filename dir-ent filename))
                  (dir-ent-first-cluster dir-ent)))
  :hints
  (("goal" :in-theory (enable dir-ent-first-cluster
                              dir-ent-set-filename dir-ent-p))))

(defthm
  dir-ent-filename-of-dir-ent-set-filename
  (equal
   (dir-ent-filename (dir-ent-set-filename dir-ent filename))
   (coerce (take 11 (coerce filename 'list))
           'string))
  :hints
  (("goal"
    :in-theory (enable dir-ent-filename dir-ent-set-filename
                       dir-ent-fix dir-ent-p nats=>string))))

(defthm
  dir-ent-file-size-of-dir-ent-set-filename
  (implies
   (and (dir-ent-p dir-ent)
        (fat32-filename-p filename))
   (equal
    (dir-ent-file-size (dir-ent-set-filename dir-ent filename))
    (dir-ent-file-size dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-file-size
                                     dir-ent-set-filename
                                     dir-ent-p-of-append
                                     len-when-dir-ent-p))))

(defthm
  dir-ent-directory-p-of-dir-ent-set-first-cluster-file-size
  (implies
   (dir-ent-p dir-ent)
   (equal
    (dir-ent-directory-p (dir-ent-set-first-cluster-file-size
                          dir-ent first-cluster file-size))
    (dir-ent-directory-p dir-ent)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (dir-ent-directory-p dir-ent-set-first-cluster-file-size)
     (logbitp)))))

(fty::deflist fat32-filename-list
              :elt-type fat32-filename      ;; required, must have a known fixing function
              :true-listp t
              )

(defthm nthcdr-of-fat32-filename-list-fix
  (equal (nthcdr n
                 (fat32-filename-list-fix relpath))
         (fat32-filename-list-fix (nthcdr n relpath)))
  :hints (("goal" :in-theory (enable fat32-filename-list-fix))))

(defthm
  take-of-fat32-filename-list-fix
  (implies (< (nfix n) (len x))
           (equal (take n (fat32-filename-list-fix x))
                  (fat32-filename-list-fix (take n x))))
  :hints
  (("goal" :in-theory (e/d (fat32-filename-list-fix)
                           (take-of-too-many take-when-atom take-of-cons)))))

(defthm nth-of-fat32-filename-list-fix
  (equal (nth n (fat32-filename-list-fix x))
         (if (< (nfix n) (len x))
             (fat32-filename-fix (nth n x))
             nil))
  :hints (("goal" :in-theory (enable fat32-filename-list-fix))))

(defrefinement
  list-equiv fat32-filename-list-equiv
  :hints
  (("goal" :in-theory (enable fat32-filename-list-fix prefixp)
    :induct (prefixp x y))))

(defcong
  fat32-filename-list-equiv
  fat32-filename-list-equiv
  (nthcdr n l)
  2)

(defcong fat32-filename-list-equiv fat32-filename-list-equiv
  (append x y) 1)

(defcong fat32-filename-list-equiv fat32-filename-list-equiv
  (append x y) 2)

(defthm
  prefixp-of-fat32-filename-list-fix
  (implies (prefixp x y)
           (prefixp (fat32-filename-list-fix x)
                    (fat32-filename-list-fix y)))
  :hints (("goal" :in-theory (enable prefixp fat32-filename-list-fix))))

(defthm prefixp-nthcdr-nthcdr-when-fat32-filename-list-p-1
  (implies (and (>= (len l2) n)
                (equal (take n (fat32-filename-list-fix l1))
                       (take n l2)))
           (equal (prefixp (fat32-filename-list-fix (nthcdr n l1))
                           (nthcdr n l2))
                  (prefixp (fat32-filename-list-fix l1)
                           l2)))
  :hints (("goal"
           :in-theory (enable prefixp fat32-filename-list-fix))))

(defthm prefixp-nthcdr-nthcdr-when-fat32-filename-list-p-2
  (implies (and (>= (len l2) n)
                (equal (take n l1)
                       (take n (fat32-filename-list-fix l2))))
           (equal (prefixp (nthcdr n l1)
                           (fat32-filename-list-fix (nthcdr n l2)))
                  (prefixp l1
                           (fat32-filename-list-fix l2))))
  :hints (("goal"
           :in-theory (enable prefixp fat32-filename-list-fix))))

;; We need to write this whole thing out - based on an idea we got from an
;; event generated by fty::defalist - because the induction scheme has to be
;; created by us, without assistance from fty, just this once.
(defund
  m1-file-alist-p (x)
  (declare (xargs :guard t))
  (b* (((when (atom x)) (equal x nil))
       (head (car x))
       ((when (atom head)) nil)
       (file (cdr head))
       ((unless (and (alistp file)
                     (equal (strip-cars file)
                            '(dir-ent contents))))
        nil)
       (dir-ent (cdr (std::da-nth 0 (cdr head))))
       (contents (cdr (std::da-nth 1 (cdr head)))))
    (and (fat32-filename-p (car head))
         (dir-ent-p dir-ent)
         (or (and (stringp contents)
                  (unsigned-byte-p 32 (length contents)))
             (m1-file-alist-p contents))
         (m1-file-alist-p (cdr x)))))

(defund m1-file-contents-p (contents)
  (declare (xargs :guard t))
  (or (and (stringp contents)
           (unsigned-byte-p 32 (length contents)))
      (m1-file-alist-p contents)))

(defund m1-file-contents-fix (contents)
  (declare (xargs :guard t))
  (if (m1-file-contents-p contents)
      contents
    ""))

(defthm
  m1-file-contents-p-correctness-1
  (implies (m1-file-alist-p contents)
           (m1-file-contents-p contents))
  :hints (("goal" :in-theory (enable m1-file-contents-p))))

(defthm m1-file-contents-p-of-m1-file-contents-fix
  (m1-file-contents-p (m1-file-contents-fix x))
  :hints (("goal" :in-theory (enable m1-file-contents-fix))))

(defthm m1-file-contents-fix-when-m1-file-contents-p
  (implies (m1-file-contents-p x)
           (equal (m1-file-contents-fix x) x))
  :hints (("goal" :in-theory (enable m1-file-contents-fix))))

(defthm
  m1-file-contents-p-when-stringp
  (implies (stringp contents)
           (equal (m1-file-contents-p contents)
                  (unsigned-byte-p 32 (length contents))))
  :hints (("goal" :in-theory (enable m1-file-contents-p m1-file-alist-p))))

(defthm
  m1-file-alist-p-of-m1-file-contents-fix
  (equal (m1-file-alist-p (m1-file-contents-fix contents))
         (m1-file-alist-p contents))
  :hints (("goal" :in-theory (enable m1-file-contents-fix))))

(fty::deffixtype m1-file-contents
                 :pred m1-file-contents-p
                 :fix m1-file-contents-fix
                 :equiv m1-file-contents-equiv
                 :define t)

(fty::defprod
 m1-file
 ((dir-ent dir-ent-p :default (dir-ent-fix nil))
  (contents m1-file-contents-p :default (m1-file-contents-fix nil))))

(defthm
  acl2-count-of-m1-file->contents
  t
  :rule-classes
  ((:linear
    :corollary
    (implies (m1-file-p file)
             (< (acl2-count (m1-file->contents file))
                (acl2-count file)))
    :hints
    (("goal" :in-theory (enable m1-file-p m1-file->contents))))
   (:linear
    :corollary
    (<= (acl2-count (m1-file->contents file))
        (acl2-count file))
    :hints
    (("goal"
      :in-theory
      (enable m1-file-p m1-file->contents m1-file-contents-fix))))))

(defund m1-regular-file-p (file)
  (declare (xargs :guard t))
  (and (m1-file-p file)
       (stringp (m1-file->contents file))
       (unsigned-byte-p 32 (length (m1-file->contents file)))))

(defund m1-directory-file-p (file)
  (declare (xargs :guard t))
  (and (m1-file-p file)
       (m1-file-alist-p (m1-file->contents file))))

(encapsulate
  ()

  (local
   (defthm
     m1-regular-file-p-correctness-1-lemma-1
     (implies (stringp (m1-file->contents file))
              (not (m1-file-alist-p (m1-file->contents file))))
     :hints (("goal" :in-theory (enable m1-file-alist-p)))))

  (defthm
    m1-regular-file-p-correctness-1
    (implies (m1-regular-file-p file)
             (and (stringp (m1-file->contents file))
                  (unsigned-byte-p 32 (len (explode (m1-file->contents file))))
                  (not (m1-directory-file-p file))))
    :hints
    (("goal"
      :in-theory (enable m1-regular-file-p m1-directory-file-p)))))

(defthm m1-file-p-when-m1-regular-file-p
  (implies
   (m1-regular-file-p file)
   (m1-file-p file))
  :hints (("Goal" :in-theory (enable m1-regular-file-p))))

(defthm
  m1-regular-file-p-of-m1-file
  (equal
   (m1-regular-file-p (m1-file dir-ent contents))
   (and
    (stringp (m1-file-contents-fix contents))
    (unsigned-byte-p 32
                     (length (m1-file-contents-fix contents)))))
  :hints (("goal" :in-theory (enable m1-regular-file-p))))

(defthm
  m1-directory-file-p-correctness-1
  (implies (m1-directory-file-p file)
           (and (m1-file-p file)
                (not (stringp (m1-file->contents file)))))
  :hints (("goal"
           :in-theory (enable m1-directory-file-p m1-file-alist-p
                              m1-regular-file-p))))

(defthm
  m1-file-alist-p-of-m1-file->contents
  (equal
   (m1-file-alist-p (m1-file->contents file))
   (m1-directory-file-p (m1-file-fix file)))
  :hints (("Goal" :in-theory (enable m1-file->contents m1-directory-file-p)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (m1-directory-file-p file)
     (m1-file-alist-p (m1-file->contents file))))))

(defthm
  m1-directory-file-p-of-m1-file
  (implies (m1-file-alist-p contents)
           (m1-directory-file-p (m1-file dir-ent contents)))
  :hints (("goal" :in-theory (enable m1-directory-file-p))))

(defthm
  m1-file-alist-p-of-revappend
  (equal (m1-file-alist-p (revappend x y))
         (and (m1-file-alist-p (list-fix x))
              (m1-file-alist-p y)))
  :hints
  (("goal"
    :use
    ((:functional-instance
      element-list-p-of-revappend
      (element-p (lambda (x)
                   (and (consp x)
                        (fat32-filename-p (car x))
                        (m1-file-p (cdr x)))))
      (non-element-p (lambda (x)
                       (not (and (consp x)
                                 (fat32-filename-p (car x))
                                 (m1-file-p (cdr x))))))
      (element-list-p (lambda (x) (m1-file-alist-p x)))
      (element-list-final-cdr-p not)))
    :in-theory (enable m1-file-alist-p
                       m1-file-p m1-file-contents-p)))
  :rule-classes ((:rewrite)))

(fty::defalist m1-file-alist
               :key-type fat32-filename
               :val-type m1-file
               :true-listp t)

(in-theory (disable fat32-filename-p fat32-filename-fix))

(defthm
  m1-file-alist-p-of-remove-assoc-equal
  (implies (m1-file-alist-p fs)
           (m1-file-alist-p (remove-assoc-equal key fs))))

(defun
    hifat-bounded-file-alist-p-helper (x ac)
  (declare (xargs :guard (and (m1-file-alist-p x) (natp ac))
                  :measure (acl2-count x)))
  (or
   (atom x)
   (and
    (not (zp ac))
    (let
        ((head (car x)))
      (and
       (consp head)
       (let
           ((file (cdr head)))
         (if
             (m1-directory-file-p file)
             (and (hifat-bounded-file-alist-p-helper (m1-file->contents file)
                                                     *ms-max-dir-ent-count*)
                  (hifat-bounded-file-alist-p-helper (cdr x)
                                                     (- ac 1)))
           (hifat-bounded-file-alist-p-helper (cdr x)
                                              (- ac 1)))))))))

(defthmd len-when-hifat-bounded-file-alist-p-helper
  (implies (hifat-bounded-file-alist-p-helper x ac)
           (<= (len x) (nfix ac)))
  :rule-classes :linear)

(defund
  hifat-bounded-file-alist-p (x)
  (declare (xargs :guard (m1-file-alist-p x)))
  (hifat-bounded-file-alist-p-helper x *ms-max-dir-ent-count*))

(defthm
  len-when-hifat-bounded-file-alist-p
  (implies (hifat-bounded-file-alist-p x)
           (<= (len x) *ms-max-dir-ent-count*))
  :rule-classes
  (:linear
   (:linear
    :corollary (implies (hifat-bounded-file-alist-p x)
                        (<= (* *ms-dir-ent-length* (len x))
                            (* *ms-dir-ent-length*
                               *ms-max-dir-ent-count*))))
   (:linear
    :corollary (implies (and (hifat-bounded-file-alist-p x) (consp x))
                        (<= (* *ms-dir-ent-length* (len (cdr x)))
                            (-
                             (* *ms-dir-ent-length*
                                *ms-max-dir-ent-count*)
                             *ms-dir-ent-length*)))))
  :hints
  (("goal"
    :in-theory (enable hifat-bounded-file-alist-p)
    :use (:instance len-when-hifat-bounded-file-alist-p-helper
                    (ac *ms-max-dir-ent-count*)))))

(defthmd hifat-bounded-file-alist-p-of-cdr-lemma-1
  (implies (and (hifat-bounded-file-alist-p-helper x ac1)
                (< ac1 ac2)
                (not (zp ac2)))
           (hifat-bounded-file-alist-p-helper x ac2)))

(defthm
  hifat-bounded-file-alist-p-of-cdr-lemma-2
  (implies (hifat-bounded-file-alist-p-helper x ac)
           (hifat-bounded-file-alist-p-helper (cdr x)
                                              ac))
  :hints
  (("goal" :induct (hifat-bounded-file-alist-p-helper x ac))
   ("subgoal *1/4"
    :use (:instance hifat-bounded-file-alist-p-of-cdr-lemma-1
                    (x (cdr x))
                    (ac1 (- ac 1))
                    (ac2 ac)))
   ("subgoal *1/2"
    :use (:instance hifat-bounded-file-alist-p-of-cdr-lemma-1
                    (x (cdr x))
                    (ac1 (- ac 1))
                    (ac2 ac)))))

(defthm hifat-bounded-file-alist-p-of-cdr
  (implies (hifat-bounded-file-alist-p x)
           (hifat-bounded-file-alist-p (cdr x)))
  :hints (("goal" :in-theory (enable hifat-bounded-file-alist-p))))

;; It would be nice to leave the rule-classes alone, but trying to
;; unconditionally rewrite (m1-directory-file-p x) has unintended
;; consequences.
(defthm m1-directory-file-p-when-m1-file-p
  (implies (m1-file-p x)
           (equal (m1-directory-file-p x)
                  (not (m1-regular-file-p x))))
  :hints
  (("goal"
    :in-theory (enable m1-regular-file-p
                       m1-directory-file-p m1-file-p
                       m1-file-contents-p m1-file->contents)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (m1-file-p x)
          (not (m1-regular-file-p x)))
     (m1-directory-file-p x)))))

(defthm hifat-bounded-file-alist-p-of-cdar
  (implies (and (hifat-bounded-file-alist-p x)
                (m1-directory-file-p (cdar x)))
           (hifat-bounded-file-alist-p (m1-file->contents (cdar x))))
  :hints (("goal" :in-theory (enable hifat-bounded-file-alist-p))))

(fty::defprod
 struct-stat
 ;; Currently, this is the only thing I can decipher.
 ((st_size natp :default 0)))

(fty::defprod
 struct-statfs
 ((f_type natp :default 0)
  (f_bsize natp :default 0)
  (f_blocks natp :default 0)
  (f_bfree natp :default 0)
  (f_bavail natp :default 0)
  (f_files natp :default 0)
  (f_ffree natp :default 0)
  (f_fsid natp :default 0)
  (f_namelen natp :default 72)))

;; This data structure may change later.
(fty::defprod
 file-table-element
 ((pos natp) ;; index within the file
  ;; mode ?
  (fid fat32-filename-list-p) ;; pathname of the file
  ))

(fty::defalist
 file-table
 :key-type nat
 :val-type file-table-element
 :true-listp t)

(defthm file-table-p-correctness-1
  (implies (file-table-p file-table)
           (nat-listp (strip-cars file-table))))

(defthm file-table-p-correctness-2
  (implies (and (file-table-p file-table) (consp (assoc-equal key file-table)))
           (file-table-element-p (cdr (assoc-equal key file-table)))))

;; This data structure may change later.
(fty::defalist fd-table
               :key-type nat ;; index into the fd-table
               :val-type nat ;; index into the file-table
               :true-listp t)

(defthm fd-table-p-correctness-1
  (implies (fd-table-p fd-table)
           (nat-listp (strip-cars fd-table))))

;; It's tempting to remove this predicate, because it makes the fixing of
;; certain functions hard... but it does give us the desirable property of
;; maintaining equality for hifat-entry-count between two directory trees whenever
;; it holds for the two trees. I'm not sure that property is currently used,
;; but it makes a good argument for keeping it. One other argument is the proof
;; of anti-reflexivity for hifat-subsetp - if we are to prove that y is a
;; subset of y under this definition of subsetp (that is, this definition which
;; doesn't do remove-equal), then we need to make sure there are no duplicate
;; bindings for the same filename within a directory. The third argument
;; pertains to the generally understood semantics for filesystems, where there
;; is generally no valid way of dealing with two directory entries referring to
;; the same filename (not the same inode, which is OK in filesystems with hard
;; linking.)
;;
;; In support of this whole thing about ordering of files, there are folks on
;; StackOverflow (https://unix.stackexchange.com/a/227370,
;; https://unix.stackexchange.com/a/227361) and there is this somewhat related
;; snippet from the readdir(3) man page: "The order in which filenames are read
;; by successive calls to  readdir()  depends  on  the filesystem
;; implementation; it is unlikely that the names will be sorted in any
;; fashion."
(defund
  hifat-no-dups-p (m1-file-alist)
  (declare (xargs :guard (m1-file-alist-p m1-file-alist)))
  (cond ((atom m1-file-alist) t)
        ((not (hifat-no-dups-p (cdr m1-file-alist)))
         nil)
        ((not (mbt (and (consp (car m1-file-alist))
                        (stringp (car (car m1-file-alist))))))
         (not (member-equal (car m1-file-alist)
                            (cdr m1-file-alist))))
        ((consp (assoc-equal (caar m1-file-alist)
                             (cdr m1-file-alist)))
         nil)
        ((m1-directory-file-p (cdar m1-file-alist))
         (hifat-no-dups-p
          (m1-file->contents (cdar m1-file-alist))))
        (t t)))

(defthm hifat-no-dups-p-of-cdr
  (implies (hifat-no-dups-p fs)
           (hifat-no-dups-p (cdr fs)))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(defthm
  hifat-no-dups-p-of-m1-file-contents-of-cdar
  (implies (and (hifat-no-dups-p hifat-file-alist)
                (m1-file-alist-p hifat-file-alist)
                (m1-directory-file-p (cdr (car hifat-file-alist))))
           (hifat-no-dups-p (m1-file->contents (cdr (car hifat-file-alist)))))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(defun hifat-file-alist-fix (hifat-file-alist)
  (declare (xargs :guard (and (m1-file-alist-p hifat-file-alist)
                              (hifat-no-dups-p hifat-file-alist))
                  :verify-guards nil))
  (mbe
   :exec
   hifat-file-alist
   :logic
   (b*
       (((when (atom hifat-file-alist)) nil)
        (head (cons
               (fat32-filename-fix (caar hifat-file-alist))
               (m1-file-fix (cdar hifat-file-alist))))
        (tail (hifat-file-alist-fix (cdr hifat-file-alist)))
        ((when (consp (assoc-equal (car head) tail)))
         tail))
     (if
         (m1-directory-file-p (cdr head))
         (cons
          (cons (car head)
                (make-m1-file :dir-ent (m1-file->dir-ent (cdr head))
                              :contents (hifat-file-alist-fix (m1-file->contents (cdr head)))))
          tail)
       (cons head tail)))))

(defthm m1-file-alist-p-of-hifat-file-alist-fix
  (m1-file-alist-p (hifat-file-alist-fix hifat-file-alist)))

(defthm
  hifat-file-alist-fix-when-hifat-no-dups-p
  (implies (and (hifat-no-dups-p hifat-file-alist)
                (m1-file-alist-p hifat-file-alist))
           (equal (hifat-file-alist-fix hifat-file-alist)
                  hifat-file-alist))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(defthm
  hifat-no-dups-p-of-hifat-file-alist-fix
  (hifat-no-dups-p (hifat-file-alist-fix hifat-file-alist))
  :hints
  (("goal"
    :in-theory (enable hifat-no-dups-p)
    :induct (hifat-file-alist-fix hifat-file-alist))))

(defthm
  hifat-file-alist-fix-guard-lemma-1
  (implies (and (hifat-no-dups-p hifat-file-alist)
                (m1-file-alist-p hifat-file-alist)
                (consp hifat-file-alist)
                (consp (car hifat-file-alist)))
           (not (consp (assoc-equal (car (car hifat-file-alist))
                                    (cdr hifat-file-alist)))))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(verify-guards hifat-file-alist-fix)

;; This function returns *ENOENT* when the root directory is asked for. There's
;; a simple reason: we want to return the whole file, including the directory
;; entry - and nowhere is there a directory entry for the root. Any
;; directory other than the root will be caught before a recursive call which
;; makes it the root.
(defund hifat-find-file (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p pathname))
                  :measure (acl2-count pathname)))
  (b* ((fs (hifat-file-alist-fix fs))
       ((unless (consp pathname))
        (mv (make-m1-file) *enoent*))
       (name (mbe :logic (fat32-filename-fix (car pathname))
                  :exec (car pathname)))
       (alist-elem (assoc-equal name fs))
       ((unless (consp alist-elem))
        (mv (make-m1-file) *enoent*))
       ((when (m1-directory-file-p (cdr alist-elem)))
        (if (atom (cdr pathname))
            (mv (cdr alist-elem) 0)
          (hifat-find-file
           (m1-file->contents (cdr alist-elem))
           (cdr pathname))))
       ((unless (atom (cdr pathname)))
        (mv (make-m1-file) *enotdir*)))
    (mv (cdr alist-elem) 0)))

(defthm
  hifat-find-file-correctness-1-lemma-1
  (implies (and (m1-file-alist-p fs)
                (consp (assoc-equal filename fs)))
           (m1-file-p (cdr (assoc-equal filename fs)))))

(defthm
  hifat-find-file-correctness-1
  (mv-let (file error-code)
    (hifat-find-file fs pathname)
    (and (m1-file-p file)
         (integerp error-code)))
  :hints (("goal" :induct (hifat-find-file fs pathname)
           :in-theory (enable hifat-find-file))))

(defthm hifat-find-file-correctness-2
  (equal
   (hifat-find-file fs (fat32-filename-list-fix pathname))
   (hifat-find-file fs pathname))
  :hints (("Goal" :in-theory (enable hifat-find-file))))

(defthm hifat-find-file-of-hifat-file-alist-fix
  (equal (hifat-find-file (hifat-file-alist-fix fs) pathname)
         (hifat-find-file fs pathname))
  :hints (("Goal" :in-theory (enable hifat-find-file))))

(defcong fat32-filename-list-equiv equal (hifat-find-file fs pathname) 2
  :hints
  (("goal'"
    :in-theory (disable hifat-find-file-correctness-2)
    :use (hifat-find-file-correctness-2
          (:instance hifat-find-file-correctness-2
                     (pathname pathname-equiv))))))

(defthm
  m1-file-alist-p-of-put-assoc-equal
  (implies
   (m1-file-alist-p alist)
   (equal (m1-file-alist-p (put-assoc-equal name val alist))
          (and (fat32-filename-p name) (m1-file-p val)))))

(defund
  hifat-place-file
  (fs pathname file)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p pathname)
                              (m1-file-p file))
                  :measure (acl2-count pathname)))
  (b*
      ((fs (mbe :logic (hifat-file-alist-fix fs) :exec fs))
       (file (mbe :logic (m1-file-fix file)
                  :exec file))
       ;; Pathnames aren't going to be empty lists. Even the emptiest of
       ;; empty pathnames has to have at least a slash in it, because we are
       ;; absolutely dealing in absolute pathnames.
       ((unless (consp pathname))
        (mv fs *enoent*))
       (name (fat32-filename-fix (car pathname)))
       (alist-elem (assoc-equal name fs))
       ((unless (consp alist-elem))
        (if (atom (cdr pathname))
            (mv (put-assoc-equal name file fs) 0)
          (mv fs *enotdir*)))
       ((when (and (not (m1-directory-file-p (cdr alist-elem)))
                   (or (consp (cdr pathname))
                       ;; This is the case where a regular file could get replaced by
                       ;; a directory, which is a bad idea.
                       (m1-directory-file-p file))))
        (mv fs *enotdir*))
       ((when (not (or (m1-directory-file-p (cdr alist-elem))
                       (consp (cdr pathname))
                       (m1-directory-file-p file)
                       (and
                        (atom (assoc-equal name fs))
                        (>= (len fs) *ms-max-dir-ent-count*)))))
        (mv (put-assoc-equal name file fs) 0))
       ((when (and (atom (assoc-equal name fs)) (>= (len fs) *ms-max-dir-ent-count*)))
        (mv fs *enospc*))
       ((mv new-contents error-code)
        (hifat-place-file
         (m1-file->contents (cdr alist-elem))
         (cdr pathname)
         file)))
    (mv
     (put-assoc-equal
      name
      (make-m1-file :dir-ent (m1-file->dir-ent (cdr alist-elem))
                    :contents new-contents)
      fs)
     error-code)))

(defthm
  hifat-place-file-correctness-1
  (mv-let (fs error-code)
    (hifat-place-file fs pathname file)
    (and (m1-file-alist-p fs)
         (integerp error-code)))
  :hints
  (("goal" :in-theory (enable hifat-place-file)
    :induct (hifat-place-file fs pathname file))))

(defthm
  hifat-place-file-correctness-2
  (equal
   (hifat-place-file fs (fat32-filename-list-fix pathname)
                                 file)
   (hifat-place-file fs pathname file))
  :hints (("goal" :in-theory (enable hifat-place-file))))

(defthm hifat-place-file-of-hifat-file-alist-fix
  (equal
   (hifat-place-file (hifat-file-alist-fix fs) pathname file)
   (hifat-place-file fs pathname file))
  :hints (("goal" :in-theory (enable hifat-place-file))))

(defcong fat32-filename-list-equiv equal
  (hifat-place-file fs pathname file) 2
  :hints
  (("goal'"
    :in-theory
    (e/d
     (hifat-place-file)
     (hifat-place-file-correctness-2))
    :use (hifat-place-file-correctness-2
          (:instance hifat-place-file-correctness-2
                     (pathname pathname-equiv))))))

(defcong m1-file-equiv equal
  (hifat-place-file fs pathname file) 3
  :hints (("goal" :in-theory (enable hifat-place-file))))

(defthm hifat-no-dups-p-of-put-assoc-equal-1
  (implies
   (and (m1-file-alist-p m1-file-alist)
        (hifat-no-dups-p m1-file-alist)
        (m1-regular-file-p file))
   (hifat-no-dups-p (put-assoc-equal key file m1-file-alist)))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(defthm hifat-no-dups-p-of-put-assoc-equal-2
  (implies (and (m1-file-alist-p m1-file-alist)
                (hifat-no-dups-p m1-file-alist)
                (hifat-no-dups-p (m1-file->contents file)))
           (hifat-no-dups-p (put-assoc-equal key file m1-file-alist)))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(defthm
  hifat-place-file-correctness-3
  (implies
   (m1-regular-file-p file)
   (hifat-no-dups-p
    (mv-nth 0
            (hifat-place-file fs pathname file))))
  :hints
  (("goal" :in-theory (enable hifat-place-file))))

(defund
  hifat-remove-file (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p pathname))
                  :measure (acl2-count pathname)))
  (b*
      ((fs (mbe :logic (hifat-file-alist-fix fs) :exec fs))
       ((unless (consp pathname))
        (mv fs *enoent*))
       ;; Design choice - calls which ask for the entire root directory to be
       ;; affected will fail.
       (name (fat32-filename-fix (car pathname)))
       (alist-elem (assoc-equal name fs))
       ;; If it's not there, it can't be removed
       ((unless (consp alist-elem))
        (mv fs *enoent*))
       ;; Design choice - this lower-level function will unquestioningly delete
       ;; entire subdirectory trees, as long as they are not the root. It will
       ;; also remove all possible copies for the filename, even though we
       ;; try to avoid having multiple copies of a file, whether or not they're
       ;; identical.
       ((when (atom (cdr pathname)))
        (mv (remove-assoc-equal name fs) 0))
       ;; ENOTDIR - can't delete anything that supposedly exists inside a
       ;; regular file.
       ((unless (m1-directory-file-p (cdr alist-elem)))
        (mv fs *enotdir*))
       ;; Recursion
       ((mv new-contents error-code)
        (hifat-remove-file
         (m1-file->contents (cdr alist-elem))
         (cdr pathname))))
    (mv
     (put-assoc-equal
      name
      (make-m1-file :dir-ent (m1-file->dir-ent (cdr alist-elem))
                    :contents new-contents)
      fs)
     error-code)))

(defthm
  hifat-remove-file-correctness-1
  (mv-let (fs error-code)
    (hifat-remove-file fs pathname)
    (and (m1-file-alist-p fs)
         (integerp error-code)))
  :hints (("goal" :in-theory (enable hifat-remove-file)
           :induct (hifat-remove-file fs pathname)))
  :rule-classes
  ((:rewrite
    :corollary (m1-file-alist-p (mv-nth 0 (hifat-remove-file fs pathname))))
   (:type-prescription
    :corollary (integerp (mv-nth 1 (hifat-remove-file fs pathname))))
   (:type-prescription
    :corollary (not (stringp (mv-nth 0 (hifat-remove-file fs pathname)))))))

(defthm
  hifat-remove-file-correctness-2
  (equal
   (hifat-remove-file (hifat-file-alist-fix fs) pathname)
   (hifat-remove-file fs pathname))
  :hints (("goal" :in-theory (enable hifat-remove-file))))

(defthm
  hifat-remove-file-correctness-3-lemma-1
  (implies
   (and (m1-file-alist-p m1-file-alist)
        (hifat-no-dups-p m1-file-alist))
   (hifat-no-dups-p (remove-assoc-equal key m1-file-alist)))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(defthm
  hifat-remove-file-correctness-3
  (hifat-no-dups-p (mv-nth 0 (hifat-remove-file fs pathname)))
  :hints (("goal" :in-theory (enable hifat-remove-file))))

(defthm
  hifat-remove-file-correctness-4-lemma-1
  (implies (and (m1-file-alist-p z)
                (hifat-no-dups-p z)
                (m1-directory-file-p (cdr (assoc-equal key z))))
           (hifat-no-dups-p (m1-file->contents (cdr (assoc-equal key z)))))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p)) ))

(defthm hifat-remove-file-correctness-4
  (implies (not (equal (mv-nth 1 (hifat-remove-file fs pathname))
                       0))
           (equal (mv-nth 0 (hifat-remove-file fs pathname))
                  (hifat-file-alist-fix fs)))
  :hints (("goal" :in-theory (e/d (hifat-remove-file) (put-assoc-equal)))))

;; We decided to keep this around even though the motivation of preserving
;; fat32-filename-list-equiv is somewhat weak. The alternative is to use
;; prefixp (:doc prefixp) which is not built-in.
(defun fat32-filename-list-prefixp (x y)
  (declare (xargs :guard (and (fat32-filename-list-p x)
                              (fat32-filename-list-p y))))
  (if (consp x)
      (and (consp y)
           (fat32-filename-equiv (car x) (car y))
           (fat32-filename-list-prefixp (cdr x) (cdr y)))
    t))

(defthm fat32-filename-list-prefixp-of-self
  (fat32-filename-list-prefixp x x))

(defthm
  m1-read-after-write-lemma-2
  (implies (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (m1-directory-file-p (cdr (assoc-equal key fs))))
           (hifat-no-dups-p (m1-file->contents (cdr (assoc-equal key fs)))))
  :hints (("goal" :in-theory (enable hifat-no-dups-p))))

(encapsulate
  ()

  (local (in-theory (enable hifat-place-file
                            hifat-find-file
                            hifat-remove-file)))

  (local
   (defun
       induction-scheme
       (pathname1 pathname2 fs)
     (declare (xargs :guard (and (fat32-filename-list-p pathname1)
                                 (fat32-filename-list-p pathname2)
                                 (m1-file-alist-p fs))))
     (if
         (or (atom pathname1) (atom pathname2))
         1
       (if
           (not (fat32-filename-equiv (car pathname2) (car pathname1)))
           2
         (let*
             ((alist-elem (assoc-equal (fat32-filename-fix (car pathname1)) fs)))
           (if
               (atom alist-elem)
               3
             (if
                 (m1-directory-file-p (cdr alist-elem))
                 (induction-scheme (cdr pathname1)
                                   (cdr pathname2)
                                   (m1-file->contents (cdr alist-elem)))
               4)))))))

  (local
   (defthm
     m1-read-after-write-lemma-3
     (b*
         (((mv original-file original-error-code)
           (hifat-find-file fs pathname1))
          ((mv new-fs new-error-code)
           (hifat-place-file fs pathname2 file2)))
       (implies
        (and (m1-file-alist-p fs)
             (hifat-no-dups-p fs)
             (m1-regular-file-p file2)
             (equal original-error-code 0)
             (m1-regular-file-p original-file)
             (equal new-error-code 0))
        (equal (hifat-find-file new-fs pathname1)
               (if (fat32-filename-list-equiv pathname1 pathname2)
                   (mv file2 0)
                 (hifat-find-file fs pathname1)))))
     :hints
     (("goal" :induct (induction-scheme pathname1 pathname2 fs)
       :in-theory (enable m1-regular-file-p
                          fat32-filename-list-fix)))))

  (defthm
    m1-read-after-write
    (b*
        (((mv original-file original-error-code)
          (hifat-find-file fs pathname1))
         ((mv new-fs new-error-code)
          (hifat-place-file fs pathname2 file2)))
      (implies
       (and (m1-regular-file-p file2)
            (equal original-error-code 0)
            (m1-regular-file-p original-file)
            (equal new-error-code 0))
       (equal (hifat-find-file new-fs pathname1)
              (if (fat32-filename-list-equiv pathname1 pathname2)
                  (mv file2 0)
                (hifat-find-file fs pathname1)))))
    :hints
    (("goal" :induct (induction-scheme pathname1 pathname2 fs)
      :in-theory (enable m1-regular-file-p
                         fat32-filename-list-fix))))

  (local
   (defthm
     m1-read-after-create-lemma-1
     (b*
         (((mv & original-error-code)
           (hifat-find-file fs pathname1))
          ((mv new-fs new-error-code)
           (hifat-place-file fs pathname2 file2)))
       (implies
        (and (m1-file-alist-p fs)
             (hifat-no-dups-p fs)
             (m1-regular-file-p file2)
             (not (equal original-error-code 0))
             (equal new-error-code 0))
        (equal
         (hifat-find-file new-fs pathname1)
         (if (fat32-filename-list-equiv pathname1 pathname2)
             (mv file2 0)
           (if (fat32-filename-list-prefixp pathname2 pathname1)
               (mv (make-m1-file) *enotdir*)
             (hifat-find-file fs pathname1))))))
     :hints
     (("goal" :induct (induction-scheme pathname1 pathname2 fs)
       :in-theory (enable fat32-filename-list-fix
                          m1-regular-file-p)))))

  (defthm
    m1-read-after-create
    (b*
        (((mv & original-error-code)
          (hifat-find-file fs pathname1))
         ((mv new-fs new-error-code)
          (hifat-place-file fs pathname2 file2)))
      (implies
       (and (m1-regular-file-p file2)
            (not (equal original-error-code 0))
            (equal new-error-code 0))
       (equal
        (hifat-find-file new-fs pathname1)
        (if (fat32-filename-list-equiv pathname1 pathname2)
            (mv file2 0)
          (if (fat32-filename-list-prefixp pathname2 pathname1)
              (mv (make-m1-file) *enotdir*)
            (hifat-find-file fs pathname1))))))
    :hints
    (("goal" :induct (induction-scheme pathname1 pathname2 fs)
      :in-theory (enable fat32-filename-list-fix
                         m1-regular-file-p))))

  (local
   (defthm
     m1-read-after-delete-lemma-2
     (implies
      (equal (mv-nth 1 (hifat-find-file fs pathname))
             *enoent*)
      (equal (hifat-find-file fs pathname)
             (mv (make-m1-file) *enoent*)))))

  (local
   (defthmd
     m1-read-after-delete-lemma-3
     (b* (((mv & error-code)
           (hifat-find-file fs pathname1))
          ((mv new-fs &)
           (hifat-remove-file fs pathname2)))
       (implies (and
                 (m1-file-alist-p fs)
                 (hifat-no-dups-p fs)
                 (equal error-code *enoent*))
                (equal (hifat-find-file new-fs pathname1)
                       (mv (make-m1-file) *enoent*))))
     :hints
     (("goal" :induct (induction-scheme pathname1 pathname2 fs)
       :in-theory (enable fat32-filename-list-fix
                          m1-regular-file-p)
       :expand
       ((:free (fs)
               (hifat-find-file fs pathname1))
        (:free (fs)
               (hifat-remove-file fs pathname2)))))))

  (local
   (defthmd
     m1-read-after-delete-lemma-4
     (b*
         (((mv original-file &)
           (hifat-find-file fs pathname1))
          ((mv new-fs error-code)
           (hifat-remove-file fs pathname2)))
       (implies
        (and
         (m1-file-alist-p fs)
         (hifat-no-dups-p fs)
         (m1-regular-file-p original-file))
        (equal
         (hifat-find-file new-fs pathname1)
         (if (and (fat32-filename-list-prefixp pathname2 pathname1)
                  (equal error-code 0))
             (mv (make-m1-file) *enoent*)
           (hifat-find-file fs pathname1)))))
     :hints
     (("goal" :induct (induction-scheme pathname1 pathname2 fs)
       :in-theory (enable fat32-filename-list-fix
                          m1-regular-file-p)))))

  (local
   (defthmd
     m1-read-after-delete-lemma-1
     (b*
         (((mv original-file original-error-code)
           (hifat-find-file fs pathname1))
          ((mv new-fs new-error-code)
           (hifat-remove-file fs pathname2)))
       (implies
        (and
         (m1-file-alist-p fs)
         (hifat-no-dups-p fs)
         (or (equal original-error-code *enoent*)
             (m1-regular-file-p original-file)))
        (equal
         (hifat-find-file new-fs pathname1)
         (if
             (or
              (equal original-error-code *enoent*)
              (and (equal new-error-code 0)
                   (fat32-filename-list-prefixp pathname2 pathname1)))
             (mv (make-m1-file) *enoent*)
           (hifat-find-file fs pathname1)))))
     :hints (("goal" :use (m1-read-after-delete-lemma-4
                           m1-read-after-delete-lemma-3)))))

  (defthm
    m1-read-after-delete
    (b*
        (((mv original-file original-error-code)
          (hifat-find-file fs pathname1))
         ((mv new-fs new-error-code)
          (hifat-remove-file fs pathname2)))
      (implies
       (or (equal original-error-code *enoent*)
           (m1-regular-file-p original-file))
       (equal
        (hifat-find-file new-fs pathname1)
        (if
            (or
             (equal original-error-code *enoent*)
             (and (equal new-error-code 0)
                  (fat32-filename-list-prefixp pathname2 pathname1)))
            (mv (make-m1-file) *enoent*)
          (hifat-find-file fs pathname1)))))
    :hints (("Goal"
             :use (:instance m1-read-after-delete-lemma-1
                             (fs (hifat-file-alist-fix fs)))) )))

(defun
    find-new-index-helper (fd-list candidate)
  (declare (xargs :guard (and (nat-listp fd-list) (natp candidate))
                  :measure (len fd-list)))
  (let ((snipped-list (remove1 candidate fd-list)))
    (if (equal (len snipped-list) (len fd-list))
        candidate
      (find-new-index-helper snipped-list (+ candidate 1)))))

(defthm find-new-index-helper-correctness-1-lemma-1
  (>= (find-new-index-helper fd-list candidate) candidate)
  :rule-classes :linear)

(defthm
  find-new-index-helper-correctness-1-lemma-2
  (implies (integerp candidate)
           (integerp (find-new-index-helper fd-list candidate)))
  :rule-classes :type-prescription)

(defthm
  find-new-index-helper-correctness-1
  (not (member-equal
        (find-new-index-helper fd-list candidate)
        fd-list)))

(defund
  find-new-index (fd-list)
  (declare (xargs :guard (nat-listp fd-list)))
  (find-new-index-helper fd-list 0))

(defthm find-new-index-correctness-1-lemma-1
  (>= (find-new-index fd-list) 0)
  :hints (("Goal" :in-theory (enable find-new-index)))
  :rule-classes :linear)

(defthm
  find-new-index-correctness-1-lemma-2
  (integerp (find-new-index fd-list))
  :hints (("Goal" :in-theory (enable find-new-index)))
  :rule-classes :type-prescription)

(defthm
  find-new-index-correctness-1
  (not (member-equal
        (find-new-index fd-list)
        fd-list))
  :hints (("Goal" :in-theory (enable find-new-index))))

;; Here's a problem with our current formulation: realpath-helper will receive
;; something that was emitted by pathname-to-fat32-pathname, and that means all
;; absolute paths will start with *empty-fat32-name* or "        ". That's
;; problematic because then anytime we have to compute the realpath of "/.." or
;; "/home/../.." we will return something that breaks this convention of having
;; absolute paths begin with *empty-fat32-name*. Most likely, the convention
;; itself is hard to sustain.
(defun realpath-helper (pathname ac)
  (cond ((atom pathname) (revappend ac nil))
        ((equal (car pathname)
                *current-dir-fat32-name*)
         (realpath-helper (cdr pathname) ac))
        ((equal (car pathname)
                *parent-dir-fat32-name*)
         (realpath-helper (cdr pathname)
                          (cdr ac)))
        (t (realpath-helper (cdr pathname)
                            (cons (car pathname) ac)))))

(defthm
  realpath-helper-correctness-1
  (implies
   (and (not (member-equal *current-dir-fat32-name* pathname))
        (not (member-equal *parent-dir-fat32-name* pathname)))
   (equal (realpath-helper pathname ac)
          (revappend ac (true-list-fix pathname))))
  :hints
  (("goal" :in-theory (disable (:rewrite revappend-removal)
                               revappend-of-true-list-fix)
    :induct (realpath-helper pathname ac))
   ("subgoal *1/1"
    :use (:instance revappend-of-true-list-fix (x ac)
                    (y pathname)))))

(defund realpath (relpathname abspathname)
  (realpath-helper (append abspathname relpathname) nil))

(defthm
  realpath-correctness-1
  (implies
   (and (not (member-equal *current-dir-fat32-name* (append abspathname relpathname)))
        (not (member-equal *parent-dir-fat32-name* (append abspathname relpathname))))
   (equal (realpath relpathname abspathname)
          (true-list-fix
           (append abspathname relpathname))))
  :hints
  (("goal" :in-theory (enable realpath))))

(defun
    name-to-fat32-name-helper
    (character-list n)
  (declare
   (xargs :guard (and (natp n)
                      (character-listp character-list))))
  (if (zp n)
      nil
    (if (atom character-list)
        (make-list n :initial-element #\space)
      (cons (str::upcase-char (car character-list))
            (name-to-fat32-name-helper (cdr character-list)
                                       (- n 1))))))

(defthm
  len-of-name-to-fat32-name-helper
  (equal (len (name-to-fat32-name-helper character-list n))
         (nfix n)))

;; (defthm name-to-fat32-name-helper-correctness-1
;;   (implies (member x (name-to-fat32-name-helper
;;                       character-list n))
;;            (or (equal x #\space) (str::up-alpha-p x))))

(defthm
  character-listp-of-name-to-fat32-name-helper
  (character-listp (name-to-fat32-name-helper character-list n))
  :hints (("goal" :in-theory (disable make-list-ac-removal))))

(defund
  name-to-fat32-name (character-list)
  (declare (xargs :guard (character-listp character-list)))
  (b*
      (((when (equal (coerce character-list 'string) *current-dir-name*))
        (coerce *current-dir-fat32-name* 'list))
       ((when (equal (coerce character-list 'string) *parent-dir-name*))
        (coerce *parent-dir-fat32-name* 'list))
       (dot-and-later-characters (member #\. character-list))
       (characters-before-dot
        (take (- (len character-list) (len dot-and-later-characters))
              character-list))
       (normalised-characters-before-dot
        (name-to-fat32-name-helper characters-before-dot 8))
       ((when (atom dot-and-later-characters))
        (append normalised-characters-before-dot
                (make-list 3 :initial-element #\space)))
       (characters-after-dot (cdr dot-and-later-characters))
       (second-dot-and-later-characters (member #\. characters-after-dot))
       (extension (take (- (len characters-after-dot)
                           (len second-dot-and-later-characters))
                        characters-after-dot))
       (normalised-extension
        (name-to-fat32-name-helper extension 3)))
    (append normalised-characters-before-dot normalised-extension)))

(assert-event
 (and
  (equal (name-to-fat32-name (coerce "6chars" 'list))
         (coerce "6CHARS     " 'list))
  (equal (name-to-fat32-name (coerce "6chars.h" 'list))
         (coerce "6CHARS  H  " 'list))
  (equal (name-to-fat32-name (coerce "6chars.txt" 'list))
         (coerce "6CHARS  TXT" 'list))
  (equal (name-to-fat32-name (coerce "6chars.6chars" 'list))
         (coerce "6CHARS  6CH" 'list))
  (equal (name-to-fat32-name (coerce "6chars.6ch" 'list))
         (coerce "6CHARS  6CH" 'list))
  (equal (name-to-fat32-name (coerce "11characters.6chars" 'list))
         (coerce "11CHARAC6CH" 'list))
  (equal (name-to-fat32-name (coerce "11characters.1.1.1" 'list))
         (coerce "11CHARAC1  " 'list))
  (equal (name-to-fat32-name (coerce "11characters.1.1" 'list))
         (coerce "11CHARAC1  " 'list))))

(defthm
  character-listp-of-name-to-fat32-name
  (character-listp (name-to-fat32-name character-list))
  :hints (("goal" :in-theory (enable name-to-fat32-name))))

(defun
    fat32-name-to-name-helper
    (character-list n)
  (declare (xargs :guard (and (natp n)
                              (character-listp character-list)
                              (<= n (len character-list)))))
  (if (zp n)
      nil
    (if (equal (nth (- n 1) character-list)
               #\space)
        (fat32-name-to-name-helper character-list (- n 1))
      (str::downcase-charlist (take n character-list)))))

(defthm
  character-listp-of-fat32-name-to-name-helper
  (character-listp
   (fat32-name-to-name-helper
    character-list n)))

(defun fat32-name-to-name (character-list)
  (declare (xargs :guard (and (character-listp character-list)
                              (equal (len character-list) 11))))
  (b*
      (((when (equal (coerce character-list 'string) *current-dir-fat32-name*))
        (coerce *current-dir-name* 'list))
       ((when (equal (coerce character-list 'string) *parent-dir-fat32-name*))
        (coerce *parent-dir-name* 'list))
       (characters-before-dot
        (fat32-name-to-name-helper (take 8 character-list) 8))
       (characters-after-dot
        (fat32-name-to-name-helper (subseq character-list 8 11) 3))
       ((when (atom characters-after-dot))
        characters-before-dot))
    (append characters-before-dot (list #\.) characters-after-dot)))

(assert-event
 (and
  (equal (fat32-name-to-name (coerce "6CHARS     " 'list))
         (coerce "6chars" 'list))
  (equal (fat32-name-to-name (coerce "6CHARS  H  " 'list))
         (coerce "6chars.h" 'list))
  (equal (fat32-name-to-name (coerce "6CHARS  TXT" 'list))
         (coerce "6chars.txt" 'list))
  (equal (fat32-name-to-name (coerce "6CHARS  6CH" 'list))
         (coerce "6chars.6ch" 'list))
  (equal (fat32-name-to-name (coerce "11CHARAC6CH" 'list))
         (coerce "11charac.6ch" 'list))
  (equal (fat32-name-to-name (coerce "11CHARAC1  " 'list))
         (coerce "11charac.1" 'list))))

;; We're combining two operations into one here - a different approach would be
;; to have two recursive functions for drawing out the different
;; slash-delimited strings and then for transforming the resulting list
;; element-by-element to a list of fat32 names.
;; This function now necessitates unconditionally using absolute paths every
;; place where its return value is the argument to something else. Perhaps we
;; can have one layer of abstraction for generating the absolute path, but
;; right now we don't have any per-process data structure for storing the
;; current directory, nor are we planning to implement chdir.
(defund pathname-to-fat32-pathname (character-list)
  (declare (xargs :guard (character-listp character-list)))
  (b*
      (((when (atom character-list))
        nil)
       (slash-and-later-characters
        (member #\/ character-list))
       (characters-before-slash (take (- (len character-list)
                                         (len slash-and-later-characters))
                                      character-list))
       ((when (atom characters-before-slash))
        (pathname-to-fat32-pathname (cdr slash-and-later-characters)))
       ;; We want to treat anything that ends with a slash the same way we
       ;; would if the slash weren't there.
       ((when (or (atom slash-and-later-characters)
                  (equal slash-and-later-characters (list #\/))))
        (list
         (coerce (name-to-fat32-name characters-before-slash) 'string))))
    (cons
     (coerce (name-to-fat32-name characters-before-slash) 'string)
     (pathname-to-fat32-pathname (cdr slash-and-later-characters)))))

(assert-event
 (and
  (equal (pathname-to-fat32-pathname (coerce "/bin/mkdir" 'list))
         (list "BIN        " "MKDIR      "))
  (equal (pathname-to-fat32-pathname (coerce "//bin//mkdir" 'list))
         (list "BIN        " "MKDIR      "))
  (equal (pathname-to-fat32-pathname (coerce "/bin/" 'list))
         (list "BIN        "))
  (equal (pathname-to-fat32-pathname (coerce "books/build/cert.pl" 'list))
         (list "BOOKS      " "BUILD      " "CERT    PL "))
  (equal (pathname-to-fat32-pathname (coerce "books/build/" 'list))
         (list "BOOKS      " "BUILD      "))))

;; for later
;; (defthmd pathname-to-fat32-pathname-correctness-1
;;   (implies
;;    (and (character-listp character-list)
;;         (consp character-list)
;;         (equal (last character-list)
;;                (coerce "\/" 'list)))
;;    (equal
;;     (pathname-to-fat32-pathname (take (- (len character-list) 1)
;;                                       character-list))
;;     (pathname-to-fat32-pathname character-list)))
;;   :hints (("Goal"
;;            :induct (pathname-to-fat32-pathname character-list)
;;            :in-theory (disable name-to-fat32-name)
;;            :expand (PATHNAME-TO-FAT32-PATHNAME (TAKE (+ -1 (LEN CHARACTER-LIST))
;;                                                      CHARACTER-LIST))) ))

(defun fat32-pathname-to-pathname (string-list)
  ;; (declare (xargs :guard (string-listp string-list)))
  (if (atom string-list)
      nil
    (append (fat32-name-to-name (coerce (car string-list) 'list))
            (if (atom (cdr string-list))
                nil
              (list* #\/
                     (fat32-pathname-to-pathname (cdr string-list)))))))

(assert-event
 (and
  (equal (coerce (fat32-pathname-to-pathname (list "BOOKS      " "BUILD      "
                                                   "CERT    PL "))
                 'string)
         "books/build/cert.pl")
  (equal (coerce (fat32-pathname-to-pathname (list "           " "BIN        "
                                                   "MKDIR      "))
                 'string)
         "/bin/mkdir")))

(defthm character-listp-of-fat32-pathname-to-pathname
  (character-listp (fat32-pathname-to-pathname string-list)))
