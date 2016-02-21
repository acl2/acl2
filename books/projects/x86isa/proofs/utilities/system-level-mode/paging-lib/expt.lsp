(in-package "X86ISA")

(include-book "gather-paging-structures")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "std/lists/remove-duplicates" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

(defthmd |(rm-low-32 addr2 (xw :mem addr1 val x86)) --- member addr|
  (implies (and (member-p addr-1 (addr-range 4 addr-2))
                (physical-address-p addr-2)
                (not (programmer-level-mode x86)))
           (equal (rm-low-32 addr-2 (xw :mem addr-1 val x86))
                  (cond ((equal addr-1 addr-2)
                         (b* ((byte0 val)
                              (byte1 (memi (+ 1 addr-2) x86))
                              (byte2 (memi (+ 2 addr-2) x86))
                              (byte3 (memi (+ 3 addr-2) x86))
                              (word0 (logior (ash byte1 8) byte0))
                              (word1 (logior (ash byte3 8) byte2))
                              (dword (logior (ash word1 16) word0)))
                           dword))
                        ((equal addr-1 (+ 1 addr-2))
                         (b* ((byte0 (memi addr-2 x86))
                              (byte1 val)
                              (byte2 (memi (+ 2 addr-2) x86))
                              (byte3 (memi (+ 3 addr-2) x86))
                              (word0 (logior (ash byte1 8) byte0))
                              (word1 (logior (ash byte3 8) byte2))
                              (dword (logior (ash word1 16) word0)))
                           dword))
                        ((equal addr-1 (+ 2 addr-2))
                         (b* ((byte0 (memi addr-2 x86))
                              (byte1 (memi (+ 1 addr-2) x86))
                              (byte2 val)
                              (byte3 (memi (+ 3 addr-2) x86))
                              (word0 (logior (ash byte1 8) byte0))
                              (word1 (logior (ash byte3 8) byte2))
                              (dword (logior (ash word1 16) word0)))
                           dword))
                        ((equal addr-1 (+ 3 addr-2))
                         (b* ((byte0 (memi addr-2 x86))
                              (byte1 (memi (+ 1 addr-2) x86))
                              (byte2 (memi (+ 2 addr-2) x86))
                              (byte3 val)
                              (word0 (logior (ash byte1 8) byte0))
                              (word1 (logior (ash byte3 8) byte2))
                              (dword (logior (ash word1 16) word0)))
                           dword)))))
  :hints (("Goal" :in-theory (e/d* (rm-low-32) (force (force))))))

(local
 (encapsulate
   ()

   (defthmd |(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|-helper-1
     (implies (and (physical-address-p addr-2)
                   (member-p addr-1 (addr-range 4 addr-2)))
              (disjoint-p (addr-range 1 addr-1)
                          (addr-range 4 (+ 4 addr-2))))
     :hints (("Goal"
              :expand ((addr-range 4 (+ 4 addr-2))
                       (addr-range 3 (+ 5 addr-2)))
              :in-theory (e/d* (disjoint-p member-p) ()))))

   (defthmd |(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|-helper-2
     (implies (and (physical-address-p addr-2)
                   (member-p addr-1 (addr-range 4 (+ 4 addr-2))))
              (disjoint-p (addr-range 1 addr-1)
                          (addr-range 4 addr-2)))
     :hints (("Goal"
              :expand ((addr-range 4 (+ 4 addr-2))
                       (addr-range 3 (+ 5 addr-2)))
              :in-theory (e/d* (disjoint-p member-p) ()))))

   (defthmd |(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|-helper-3
     (implies (and (member-p addr-1 (addr-range 8 addr-2))
                   (physical-address-p addr-2)
                   (not (member-p addr-1 (addr-range 4 (+ 4 addr-2)))))
              (member-p addr-1 (addr-range 4 addr-2)))
     :hints (("Goal"
              :expand ((addr-range 8 addr-2)
                       (addr-range 7 (+ 1 addr-2))
                       (addr-range 6 (+ 2 addr-2)))
              :in-theory (e/d* (member-p disjoint-p) ()))))))

(defthmd |(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|
  (implies (and (member-p addr-1 (addr-range 8 addr-2))
                (physical-address-p addr-1)
                (physical-address-p addr-2)
                (not (programmer-level-mode x86)))
           (equal (rm-low-64 addr-2 (xw :mem addr-1 val x86))
                  (if (member-p addr-1 (addr-range 4 addr-2))
                      (b* ((dword0 (rm-low-32 addr-2 (xw :mem addr-1 val x86)))
                           (dword1 (rm-low-32 (+ 4 addr-2) x86))
                           (qword (logior (ash dword1 32) dword0)))
                        qword)
                    (b* ((dword0 (rm-low-32 addr-2 x86))
                         (dword1 (rm-low-32 (+ 4 addr-2) (xw :mem addr-1 val x86)))
                         (qword (logior (ash dword1 32) dword0)))
                      qword))))
  :hints (("Goal"
           :use ((:instance |(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|-helper-1)
                 (:instance |(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|-helper-2)
                 (:instance |(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|-helper-3))
           :in-theory (e/d* (rm-low-64 member-p disjoint-p)
                            (|(rm-low-32 addr2 (xw :mem addr1 val x86)) --- member addr|
                             force (force))))))

;; ======================================================================

(defthmd xlate-equiv-entries-expressed-in-equality-of-bytes
  (implies (and (unsigned-byte-p 64 one)
                (unsigned-byte-p 64 two)
                (xlate-equiv-entries one two))
           (b* ((one-0 (part-select one :low 0 :width 8))
                (one-1 (part-select one :low 8 :width 8))
                (one-2 (part-select one :low 16 :width 8))
                (one-3 (part-select one :low 24 :width 8))
                (one-4 (part-select one :low 32 :width 8))
                (one-5 (part-select one :low 40 :width 8))
                (one-6 (part-select one :low 48 :width 8))
                (one-7 (part-select one :low 56 :width 8))
                (two-0 (part-select two :low 0 :width 8))
                (two-1 (part-select two :low 8 :width 8))
                (two-2 (part-select two :low 16 :width 8))
                (two-3 (part-select two :low 24 :width 8))
                (two-4 (part-select two :low 32 :width 8))
                (two-5 (part-select two :low 40 :width 8))
                (two-6 (part-select two :low 48 :width 8))
                (two-7 (part-select two :low 56 :width 8)))
             (and (equal (part-select one-0 :low 0 :high 4)
                         (part-select two-0 :low 0 :high 4))
                  (equal (part-select one-1 :low 7 :high 7)
                         (part-select two-1 :low 7 :high 7))
                  (equal one-2 two-2)
                  (equal one-3 two-3)
                  (equal one-4 two-4)
                  (equal one-5 two-5)
                  (equal one-6 two-6)
                  (equal one-7 two-7))))
  :hints (("Goal"
           :use ((:instance logtail-bigger (e-1 one) (e-2 two) (m 8) (n 16))
                 (:instance logtail-bigger (e-1 one) (e-2 two) (m 8) (n 24))
                 (:instance logtail-bigger (e-1 one) (e-2 two) (m 8) (n 32))
                 (:instance logtail-bigger (e-1 one) (e-2 two) (m 8) (n 40))
                 (:instance logtail-bigger (e-1 one) (e-2 two) (m 8) (n 48))
                 (:instance logtail-bigger (e-1 one) (e-2 two) (m 8) (n 57))
                 (:instance logtail-bigger-and-logbitp (e-1 one) (e-2 two) (m 8) (n 56)))
           :in-theory (e/d* (xlate-equiv-entries
                             bitops::ihsext-inductions
                             bitops::ihsext-recursive-redefs)
                            ()))))

(defthm rm-low-64-open-only-if-x86
  (implies (and (syntaxp (not (consp x86)))
                (integerp addr)
                (not (programmer-level-mode x86)))
           (equal (rm-low-64 addr x86)
                  (b* ((dword0 (rm-low-32 addr x86))
                       (dword1 (rm-low-32 (+ 4 addr) x86))
                       (qword (logior (ash dword1 32) dword0)))
                    qword)))
  :hints (("Goal" :in-theory (e/d* (rm-low-64) ()))))

(def-gl-export equality-of-logior-expressions-for-rm-low-32
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p w) (n08p x) (n08p y) (n08p z))
  :concl (equal (equal (logior a (ash (logior b (ash (logior c (ash d 8)) 8)) 8))
                       (logior w (ash (logior x (ash (logior y (ash z 8)) 8)) 8)))
                (and (equal a w) (equal b x) (equal c y) (equal d z)))

  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat w 8) (:nat x 8) (:nat y 8) (:nat z 8))))

(def-gl-export equality-of-logior-expressions-for-rm-low-64
  :hyp (and (n32p a) (n32p b)
            (n32p w) (n32p x))
  :concl (equal (equal (logior a (ash b 32)) (logior w (ash x 32)))
                (and (equal a w) (equal b x)))

  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 32) (:nat b 32)
         (:nat w 32) (:nat x 32))))

;; Pick-a-byte proof strategy:

(defthm rewrite-equality-of-two-rm-low-32s-to-that-of-memis
  (implies
   (and (not (programmer-level-mode x86-1))
        (not (programmer-level-mode x86-2))
        (x86p x86-1)
        (x86p x86-2)
        (integerp addr-1)
        (integerp addr-2))
   (equal (equal (rm-low-32 addr-1 x86-1)
                 (rm-low-32 addr-2 x86-2))
          (and (equal (memi addr-1 x86-1)
                      (memi addr-2 x86-2))
               (equal (memi (+ 1 addr-1) x86-1)
                      (memi (+ 1 addr-2) x86-2))
               (equal (memi (+ 2 addr-1) x86-1)
                      (memi (+ 2 addr-2) x86-2))
               (equal (memi (+ 3 addr-1) x86-1)
                      (memi (+ 3 addr-2) x86-2)))))
  :hints (("Goal" :in-theory (e/d* (rm-low-32) (force (force))))))

(defthm rewrite-equality-of-two-rm-low-64s-to-that-of-rm-low-32s
  (implies
   (and (not (programmer-level-mode x86-1))
        (not (programmer-level-mode x86-2))
        (x86p x86-1)
        (x86p x86-2)
        (integerp addr-1)
        (integerp addr-2))
   (equal (equal (rm-low-64 addr-1 x86-1)
                 (rm-low-64 addr-2 x86-2))
          (and (equal (rm-low-32 addr-1 x86-1)
                      (rm-low-32 addr-2 x86-2))
               (equal (rm-low-32 (+ 4 addr-1) x86-1)
                      (rm-low-32 (+ 4 addr-2) x86-2)))))
  :hints (("Goal" :in-theory (e/d* (rm-low-64) (force (force))))))

(def-gl-export xlate-equiv-of-logior-expressions-for-rm-low-64
  :hyp (and (n64p a) (n64p b))
  :concl (iff (xlate-equiv-entries a b)
              (and (equal (loghead 5 (loghead 32 a))
                          (loghead 5 (loghead 32 b)))
                   (equal (logtail 7 (loghead 32 a))
                          (logtail 7 (loghead 32 b)))
                   (equal (logtail 32 a)
                          (logtail 32 b))))
  :g-bindings (gl::auto-bindings (:mix (:nat a 64) (:nat b 64))))

(def-gl-export n32p-open-rm-low-64
  :hyp (and (n32p a) (n32p b))
  :concl (unsigned-byte-p 64 (logior a (ash b 32)))
  :g-bindings (gl::auto-bindings (:mix (:nat a 32) (:nat b 32))))

(defthm rewrite-xlate-equiv-of-two-rm-low-64s
  (implies
   (and (not (programmer-level-mode x86-1))
        (not (programmer-level-mode x86-2))
        (x86p x86-1)
        (x86p x86-2)
        (integerp addr-1)
        (integerp addr-2))
   (equal (xlate-equiv-entries (rm-low-64 addr-1 x86-1)
                               (rm-low-64 addr-2 x86-2))
          (and (equal (loghead 5 (rm-low-32 addr-1 x86-1))
                      (loghead 5 (rm-low-32 addr-2 x86-2)))
               (equal (logtail 7 (rm-low-32 addr-1 x86-1))
                      (logtail 7 (rm-low-32 addr-2 x86-2)))
               (equal (rm-low-32 (+ 4 addr-1) x86-1)
                      (rm-low-32 (+ 4 addr-2) x86-2)))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-of-logior-expressions-for-rm-low-64
                            (a (rm-low-64 addr-1 x86-1))
                            (b (rm-low-64 addr-2 x86-2))))
           :in-theory (e/d* ()
                            (rewrite-equality-of-two-rm-low-32s-to-that-of-memis
                             xlate-equiv-of-logior-expressions-for-rm-low-64
                             force (force))))))

(local
 (defthmd xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-1
   (implies (and (xlate-equiv-entries (rm-low-64 addr-2 x86-1)
                                      (rm-low-64 addr-2 x86-2))
                 (not (member-p addr-1 (addr-range 8 addr-2)))
                 (physical-address-p addr-1))
            (xlate-equiv-entries (rm-low-64 addr-2 (xw :mem addr-1 value x86-1))
                                 (rm-low-64 addr-2 (xw :mem addr-1 value x86-2))))
   :hints (("Goal"
            :in-theory (e/d* (xlate-equiv-entries disjoint-p member-p) ())))))

(defthm rm-low-32-and-loghead-parts
  (implies (and (not (programmer-level-mode x86))
                (integerp addr)
                (x86p x86))
           (equal (loghead 8 (rm-low-32 addr x86))
                  (memi addr x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-32) ()))))

(def-gl-export xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-2-helper-1
  :hyp (and (equal x (loghead 8 a))
            (equal y (loghead 8 b))
            (syntaxp (and (consp a) (equal (car a) 'rm-low-32)
                          (consp b) (equal (car b) 'rm-low-32)))
            (equal (loghead 5 a) (loghead 5 b))
            (n32p a) (n32p b))
  :concl (equal (loghead 5 x) (loghead 5 y))
  :g-bindings (gl::auto-bindings (:mix (:nat a 32) (:nat b 32)))
  :rule-classes nil)

(defthmd rm-low-32-open-only-if-x86
  (implies (and (syntaxp (not (consp x86)))
                (integerp addr)
                (not (programmer-level-mode x86)))
           (equal (rm-low-32 addr x86)
                  (b* ((byte0 (memi addr x86))
                       (byte1 (memi (1+ addr) x86))
                       (word0 (logior (ash byte1 8) byte0))
                       (byte2 (memi (+ 2 addr) x86))
                       (byte3 (memi (+ 3 addr) x86))
                       (word1 (logior (ash byte3 8) byte2))
                       (dword (logior (ash word1 16) word0)))
                    dword)))
  :hints (("Goal" :in-theory (e/d* (rm-low-32) ()))))

(def-gl-export equality-of-logior-expressions-inside-rm-low-32-1
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p w) (n08p x) (n08p y) (n08p z)
            (equal (loghead 5 a) (loghead 5 w))
            (equal (logior (logtail 7 a) (ash (logior b (ash (logior c (ash d 8)) 8)) 1))
                   (logior (logtail 7 w) (ash (logior x (ash (logior y (ash z 8)) 8)) 1))))
  :concl (equal (ash (logior b (ash (logior c (ash d 8)) 8)) 1)
                (ash (logior x (ash (logior y (ash z 8)) 8)) 1))

  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat w 8) (:nat x 8) (:nat y 8) (:nat z 8)))
  :rule-classes nil)

(def-gl-export equality-of-logior-expressions-inside-rm-low-32-2
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p w) (n08p x) (n08p y) (n08p z)
            (equal (loghead 5 a) (loghead 5 w))
            (equal (logior (logtail 7 a) (ash (logior b (ash (logior c (ash d 8)) 8)) 1))
                   (logior (logtail 7 w) (ash (logior x (ash (logior y (ash z 8)) 8)) 1))))
  :concl (equal (logior (logtail 7 a) (ash (logior c (ash d 8)) 9))
                (logior (logtail 7 w) (ash (logior y (ash z 8)) 9)))

  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat w 8) (:nat x 8) (:nat y 8) (:nat z 8)))
  :rule-classes nil)

(def-gl-export equality-of-logior-expressions-inside-rm-low-32-3
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p w) (n08p x) (n08p y) (n08p z)
            (n08p value)
            (equal (loghead 5 a) (loghead 5 w))
            (equal (logior (logtail 7 a) (ash (logior b (ash (logior c (ash d 8)) 8)) 1))
                   (logior (logtail 7 w) (ash (logior x (ash (logior y (ash z 8)) 8)) 1))))
  :concl (equal (logior (logtail 7 a) (ash (logior b (ash (logior value (ash d 8)) 8)) 1))
                (logior (logtail 7 w) (ash (logior x (ash (logior value (ash z 8)) 8)) 1)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat w 8) (:nat x 8) (:nat y 8) (:nat z 8)
         (:nat value 8)))
  :rule-classes nil)

(def-gl-export equality-of-logior-expressions-inside-rm-low-32-4
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p w) (n08p x) (n08p y) (n08p z)
            (n08p value)
            (equal (loghead 5 a) (loghead 5 w))
            (equal (logior (logtail 7 a) (ash (logior b (ash (logior c (ash d 8)) 8)) 1))
                   (logior (logtail 7 w) (ash (logior x (ash (logior y (ash z 8)) 8)) 1))))
  :concl (equal (logior (logtail 7 a) (ash b 1) (ash (logior (ash value 8) c) 9))
                (logior (logtail 7 w) (ash x 1) (ash (logior (ash value 8) y) 9)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat w 8) (:nat x 8) (:nat y 8) (:nat z 8)
         (:nat value 8)))
  :rule-classes nil)

(local
 (defthmd xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-2
   (implies (and (xlate-equiv-entries (rm-low-64 addr-2 x86-1)
                                      (rm-low-64 addr-2 x86-2))
                 ;; Case 2: addr-1 = (addr-2 to (+ 4 addr-2)).
                 (member-p addr-1 (addr-range 4 addr-2))
                 (physical-address-p addr-1)
                 (physical-address-p addr-2)
                 (unsigned-byte-p 8 value)
                 (not (programmer-level-mode x86-1))
                 (not (programmer-level-mode x86-2))
                 (x86p x86-1)
                 (x86p x86-2))
            (xlate-equiv-entries (rm-low-64 addr-2 (xw :mem addr-1 value x86-1))
                                 (rm-low-64 addr-2 (xw :mem addr-1 value x86-2))))
   :hints (("Goal"
            :in-theory (e/d* (disjoint-p
                              member-p
                              |(rm-low-32 addr2 (xw :mem addr1 val x86)) --- member addr|)
                             (force (force))))
           ("Subgoal 1"
            :use ((:instance equality-of-logior-expressions-inside-rm-low-32-4
                             (value value)
                             (a (xr :mem addr-2 x86-1))
                             (w (xr :mem addr-2 x86-2))
                             (b (xr :mem (+ 1 addr-2) x86-1))
                             (x (xr :mem (+ 1 addr-2) x86-2))
                             (c (xr :mem (+ 2 addr-2) x86-1))
                             (y (xr :mem (+ 2 addr-2) x86-2))
                             (d (xr :mem (+ 3 addr-2) x86-1))
                             (z (xr :mem (+ 3 addr-2) x86-2))))
            :in-theory (e/d* (rm-low-32-open-only-if-x86)
                             (|(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|
                              force (force))))
           ("Subgoal 2"
            :use ((:instance xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-2-helper-1
                             (x (xr :mem addr-2 x86-1))
                             (y (xr :mem addr-2 x86-2))
                             (a (rm-low-32 addr-2 x86-1))
                             (b (rm-low-32 addr-2 x86-2))))
            :in-theory (e/d* ()
                             (|(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|
                              force (force))))
           ("Subgoal 3"
            :use ((:instance equality-of-logior-expressions-inside-rm-low-32-3
                             (value value)
                             (a (xr :mem addr-2 x86-1))
                             (w (xr :mem addr-2 x86-2))
                             (b (xr :mem (+ 1 addr-2) x86-1))
                             (x (xr :mem (+ 1 addr-2) x86-2))
                             (c (xr :mem (+ 2 addr-2) x86-1))
                             (y (xr :mem (+ 2 addr-2) x86-2))
                             (d (xr :mem (+ 3 addr-2) x86-1))
                             (z (xr :mem (+ 3 addr-2) x86-2))))
            :in-theory (e/d* (rm-low-32-open-only-if-x86)
                             (|(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|
                              force (force))))
           ("Subgoal 4"
            :use ((:instance xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-2-helper-1
                             (x (xr :mem addr-2 x86-1))
                             (y (xr :mem addr-2 x86-2))
                             (a (rm-low-32 addr-2 x86-1))
                             (b (rm-low-32 addr-2 x86-2))))
            :in-theory (e/d* ()
                             (|(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|
                              force (force))))
           ("Subgoal 5"
            :use ((:instance equality-of-logior-expressions-inside-rm-low-32-2
                             (a (xr :mem addr-2 x86-1))
                             (w (xr :mem addr-2 x86-2))
                             (b (xr :mem (+ 1 addr-2) x86-1))
                             (x (xr :mem (+ 1 addr-2) x86-2))
                             (c (xr :mem (+ 2 addr-2) x86-1))
                             (y (xr :mem (+ 2 addr-2) x86-2))
                             (d (xr :mem (+ 3 addr-2) x86-1))
                             (z (xr :mem (+ 3 addr-2) x86-2))))
            :in-theory (e/d* (rm-low-32-open-only-if-x86)
                             (|(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|
                              force (force))))
           ("Subgoal 6"
            :use ((:instance xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-2-helper-1
                             (x (xr :mem addr-2 x86-1))
                             (y (xr :mem addr-2 x86-2))
                             (a (rm-low-32 addr-2 x86-1))
                             (b (rm-low-32 addr-2 x86-2))))
            :in-theory (e/d* ()
                             (|(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|
                              force (force))))
           ("Subgoal 7"
            :use ((:instance equality-of-logior-expressions-inside-rm-low-32-1
                             (a (xr :mem addr-1 x86-1))
                             (w (xr :mem addr-1 x86-2))
                             (b (xr :mem (+ 1 addr-1) x86-1))
                             (x (xr :mem (+ 1 addr-1) x86-2))
                             (c (xr :mem (+ 2 addr-1) x86-1))
                             (y (xr :mem (+ 2 addr-1) x86-2))
                             (d (xr :mem (+ 3 addr-1) x86-1))
                             (z (xr :mem (+ 3 addr-1) x86-2))))
            :in-theory (e/d* (rm-low-32-open-only-if-x86)
                             (|(rm-low-64 addr2 (xw :mem addr1 val x86)) --- member addr|
                              force (force)))))))

(defthmd xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-3-helper-1
  (implies (and (physical-address-p addr-2)
                (member-p addr-1 (addr-range 4 (+ 4 addr-2))))
           (equal (member-p addr-1 (addr-range 4 addr-2))
                  nil))
  :hints
  (("Goal" :expand ((addr-range 4 (+ 4 addr-2))
                    (addr-range 3 (+ 5 addr-2)))
    :in-theory (e/d* (disjoint-p member-p) ()))))

(local
 (defthmd xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-3
   (implies (and (xlate-equiv-entries (rm-low-64 addr-2 x86-1)
                                      (rm-low-64 addr-2 x86-2))
                 ;; Case 2: addr-1 = ((+ 4 addr-2) to (+ 8 addr-2)).
                 (member-p addr-1 (addr-range 4 (+ 4 addr-2)))
                 (physical-address-p addr-1)
                 (physical-address-p addr-2)
                 (unsigned-byte-p 8 value)
                 (not (programmer-level-mode x86-1))
                 (not (programmer-level-mode x86-2))
                 (x86p x86-1)
                 (x86p x86-2))
            (xlate-equiv-entries (rm-low-64 addr-2 (xw :mem addr-1 value x86-1))
                                 (rm-low-64 addr-2 (xw :mem addr-1 value x86-2))))
   :hints (("Goal"
            :in-theory (e/d* (disjoint-p
                              member-p
                              xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-3-helper-1
                              |(rm-low-32 addr2 (xw :mem addr1 val x86)) --- member addr|)
                             (force (force)))))))

(defthmd xlate-equiv-entries-of-rm-low-64-and-xw-mem-helper
  (implies (and (member-p addr-1 (addr-range 8 addr-2))
                (physical-address-p addr-2)
                (not (member-p addr-1 (addr-range 4 (+ 4 addr-2)))))
           (member-p addr-1 (addr-range 4 addr-2)))
  :hints (("Goal"
           :expand ((addr-range 4 addr-2)
                    (addr-range 8 addr-2)
                    (addr-range 7 (+ 1 addr-2))
                    (addr-range 4 (+ 4 addr-2))
                    (addr-range 3 (+ 1 addr-2)))
           :in-theory (e/d* (member-p) ()))))

(defthmd xlate-equiv-entries-of-rm-low-64-and-xw-mem
  (implies (and (xlate-equiv-entries (rm-low-64 superior-structure-paddr x86-1)
                                     (rm-low-64 superior-structure-paddr x86-2))
                (physical-address-p index)
                (physical-address-p superior-structure-paddr)
                (unsigned-byte-p 8 value)
                (not (programmer-level-mode x86-1))
                (not (programmer-level-mode x86-2))
                (x86p x86-1)
                (x86p x86-2))
           (xlate-equiv-entries
            (rm-low-64 superior-structure-paddr (xw :mem index value x86-1))
            (rm-low-64 superior-structure-paddr (xw :mem index value x86-2))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-1
                            (addr-1 index)
                            (addr-2 superior-structure-paddr))
                 (:instance xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-2
                            (addr-1 index)
                            (addr-2 superior-structure-paddr))
                 (:instance xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-3
                            (addr-1 index)
                            (addr-2 superior-structure-paddr)))
           :in-theory (e/d* (xlate-equiv-entries-of-rm-low-64-and-xw-mem-helper)
                            (rewrite-equality-of-two-rm-low-32s-to-that-of-memis
                             rewrite-xlate-equiv-of-two-rm-low-64s
                             rm-low-64-open-only-if-x86
                             xlate-equiv-of-logior-expressions-for-rm-low-64
                             xlate-equiv-of-logior-expressions-for-rm-low-64-gl
                             xlate-equiv-entries-of-rm-low-64-and-xw-mem-case-1))
           :cases ((member-p index (addr-range 4 superior-structure-paddr))
                   (member-p index (addr-range 4 (+ 4 superior-structure-paddr)))
                   (not (member-p index (addr-range 8 superior-structure-paddr)))))))

(in-theory (e/d () (rewrite-equality-of-two-rm-low-32s-to-that-of-memis
                    rewrite-xlate-equiv-of-two-rm-low-64s
                    rm-low-64-open-only-if-x86
                    xlate-equiv-of-logior-expressions-for-rm-low-64
                    xlate-equiv-of-logior-expressions-for-rm-low-64-gl)))

(defthm gather-qword-addresses-corresponding-to-1-entry-and-xw-mem
  (implies (and
            ;; TO-DO: Dumb bind-free and syntaxp below...
            (bind-free '((x86-2 . x86-2)))
            (syntaxp (equal x86-1 'x86-1))
            (xlate-equiv-entries (rm-low-64 addr x86-1)
                                 (rm-low-64 addr x86-2))
            (system-level-state-p x86-1)
            (system-level-state-p x86-2)
            (physical-address-p addr)
            (physical-address-p index)
            (unsigned-byte-p 8 value))
           (equal (gather-qword-addresses-corresponding-to-1-entry addr (xw :mem index value x86-1))
                  (gather-qword-addresses-corresponding-to-1-entry addr (xw :mem index value x86-2))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-of-rm-low-64-and-xw-mem
                            (superior-structure-paddr addr)
                            (index index))
                 (:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 addr (xw :mem index value x86-1)))
                            (e-2 (rm-low-64 addr (xw :mem index value x86-2)))
                            (n 12))
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 addr (xw :mem index value x86-1)))
                            (e-2 (rm-low-64 addr (xw :mem index value x86-2)))))
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             member-p)
                            ()))))

(defthm gather-qword-addresses-corresponding-to-entries-aux-and-xw-mem
  (implies (and
            ;; TO-DO
            (bind-free '((x86-2 . x86-2)))
            (syntaxp (equal x86-1 'x86-1))
            (xlate-equiv-entries-at-qword-addresses addrs addrs x86-1 x86-2)
            (system-level-state-p x86-1)
            (system-level-state-p x86-2)
            (mult-8-qword-paddr-listp addrs)
            (physical-address-p index)
            (unsigned-byte-p 8 value))
           (equal (gather-qword-addresses-corresponding-to-entries-aux
                   addrs (xw :mem index value x86-1))
                  (gather-qword-addresses-corresponding-to-entries-aux
                   addrs (xw :mem index value x86-2))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses
                                    gather-qword-addresses-corresponding-to-entries-aux)
                                   ()))))

(defthm gather-qword-addresses-corresponding-to-entries-and-xw-mem
  (implies (and
            ;; TO-DO
            (bind-free '((x86-2 . x86-2)))
            (syntaxp (equal x86-1 'x86-1))
            (xlate-equiv-entries-at-qword-addresses addrs addrs x86-1 x86-2)
            (system-level-state-p x86-1)
            (system-level-state-p x86-2)
            (mult-8-qword-paddr-listp addrs)
            (physical-address-p index)
            (unsigned-byte-p 8 value))
           (equal (gather-qword-addresses-corresponding-to-entries
                   addrs (xw :mem index value x86-1))
                  (gather-qword-addresses-corresponding-to-entries
                   addrs (xw :mem index value x86-2))))
  :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries) ()))))

(defthm xlate-equiv-entries-at-qword-addresses-xw-mem
  (implies (and
            (xlate-equiv-entries-at-qword-addresses
             addrs addrs x86-1 x86-2)
            (mult-8-qword-paddr-listp addrs)
            (system-level-state-p x86-1)
            (system-level-state-p x86-2)
            (physical-address-p index)
            (unsigned-byte-p 8 value))
           (xlate-equiv-entries-at-qword-addresses
            addrs addrs
            (xw :mem index value x86-1)
            (xw :mem index value x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses
                                    xlate-equiv-structures
                                    xlate-equiv-x86s)
                                   ()))
          ("Subgoal *1/2"
           :use ((:instance xlate-equiv-entries-of-rm-low-64-and-xw-mem
                            (superior-structure-paddr (car addrs)))))))

(i-am-here)

(defun find-xlate-equiv-entries-at-qword-addresses-from-occurrence
  (mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((call (acl2::find-call-lst
              'xlate-equiv-entries-at-qword-addresses
              (acl2::mfc-clause mfc)))
       ((when (not call))
        ;; xlate-equiv-entries-at-qword-addresses term not encountered.
        nil)
       (addresses (second call)))
    `((addresses . ,addresses))))

(defthmd xlate-equiv-entries-at-qword-addresses-and-subset-p
  (implies (and (bind-free (find-xlate-equiv-entries-at-qword-addresses-from-occurrence
                            mfc state)
                           (addresses))
                (xlate-equiv-entries-at-qword-addresses
                 addresses addresses x86-1 x86-2)
                (subset-p addrs addresses))
           (xlate-equiv-entries-at-qword-addresses
            addrs addrs x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses
                                    subset-p)
                                   ()))))

(defthm xlate-equiv-structures-and-gather-pml4-table-qword-addresses
  (implies (and
            ;; TO-DO
            (bind-free '((x86-2 . x86-2)))
            (syntaxp (equal x86-1 'x86-1))
            (xlate-equiv-structures x86-1 x86-2)
            (system-level-state-p x86-1))
           (equal (gather-pml4-table-qword-addresses x86-1)
                  (gather-pml4-table-qword-addresses x86-2)))
  :hints (("Goal" :in-theory (e/d* (gather-pml4-table-qword-addresses
                                    xlate-equiv-structures)
                                   ()))))

(defthm subset-p-and-remove-duplicates-equal
  (equal (subset-p xs (remove-duplicates-equal ys))
         (subset-p xs ys))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(defthm member-p-subset-p-and-remove-duplicates-equal
  (implies (and (member-p e xs)
                (subset-p xs ys))
           (member-p e (remove-duplicates-equal ys)))
  :hints (("Goal" :in-theory (e/d* (subset-p member-p) ()))))

(acl2::why  XLATE-EQUIV-ENTRIES-AT-QWORD-ADDRESSES-XW-MEM)

;; (defthmd xlate-equiv-entries-of-rm-low-64-and-xw-mem
;;   (implies (and (xlate-equiv-entries (rm-low-64 superior-structure-paddr x86-1)
;;                                      (rm-low-64 superior-structure-paddr x86-2))
;;                 (physical-address-p index)
;;                 (physical-address-p superior-structure-paddr)
;;                 (unsigned-byte-p 8 value)
;;                 (not (programmer-level-mode x86-1))
;;                 (not (programmer-level-mode x86-2))
;;                 (x86p x86-1)
;;                 (x86p x86-2))
;;            (xlate-equiv-entries
;;             (rm-low-64 superior-structure-paddr (xw :mem index value x86-1))
;;             (rm-low-64 superior-structure-paddr (xw :mem index value x86-2))))))

(defthm xlate-equiv-entries-at-qword-addresses-xw-mem-with-gather-qword-addresses-corresponding-to-1-entry
  (implies (and
            (xlate-equiv-entries-at-qword-addresses
             (gather-qword-addresses-corresponding-to-1-entry addr x86-1)
             (gather-qword-addresses-corresponding-to-1-entry addr x86-2)
             x86-1 x86-2)
            (all-mem-except-paging-structures-equal x86-1 x86-2)
            (xlate-equiv-x86s x86-1 x86-2)
            (xlate-equiv-entries (rm-low-64 addr x86-1)
                                 (rm-low-64 addr x86-2))
            (member-p index (addr-range 8 addr))
            (physical-address-p addr)
            (system-level-state-p x86-1)
            (system-level-state-p x86-2)
            (physical-address-p index)
            (unsigned-byte-p 8 value))
           (xlate-equiv-entries-at-qword-addresses
            (gather-qword-addresses-corresponding-to-1-entry addr (xw :mem index value x86-1))
            (gather-qword-addresses-corresponding-to-1-entry addr (xw :mem index value x86-2))
            (xw :mem index value x86-1)
            (xw :mem index value x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-of-rm-low-64-and-xw-mem
                            (superior-structure-paddr addr))
                 (:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 addr (xw :mem index value x86-1)))
                            (e-2 (rm-low-64 addr (xw :mem index value x86-2)))
                            (n 12)))
           :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses
                             gather-qword-addresses-corresponding-to-1-entry
                             xlate-equiv-x86s)
                            (unsigned-byte-p
                             gather-qword-addresses-corresponding-to-1-entry-with-different-x86-entries
                             signed-byte-p)))))



(defthm xlate-equiv-entries-at-qword-addresses-xw-mem-with-gather-qword-addresses-corresponding-to-entries-aux
  (implies (and
            (xlate-equiv-entries-at-qword-addresses
             (gather-qword-addresses-corresponding-to-entries-aux addrs x86-1)
             (gather-qword-addresses-corresponding-to-entries-aux addrs x86-2)
             x86-1 x86-2)
            (mult-8-qword-paddr-listp addrs)
            (system-level-state-p x86-1)
            (system-level-state-p x86-2)
            (physical-address-p index)
            (unsigned-byte-p 8 value))
           (xlate-equiv-entries-at-qword-addresses
            (gather-qword-addresses-corresponding-to-entries-aux addrs (xw :mem index value x86-1))
            (gather-qword-addresses-corresponding-to-entries-aux addrs (xw :mem index value x86-2))
            (xw :mem index value x86-1)
            (xw :mem index value x86-2)))
  :hints (("Goal"
           :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses
                             gather-qword-addresses-corresponding-to-entries-aux
                             xlate-equiv-structures
                             xlate-equiv-x86s)
                            (unsigned-byte-p
                             signed-byte-p)))))

;; (DEFTHM GATHER-QWORD-ADDRESSES-CORRESPONDING-TO-ENTRIES-AND-XW-MEM
;;   (IMPLIES (AND (BIND-FREE '((X86-2 . X86-2)))
;;                 (SYNTAXP (EQUAL X86-1 '`X86-1))
;;                 (XLATE-EQUIV-ENTRIES-AT-QWORD-ADDRESSES
;;                  ADDRS ADDRS X86-1 X86-2)
;;                 (SYSTEM-LEVEL-STATE-P X86-1)
;;                 (SYSTEM-LEVEL-STATE-P X86-2)
;;                 (MULT-8-QWORD-PADDR-LISTP ADDRS)
;;                 (PHYSICAL-ADDRESS-P INDEX)
;;                 (UNSIGNED-BYTE-P 8 VALUE))
;;            (EQUAL (GATHER-QWORD-ADDRESSES-CORRESPONDING-TO-ENTRIES
;;                    ADDRS (XW :MEM INDEX VALUE X86-1))
;;                   (GATHER-QWORD-ADDRESSES-CORRESPONDING-TO-ENTRIES
;;                    ADDRS (XW :MEM INDEX VALUE X86-2)))))
;; (defthmd xlate-equiv-entries-at-qword-addresses-and-subset-p
;;   (implies (and (bind-free (find-xlate-equiv-entries-at-qword-addresses-from-occurrence
;;                             mfc state)
;;                            (addresses))
;;                 (xlate-equiv-entries-at-qword-addresses
;;                  addresses addresses x86-1 x86-2)
;;                 (subset-p addrs addresses))
;;            (xlate-equiv-entries-at-qword-addresses
;;             addrs addrs x86-1 x86-2)))

(acl2::why gather-qword-addresses-corresponding-to-entries-and-xw-mem)
(acl2::why xlate-equiv-entries-of-rm-low-64-and-xw-mem)

(DEFTHM XLATE-EQUIV-ENTRIES-OF-RM-LOW-64-AND-XW-MEM
  (IMPLIES
   (AND (XLATE-EQUIV-ENTRIES
         (RM-LOW-64 SUPERIOR-STRUCTURE-PADDR X86-1)
         (RM-LOW-64 SUPERIOR-STRUCTURE-PADDR X86-2))
        (PHYSICAL-ADDRESS-P INDEX)
        (PHYSICAL-ADDRESS-P SUPERIOR-STRUCTURE-PADDR)
        (UNSIGNED-BYTE-P 8 VALUE)
        (NOT (PROGRAMMER-LEVEL-MODE X86-1))
        (NOT (PROGRAMMER-LEVEL-MODE X86-2))
        (X86P X86-1)
        (X86P X86-2))
   (XLATE-EQUIV-ENTRIES
    (RM-LOW-64 SUPERIOR-STRUCTURE-PADDR
               (XW :MEM INDEX VALUE X86-1))
    (RM-LOW-64 SUPERIOR-STRUCTURE-PADDR
               (XW :MEM INDEX VALUE X86-2)))))

(defthm gather-all-paging-structure-qword-addresses-xw-mem-with-xlate-equiv-structures
  (implies (and
            ;; TO-DO
            (bind-free '((x86-2 . x86-2)))
            (syntaxp (equal x86-1 'x86-1))
            (xlate-equiv-structures x86-1 x86-2)
            (system-level-state-p x86-1)
            (system-level-state-p x86-2)
            (physical-address-p index)
            (unsigned-byte-p 8 value))
           (equal
            (gather-all-paging-structure-qword-addresses (xw :mem index value x86-1))
            (gather-all-paging-structure-qword-addresses (xw :mem index value x86-2))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses-and-subset-p
                            (addresses (gather-all-paging-structure-qword-addresses x86-2))
                            (addrs (gather-pml4-table-qword-addresses x86-2))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses
                             xlate-equiv-entries-of-rm-low-64-and-xw-mem
                             xlate-equiv-structures
                             subset-p)
                            (unsigned-byte-p
                             system-level-state-p
                             signed-byte-p)))))

(defthm gather-all-paging-structure-qword-addresses-xw-mem-with-xlate-equiv-x86s
  (implies (and
            ;; TO-DO
            (bind-free '((x86-2 . x86-2)))
            (syntaxp (equal x86-1 'x86-1))
            (xlate-equiv-x86s x86-1 x86-2)
            (system-level-state-p x86-1)
            (system-level-state-p x86-2)
            (physical-address-p index)
            (unsigned-byte-p 8 value))
           (equal
            (gather-all-paging-structure-qword-addresses (xw :mem index value x86-1))
            (gather-all-paging-structure-qword-addresses (xw :mem index value x86-2))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses-and-subset-p
                            (addresses (gather-all-paging-structure-qword-addresses x86-2))
                            (addrs (gather-pml4-table-qword-addresses x86-2))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses
                             xlate-equiv-entries-at-qword-addresses-and-subset-p
                             xlate-equiv-structures
                             xlate-equiv-x86s
                             subset-p)
                            (unsigned-byte-p
                             system-level-state-p
                             signed-byte-p)))))

(defthm all-mem-except-paging-structures-equal-and-xw-mem
  (implies (and (all-mem-except-paging-structures-equal x y)
                (system-level-state-p y)
                (physical-address-p index)
                (x86p (xw :mem index value x))
                (x86p (xw :mem index value y)))
           (all-mem-except-paging-structures-equal
            (xw :mem index value x)
            (xw :mem index value y)))
  :hints (("Goal" :in-theory (e/d* (all-mem-except-paging-structures-equal)
                                   ())))
  :otf-flg t)

(defthm xlate-equiv-x86s-and-xw-mem
  (implies (and
            (xlate-equiv-x86s x86-1 x86-2)
            (system-level-state-p x86-1)
            (system-level-state-p x86-2)
            (physical-address-p index)
            (unsigned-byte-p 8 value))
           (xlate-equiv-x86s
            (xw :mem index value x86-1)
            (xw :mem index value x86-2)))
  :hints (("Goal"
           :in-theory (e/d* (xlate-equiv-x86s
                             xlate-equiv-structures
                             system-level-state-p)
                            (all-mem-except-paging-structures-equal))))
  :otf-flg t)
