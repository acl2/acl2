#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "ihs/ihs-lemmas" :dir :system)
(include-book "arithmetic")

;;;make lognot "invisible" when ordering terms using commutativity of the logops
(add-invisible-fns binary-logand lognot)
(add-invisible-fns binary-logior lognot)
(add-invisible-fns binary-logxor lognot)

;;;same with b-not and the binary operators
(add-invisible-fns b-and b-not)
(add-invisible-fns b-ior b-not)


(in-theory (disable 
            B-NOT
            B-AND
            B-IOR
            B-XOR
            B-EQV
            B-NAND
            B-NOR
            B-ANDC1
            B-ANDC2
            B-ORC1
            B-ORC2))

(defthm associativity-of-b-and
  (equal (b-and (b-and a b) c)
         (b-and a (b-and b c)))
  :hints (("Goal" :in-theory (enable b-and))))

(defthm associativity-of-b-ior
  (equal (b-ior (b-ior a b) c)
         (b-ior a (b-ior b c)))
  :hints (("Goal" :in-theory (enable b-ior))))

(local (in-theory (enable b-xor b-eqv b-nand b-nor 
                          b-andc1 b-andc2 b-orc1 b-orc2 b-not)))


(defthm simplify-bit-functions-2
  (and (equal (b-and a (b-and (b-not a) b)) 0)
       (equal (b-ior a (b-ior (b-not a) b)) 1)
       (equal (b-and a (b-and a b)) (b-and a b))
       (equal (b-ior a (b-ior a b)) (b-ior a b)))
  :hints (("goal" :in-theory (enable b-and b-ior b-not))))
;           :in-theory (disable associativity-of-bit-functions)

(defthm b-and-b-ior
  (and (equal (b-and i (b-ior j k))
              (b-ior (b-and i j) (b-and i k)))
       (equal (b-and (b-ior i j) k)
              (b-ior (b-and i k) (b-and j k))))
  :hints (("goal" :in-theory (enable b-and b-ior))))

(defthm b-xor-b-not
  (and (equal (b-xor a (b-not b)) (b-not (b-xor a b)))
       (equal (b-xor (b-not a) b) (b-not (b-xor a b))))
  :hints (("goal" :in-theory (enable b-not b-xor))))

(defthm b-xor-constant
  (implies (and (equal y 0)
                (syntaxp (quotep y))    
                (not (equal x y))
                (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 z))
           (equal (b-xor x z) (b-not z)))
  :hints (("goal" :in-theory (enable unsigned-byte-p b-xor b-not))))

;drop?
(defthmd b-not-open-0
  (implies (and (equal x 0)
                (unsigned-byte-p 1 x))
           (equal (b-not x)
                  1))
  :hints (("goal" :in-theory (enable b-not unsigned-byte-p))))

(defthm b-not-open-1
  (implies (and (not (equal x 0))
                (unsigned-byte-p 1 x))
           (equal (b-not x)
                  0))
  :hints (("goal" :in-theory (enable b-not unsigned-byte-p))))

(defthm bfix-b-functions
  (and (equal (bfix (b-not x))   (b-not x))
       (equal (bfix (b-and x y)) (b-and x y))
       (equal (bfix (b-ior x y)) (b-ior x y))
       (equal (bfix (b-xor x y)) (b-xor x y)))
  :hints (("goal" :in-theory (enable b-ior b-and b-xor b-not))))

(defthm commutativity2-of-b-functions
  (and (equal (b-ior a (b-ior b c))
              (b-ior b (b-ior a c)))
       (equal (b-xor a (b-xor b c))
              (b-xor b (b-xor a c)))
       (equal (b-and a (b-and b c))
              (b-and b (b-and a c))))
  :hints (("goal" :in-theory (enable b-ior b-and b-xor b-not))))

(defthm equal-k-b-and
  (and (equal (equal 0 (b-and x y))
              (or (zbp x) (zbp y)))
       (equal (equal 1 (b-and x y))
              (and (not (zbp x)) (not (zbp y)))))
  :hints (("goal" :in-theory (enable b-and))))

(defthm equal-k-b-ior
  (and (equal (equal 0 (b-ior x y))
              (and (zbp x) (zbp y)))
       (equal (equal 1 (b-ior x y))
              (not (and (zbp x) (zbp y)))))
  :hints (("goal" :in-theory (enable b-ior))))

;why not just define them this way and leave them enabled?
(defthm b-xor-rewrite
  (equal (b-xor a b)
         (b-ior (b-and a (b-not b))
                (b-and (b-not a) b))))

(defthm b-eqv-rewrite
  (equal (b-eqv a b)
         (b-ior (b-and a b)
                (b-and (b-not a) (b-not b)))))

(defthm b-nor-rewrite
  (equal (b-nor a b)
         (b-not (b-ior a b))))

(defthm b-nand-rewrite
  (equal (b-nand a b)
         (b-not (b-and a b))))

(defthm b-andc1-rewrite
  (equal (b-andc1 a b)
         (b-and (b-not a) b)))

(defthm b-andc2-rewrite
  (equal (b-andc2 a b)
         (b-and a (b-not b))))

(defthm b-orc1-rewrite
  (equal (b-orc1 a b)
         (b-ior (b-not a) b)))

(defthm b-orc2-rewrite
  (equal (b-orc2 a b)
         (b-ior a (b-not b))))


;bzo more like this?
;separate rw from fc rules?
;generalize the size in the rw version?
(defthm unsigned-byte-p-b-xor
  (unsigned-byte-p 1 (b-xor x y))
  :hints (("goal" :in-theory (enable b-xor)))
  :rule-classes ((:forward-chaining :trigger-terms ((b-xor x y)))
                 (:rewrite)))

(defthm unsigned-byte-p-b-and
  (unsigned-byte-p 1 (b-and x y))
  :hints (("goal" :in-theory (enable b-and)))
  :rule-classes ((:forward-chaining :trigger-terms ((b-and x y)))
                 (:rewrite)))

(defthm unsigned-byte-p-b-ior
  (unsigned-byte-p 1 (b-ior x y))
  :hints (("goal" :in-theory (enable b-ior)))
  :rule-classes ((:forward-chaining :trigger-terms ((b-ior x y)))
                 (:rewrite)))

(defthm unsigned-byte-p-b-functions
  (and (equal (unsigned-byte-p n (b-and x y))
              (and (integerp n)
                   (<= 0 n)
                   (or (< 0 n)
                       (equal (b-and x y) 0) ;improve
                       )))
       (equal (unsigned-byte-p n (b-ior x y))
              (and (integerp n)
                   (<= 0 n)
                   (or (< 0 n)
                       (equal (b-ior x y) 0) ;improve
                       ))))
  :hints (("goal" :in-theory (enable b-ior b-and unsigned-byte-p))))

(defthmd b-xor-equal-0-rewrite
  (equal (equal (b-xor x y) 0)
         (equal (zbp x) (zbp y)))
  :hints (("goal" :in-theory (enable b-xor b-not))))

(defthmd b-xor-equal-1-rewrite
  (equal (equal (b-xor x y) 1)
         (not (equal (zbp x) (zbp y))))
  :hints (("goal" :in-theory (enable b-xor b-not))))

(defthm b-ior-upper-bound
  (<= (b-ior x y) 1)
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable b-ior))))

(defthm unsigned-byte-p-b-not
  (implies (and (integerp size)
                (< 0 size))
           (unsigned-byte-p size (b-not x)))
  :hints (("Goal" :in-theory (enable b-not))))

(defthm logext-16-of-b-not
  (implies (and (integerp n)
                (< 1 n))
           (equal (logext n (b-not bit))
                  (b-not bit)))
  :hints (("Goal" :in-theory (enable b-not))))

(defthm loghead-of-b-not
  (implies (and (integerp n)
                (< 0 n))
           (equal (loghead n (b-not bit))
                  (b-not bit)))
  :hints (("Goal" :in-theory (enable b-not))))

(defthm logtail-of-b-not
  (implies (and (integerp n)
                (< 0 n))
           (equal (logtail n (b-not bit))
                  0))
  :hints (("Goal" :in-theory (enable b-not))))
