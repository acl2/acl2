
(in-package "GL")

(include-book "def-gl-rewrite")
(include-book "symbolic-arithmetic-fns")
(local (include-book "centaur/bitops/congruences" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(def-gl-rewrite integerp-of-logapp
  (integerp (logapp a b c)))

(defun plus-of-logapp-ind (n a c carry)
  (if (zp n)
      (list a c carry)
    (plus-of-logapp-ind (1- n) (logcdr a) (logcdr c)
                        (b-ior (b-and carry (logcar a))
                               (b-and carry (logcar c))))))

(local
 (defthmd plus-of-logapp-lemma
   (implies (and (bitp carry) (integerp c))
            (equal (+ (logapp n a b) c carry)
                   (+ (+ carry
                         (loghead n a)
                         (loghead n c))
                      (ash (+ (ifix b) (logtail n c)) (nfix n)))))
   :hints(("Goal" :in-theory (enable* acl2::ihsext-recursive-redefs)
           :induct (plus-of-logapp-ind n a c carry))
          (and stable-under-simplificationp
               '(:in-theory (enable acl2::equal-logcons-strong
                                    b-xor b-and b-ior))))))

(def-gl-rewrite plus-of-logapp-1
  (implies (integerp c)
           (equal (+ (logapp n a b) c)
                  (+ (+ (loghead n a)
                        (loghead n c))
                     (ash (+ (ifix b) (logtail n c)) (nfix n)))))
  :hints (("goal" :use ((:instance plus-of-logapp-lemma
                         (carry 0)))
           :in-theory (disable plus-of-logapp-lemma))))

(def-gl-rewrite plus-of-logapp-2
  (implies (integerp c)
           (equal (+ c (logapp n a b))
                  (+ (+ (loghead n a)
                        (loghead n c))
                     (ash (+ (ifix b) (logtail n c)) (nfix n)))))
  :hints (("goal" :use ((:instance plus-of-logapp-lemma
                         (carry 0)))
           :in-theory (disable plus-of-logapp-lemma))))

(def-gl-rewrite loghead-of-logapp
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logapp m a b))
                  (loghead n a)))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(def-gl-rewrite logbitp-of-logapp
  (implies (< (nfix n) (nfix m))
           (equal (logbitp n (logapp m a b))
                  (logbitp n a)))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(def-gl-rewrite loghead-of-plus
  (implies (and (integerp a) (integerp b))
           (equal (loghead n (+ a b))
                  (loghead n (+ (loghead n a) (loghead n b)))))
  :hints(("Goal" :use ((:instance acl2::loghead-of-plus-loghead-first
                        (m n))
                       (:instance acl2::loghead-of-plus-loghead-first
                        (m n) (a (loghead n b)) (b a))))))

(def-gl-rewrite logbitp-of-plus
  (implies (and (integerp a) (integerp b))
           (equal (logbitp n (+ a b))
                  (logbitp n (+ (loghead (+ 1 (nfix n)) a)
                                (loghead (+ 1 (nfix n)) b)))))
  :hints (("goal" :in-theory (e/d* (acl2::bitops-congruences)
                                   (acl2::bitops-congruence-incompatible)))))


(def-gl-rewrite logand-of-logapp
  (implies (and (<= 0 mask)
                (<= (integer-length mask) (nfix n)))
           (equal (logand mask (logapp n a b))
                  (logand mask a)))
  :hints (("goal" :in-theory (enable* acl2::ihsext-recursive-redefs
                                     acl2::ihsext-inductions))))

(def-gl-rewrite integerp-of-maybe-integer
  (equal (integerp (maybe-integer i x intp))
         (and intp t))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(def-gl-rewrite <-of-maybe-integer-1
  (implies intp
           (equal (< (maybe-integer i x intp) a)
                  (< (ifix i) a)))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(def-gl-rewrite <-of-maybe-integer-2
  (implies intp
           (equal (< a (maybe-integer i x intp))
                  (< a (ifix i))))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(def-gl-rewrite <-logapp-0
  (equal (< (logapp n i j) 0)
         (< (ifix j) 0))
  :hints(("Goal" :in-theory (e/d* ;; acl2::ihsext-bounds-thms
                             (acl2::ihsext-recursive-redefs
                                     acl2::ihsext-inductions)
                             ((force))))))

(def-gl-rewrite integerp-int-set-sign
  (integerp (int-set-sign negp i)))

(def-gl-rewrite <-int-set-sign-0
  (equal (< (int-set-sign negp i) 0)
         (and negp t)))

(def-gl-rewrite ifix-of-maybe-integer
  (equal (ifix (maybe-integer i x intp))
         (if intp (ifix i) 0))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(def-gl-rewrite nfix-of-maybe-integer
  (equal (nfix (maybe-integer i x intp))
         (if intp (nfix i) 0))
  :hints(("Goal" :in-theory (enable maybe-integer))))

;; (local (defthm logapp-of-non-integer-second
;;          (implies (not (integerp b))
;;                   (equal (logapp n a b)
;;                          (logapp n a 0)))
;;          :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
;;                                             acl2::ihsext-recursive-redefs)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))
         
#||




(trace$ gl::glcp-unify-term/gobj)

(thm (IMPLIES
      (and (GL::INTEGER-WITH-NBITSP 64 ACL2::X0)
           (UNSIGNED-BYTE-P 64 ACL2::X1)
           (UNSIGNED-BYTE-P 64 ACL2::X2))
      (OR (LOGBITP 10 ACL2::X1)
          (EQUAL (UNSIGNED-BYTE-FIX 64
                                    (AAA_AAS-G7 ACL2::X2 (LOGHEAD 64 ACL2::X0)))
                 (LOGIOR 2 (ACL2::LOGSQUASH 32 ACL2::X2)
                         (LOGAND 2261 ACL2::X0)))))
     :hints (("goal" :in-theory nil)
             (gl::try-gl
              ;; :fixes
              ;; (((nfix (st-get :eflags st)) (loghead 64 acl2::x)))
              :subterms-types
              (((nfix (st-get :eflags st))              (gl::integer-with-nbitsp 64 acl2::x))
               ((u64-tr-get n g)                        (unsigned-byte-p 64 acl2::x))
;            ((st-set :pc val st)                     (unknownp acl2::x))
               ((st-get :oracle st)                     (unknownp acl2::x)))
              :type-gens (((unknownp acl2::x) (gl::g-var 0)))
;           :bad-subterms (st)
              )))

||#
