;; Cuong Chau <cuong.chau@arm.com>

;; May 2021

;; Prove correctness for special inputs

(in-package "RTL")

(include-book "prelim")

(local (arith-5-for-rtl))

(local
 (in-theory (disable bits-tail-gen
                     neg-bitn-0
                     neg-bitn-1
                     acl2::not-integerp-1b
                     acl2::not-integerp-2b
                     acl2::not-integerp-3b
                     acl2::not-integerp-4b)))

;; ======================================================================

(defundd specialp ()
  (or (member (classa) '(0 1 2 3))
      (member (classb) '(0 1 2 3))))

(defundd fmtw () (+ 1 (expw (f)) (sigw (f))))

(defundd opaw () (bits (opa) (1- (fmtw)) 0))

(defundd opbw () (bits (opb) (1- (fmtw)) 0))

(defundd opaz ()
  (if (and (= (fzp) 1)
           (denormp (opaw) (f)))
      (zencode (sgnf (opaw) (f)) (f))
     (opaw)))

(defundd opbz ()
  (if (and (= (fzp) 1)
           (denormp (opbw) (f)))
      (zencode (sgnf (opbw) (f)) (f))
    (opbw)))

(local
 (def-gl-rule aux-1
   :hyp (and (bvecp x 64)
             (member n '(9 22 51))
             (equal m (expt 2 n)))
   :concl (equal (logand m (bits x n 0))
                 (if (equal (bitn x n) 0)
                     0
                   m))
   :disabledp t
   :g-bindings (gl::auto-bindings
                (:nat x 64)
                (:nat n 6))))

(defthmd a-class
  (and (equal (equal (classa) 0)
              (zerp (opaz) (f)))
       (equal (equal (classa) 1)
              (infp (opaz) (f)))
       (equal (equal (classa) 2)
              (snanp (opaz) (f)))
       (equal (equal (classa) 3)
              (qnanp (opaz) (f)))
       (equal (equal (classa) 4)
              (normp (opaz) (f)))
       (equal (equal (classa) 5)
              (denormp (opaz) (f))))
  :hints (("Goal" :in-theory (e/d (aux-1
                                   opaz
                                   f
                                   classa
                                   zerp
                                   infp
                                   snanp
                                   qnanp
                                   nanp
                                   normp
                                   denormp
                                   opaw
                                   fmtw
                                   analyze
                                   expf
                                   manf
                                   si
                                   bitn-bits
                                   zencode
                                   encodingp
                                   unsupp)
                                  (acl2::default-plus-1
                                   acl2::default-plus-2)))))

(defthmd b-class
  (and (equal (equal (classb) 0)
              (zerp (opbz) (f)))
       (equal (equal (classb) 1)
              (infp (opbz) (f)))
       (equal (equal (classb) 2)
              (snanp (opbz) (f)))
       (equal (equal (classb) 3)
              (qnanp (opbz) (f)))
       (equal (equal (classb) 4)
              (normp (opbz) (f)))
       (equal (equal (classb) 5)
              (denormp (opbz) (f))))
  :hints (("Goal" :in-theory (e/d (aux-1
                                   opbz
                                   f
                                   classb
                                   zerp
                                   infp
                                   snanp
                                   qnanp
                                   nanp
                                   normp
                                   denormp
                                   opbw
                                   fmtw
                                   analyze
                                   expf
                                   manf
                                   si
                                   bitn-bits
                                   zencode
                                   encodingp
                                   unsupp)
                                  (acl2::default-plus-1
                                   acl2::default-plus-2)))))

(defthmd flags-a-rewrite
  (equal (flags-a)
         (if (and (denormp (opaw) (f))
                  (equal (fzp) 1)
                  (not (equal (fnum) 1)))
             (expt 2 7)
           0))
  :hints (("Goal" :in-theory (enable flags-a
                                     f
                                     opaw
                                     fmtw
                                     denormp
                                     expf
                                     manf
                                     analyze
                                     si
                                     encodingp))))

(defthmd flags-b-rewrite
  (equal (flags-b)
         (if (and (or (denormp (opaw) (f))
                      (denormp (opbw) (f)))
                  (equal (fzp) 1)
                  (not (equal (fnum) 1)))
             (expt 2 7)
           0))
  :hints (("Goal" :in-theory (enable fdivlane-segment-result-expand
                                     flags-b-segment
                                     flags-a-rewrite
                                     f
                                     opbw
                                     fmtw
                                     denormp
                                     expf
                                     manf
                                     analyze
                                     si
                                     encodingp))))

(defthmd sign-rewrite
  (equal (sign)
         (logxor (sgnf (opaw) (f))
                 (sgnf (opbw) (f))))
  :hints (("Goal" :in-theory (e/d (sign
                                   sgnf
                                   opaw
                                   opbw
                                   fmtw
                                   f
                                   signa
                                   signb
                                   bitn-bits
                                   analyze)
                                  (acl2::default-logxor-1
                                   acl2::default-logxor-2)))))

(local
 (def-gl-rule aux-2-hp
   :hyp (and (bvecp x 64)
             (qnanp (bits x 15 0) (hp)))
   :concl (equal (logior *2^9* (bits x 15 0))
                 (bits x 15 0))
   :g-bindings (gl::auto-bindings
                (:nat x 64))))

(local
 (def-gl-rule aux-2-sp
   :hyp (and (bvecp x 64)
             (qnanp (bits x 31 0) (sp)))
   :concl (equal (logior *2^22* (bits x 31 0))
                 (bits x 31 0))
   :g-bindings (gl::auto-bindings
                (:nat x 64))))

(local
 (def-gl-rule aux-2-dp
   :hyp (and (bvecp x 64)
             (qnanp x (dp)))
   :concl (equal (logior *2^51* x)
                 x)
   :g-bindings (gl::auto-bindings
                (:nat x 64))))

(local
 (defthm aux-3
   (implies (bitp b)
            (and (equal (bits (* *2^15* b) 15 0)
                        (* *2^15* b))
                 (zerp (* *2^15* b) (hp))
                 (equal (sgnf (* *2^15* b) (hp))
                        b)
                 (equal (decode (* *2^15* b) (hp))
                        0)

                 (equal (bits (* *2^31* b) 31 0)
                        (* *2^31* b))
                 (zerp (* *2^31* b) (sp))
                 (equal (sgnf (* *2^31* b) (sp))
                        b)
                 (equal (decode (* *2^31* b) (sp))
                        0)

                 (equal (bits (* *2^63* b) 63 0)
                        (* *2^63* b))
                 (zerp (* *2^63* b) (dp))
                 (equal (sgnf (* *2^63* b) (dp))
                        b)
                 (equal (decode (* *2^63* b) (dp))
                        0)))
   :hints (("Goal" :in-theory (enable hp sp dp sgnf)))))

(defthmd fdivlane-special-correct
  (mv-let
    (data-spec r-spec)
    (arm-binary-spec 'div (opaw) (opbw) (rin) (f))
    (implies (specialp)
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec))))
  :hints (("Goal"
           :in-theory (enable f
                              specialp
                              data
                              flags
                              a-class b-class
                              zerp-is-unique-format
                              fzp dnp
                              opaz opbz
                              opaw opbw
                              fmtw
                              flags-b-rewrite
                              set-flag
                              qnanize
                              sign-rewrite
                              cat-for-gl
                              binary-undefined-p
                              binary-zero-sgn
                              binary-inf-sgn
                              binary-eval
                              zencode
                              zerp-decode-rel-hp
                              zerp-decode-rel-sp
                              zerp-decode-rel-dp
                              bitn-logior
                              bitn-bitp
                              result
                              specialcase))))
