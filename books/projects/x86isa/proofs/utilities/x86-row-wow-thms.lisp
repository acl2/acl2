;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "basics"
              :ttags (:include-raw :undef-flg :syscall-exec :other-non-det))

;; ===================================================================

(defsection x86-RoW-WoW-thms

  :parents (proof-utilities)

  :short "Miscellaneous RoW and WoW theorems"
  :long "<p>See @(see x86-state-field-theorems) for a detailed
  description of RoW and WoW theorems.</p>"

  )

(local (xdoc::set-default-parents x86-RoW-WoW-thms))

;; ======================================================================

(defthm assoc-equal-put-assoc-equal-diff
  (equal (assoc-equal x (put-assoc-equal y z ss))
         (if (equal x y)
             (cons x z)
           (assoc-equal x ss))))

(defthm assoc-equal-consp
  (implies (consp (assoc-equal x ss))
           (consp (assoc-equal x (put-assoc-equal x z ss)))))

(defthm read-x86-file-des-write-x86-file-des-different-indices
  (implies (not (equal fd1 fd2))
           (equal (read-x86-file-des fd1 (write-x86-file-des fd2 fd2-field x86))
                  (read-x86-file-des fd1 x86)))
  :hints (("Goal" :in-theory (e/d (read-x86-file-des
                                   read-x86-file-des-logic
                                   write-x86-file-des
                                   write-x86-file-des-logic)
                                  ()))))

(defthm read-x86-file-des-write-x86-file-des-same-indices
  (equal (read-x86-file-des fd (write-x86-file-des fd fd-field x86))
         (cdr
          (assoc-equal
           fd
           (put-assoc-equal fd fd-field
                            (cdr (assoc-equal :file-descriptors (env-read x86)))))))
  :hints (("Goal" :in-theory (e/d (read-x86-file-des
                                   write-x86-file-des
                                   read-x86-file-des-logic
                                   write-x86-file-des-logic)
                                  ()))))

(defthm read-x86-file-contents-write-x86-file-contents-same-indices
  (equal (read-x86-file-contents name (write-x86-file-contents name name-field x86))
         (cdr
          (assoc-equal
           name
           (put-assoc-equal name name-field
                            (cdr (assoc-equal :file-contents (env-read x86)))))))
  :hints (("Goal" :in-theory (e/d (read-x86-file-contents
                                   write-x86-file-contents
                                   read-x86-file-contents-logic
                                   write-x86-file-contents-logic)
                                  ()))))

(defthm read-x86-file-contents-write-x86-file-contents-different-indices
  (implies (not (equal name1 name2))
           (equal (read-x86-file-contents name1 (write-x86-file-contents name2 name-field x86))
                  (read-x86-file-contents name1 x86)))
  :hints (("Goal" :in-theory (e/d (read-x86-file-contents
                                   write-x86-file-contents
                                   read-x86-file-contents-logic
                                   write-x86-file-contents-logic)
                                  ()))))

;; ======================================================================

;; Some rules about flgi and !flgi:

(local (include-book "centaur/gl/gl" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(include-book "centaur/bitops/equal-by-logbitp" :dir :system)

(encapsulate
 ()

 (local (in-theory (e/d () (unsigned-byte-p))))

 (local
  (encapsulate
   ()

   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm unsigned-byte-p-and-logbitp
     (implies (and (unsigned-byte-p n x)
                   (natp m)
                   (<= n m))
              (equal (logbitp m x) nil))
     :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                       ihsext-recursive-redefs)
                                      ()))))))

 (local
  (def-gl-thm flgi-!flgi-different-helper
    :hyp (unsigned-byte-p 32 rflags)
    :concl (equal (bitops::logsquash -11
                                     (loghead 2 (logtail 12 rflags)))
                  (loghead 2 (logtail 12 rflags)))
    :g-bindings
    `((rflags (:g-number ,(gl-int 0 1 33))))))

 (defthm flgi-!flgi
   (implies (and (member i1 *flg-names*)
                 (member i2 *flg-names*)
                 (if (equal i2 *iopl*)
                     (unsigned-byte-p 2 v)
                   (unsigned-byte-p 1 v))
                 (x86p x86))
            (equal (flgi i1 (!flgi i2 v x86))
                   (if (equal i1 i2) v (flgi i1 x86))))
   :hints (("Goal" :in-theory (e/d (flgi !flgi bool->bit) ()))))

 (local
  (def-gl-thm !flgi-!flgi-same-helper-1
    :hyp (and (unsigned-byte-p 32 rflags)
              (unsigned-byte-p 32 y)
              (equal y
                     (part-install 0 *2^32-1* :low x :width 1))
              (member x *flg-names*)
              (unsigned-byte-p 1 v1)
              (unsigned-byte-p 1 v2))
    :concl (equal (logior (ash v2 x)
                          (logand y (logior (ash v1 x)
                                            (logand y rflags))))
                  (logior (ash v2 x)
                          (logand y rflags)))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat rflags 32)
           (:nat y 32))
     (:nat x 5)
     (:nat v1 2)
     (:nat v2 2))))

 (local
  (def-gl-thm !flgi-!flgi-same-helper-2
    :hyp (and (unsigned-byte-p 32 rflags)
              (unsigned-byte-p 32 y)
              (equal y
                     (part-install 0 *2^32-1* :low x :width 2))
              (member x *flg-names*)
              (unsigned-byte-p 2 v1)
              (unsigned-byte-p 2 v2))
    :concl (equal (logior (ash v2 x)
                          (logand y (logior (ash v1 x)
                                            (logand y rflags))))
                  (logior (ash v2 x)
                          (logand y rflags)))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat rflags 32)
           (:nat y 32))
     (:nat x 5)
     (:nat v1 2)
     (:nat v2 2))))

 (defthm !flgi-!flgi-same
   (implies (and (member i *flg-names*)
                 (x86p x86))
            (equal (!flgi i v2 (!flgi i v1 x86))
                   (!flgi i v2 x86)))
   :hints (("Goal" :in-theory (e/d (!flgi bool->bit) ()))))

 (local
  (def-gl-thm !flgi-!flgi-unequal-helper-1
    :hyp (and (unsigned-byte-p 32 rflags)
              (unsigned-byte-p 32 yval)
              (equal yval
                     (part-install 0 *2^32-1*
                                   :low y
                                   :width 1))
              (member y *flg-names*)
              (not (equal y *iopl*))
              (< 0 y)
              (unsigned-byte-p 1 v1)
              (unsigned-byte-p 1 v2))
    :concl (equal
            (logior (ash v2 y)
                    (logand yval
                            (logior v1 (bitops::logsquash 1 rflags))))
            (logior v1 (ash v2 y)
                    (logand (1- yval)
                            (bitops::logsquash 1 rflags))))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat rflags 32)
           (:nat yval 32))
     (:nat y 5)
     (:mix (:nat v1 2)
           (:nat v2 2)))))

 (local
  (def-gl-thm !flgi-!flgi-unequal-helper-2
    :hyp (and (unsigned-byte-p 32 rflags)
              (unsigned-byte-p 32 xval)
              (unsigned-byte-p 32 yval)
              (equal xval
                     (part-install 0 *2^32-1*
                                   :low x
                                   :width (if (equal x *iopl*)
                                              2
                                            1)))
              (equal yval
                     (part-install 0 *2^32-1*
                                   :low y
                                   :width (if (equal y *iopl*)
                                              2
                                            1)))
              (member x *flg-names*)
              (member y *flg-names*)
              (not (equal x y))
              (if (equal x *iopl*)
                  (unsigned-byte-p 2 v1)
                (unsigned-byte-p 1 v1))
              (if (equal y *iopl*)
                  (unsigned-byte-p 2 v2)
                (unsigned-byte-p 1 v2)))
    :concl (equal (logior (ash v2 y)
                          (logand yval
                                  (logior (ash v1 x)
                                          (logand xval rflags))))
                  (logior (ash v1 x)
                          (logand xval
                                  (logior (ash v2 y)
                                          (logand yval rflags)))))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat rflags 32)
           (:nat xval 32)
           (:nat yval 32))
     (:mix (:nat x 5)
           (:nat y 5))
     (:mix (:nat v1 2)
           (:nat v2 2)))))

 (local
  (def-gl-thm !flgi-!flgi-unequal-helper-3
    :hyp (and (unsigned-byte-p 32 rflags)
              (unsigned-byte-p 1 v1)
              (unsigned-byte-p 2 v2))
    :concl (equal (logior (ash v2 12)
                          (logand 4294955007
                                  (logior v1
                                          (bitops::logsquash 1 rflags))))
                  (logior v1 (ash v2 12)
                          (logand 4294955006
                                  (bitops::logsquash 1 rflags))))
    :g-bindings
    (gl::auto-bindings
     (:nat rflags 32)
     (:mix (:nat v1 2)
           (:nat v2 2)))))

 (defthm !flgi-!flgi-different-unequal-indices
   (implies (and (not (equal i1 i2))
                 (member i1 *flg-names*)
                 (member i2 *flg-names*)
                 (x86p x86))
            (equal (!flgi i2 v2 (!flgi i1 v1 x86))
                   (!flgi i1 v1 (!flgi i2 v2 x86))))
   :hints (("Goal" :in-theory (e/d (!flgi bool->bit) ())))
   :rule-classes ((:rewrite :loop-stopper ((i2 i1)))))

 (defthm !flgi-!flgi-different-concrete-indices
   (implies (and (syntaxp (quotep i1))
                 (syntaxp (quotep i2))
                 (member i1 *flg-names*)
                 (member i2 *flg-names*)
                 (x86p x86))
            (equal (!flgi i2 v2 (!flgi i1 v1 x86))
                   (if (< i1 i2)
                       (!flgi i1 v1 (!flgi i2 v2 x86))
                     (!flgi i2 v2 (!flgi i1 v1 x86)))))
   :rule-classes ((:rewrite :loop-stopper ((i2 i1)))))

 (local
  (def-gl-thm !flgi-flgi-helper-1
    :hyp (unsigned-byte-p 32 rflags)
    :concl (equal (logior (logand 4294955007 rflags)
                          (ash (loghead 2 (logtail 12 rflags))
                               12))
                  rflags)
    :g-bindings
    (gl::auto-bindings
     (:nat rflags 32))))

 (local
  (defthm unsigned-byte-p-not-logbitp-and-logand
    (implies (and (unsigned-byte-p 32 x)
                  (not (logbitp m x))
                  (equal mval
                         (part-install 0 *2^32-1*
                                       :low m
                                       :width 1)))
             (equal (logand mval x) x))
    :hints ((and stable-under-simplificationp
                 (bitops::equal-by-logbitp-hint)))))

 (local
  (defthm unsigned-byte-p-not-logbitp-and-logsquash
    (implies (and (unsigned-byte-p 32 x)
                  (not (logbitp 0 x)))
             (equal (bitops::logsquash 1 x) x))
    :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                      ihsext-recursive-redefs)
                                     ())))))

 (local
  (defthm unsigned-byte-p-logbitp-and-logsquash
    (implies (and (unsigned-byte-p 32 x)
                  (logbitp 0 x))
             (equal (logior 1 (bitops::logsquash 1 x)) x))
    :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                      ihsext-recursive-redefs)
                                     ())))))

 (local
  (defthmd unsigned-byte-p-logbitp-and-logand-helper-1
    (implies (and (unsigned-byte-p 32 x)
                  (natp m)
                  (logbitp m x)
                  (equal mval1
                         (part-install 0 *2^32-1*
                                       :low m
                                       :width 1))
                  (equal mval2 (ash 1 m)))
             (equal (logior mval2 (logand mval1 x))
                    (logand (logior mval2 mval1) x)))
    :hints (("Goal" :in-theory (e/d (bool->bit b-ior b-and) ()))
            (and stable-under-simplificationp
                 (bitops::equal-by-logbitp-hint)))))

 (local
  (defthmd unsigned-byte-p-logbitp-and-logand-helper-2
    (implies (and (unsigned-byte-p 32 x)
                  (natp m)
                  (logbitp m x)
                  (equal mval1
                         (part-install 0 *2^32-1*
                                       :low m
                                       :width 1))
                  (equal mval2 (ash 1 m)))
             (equal (logand (logior mval2 mval1) x)
                    x))
    :hints (("Goal" :in-theory (e/d (bool->bit b-ior b-and) ()))
            (and stable-under-simplificationp
                 (bitops::equal-by-logbitp-hint)))))

 (local
  (defthm unsigned-byte-p-logbitp-and-logand
    (implies (and
              ;; Since m is a free variable, I've put the logbitp
              ;; hypothesis at the top to help ACL2 do matching
              ;; effectively.  Moving this hyp to a lower position will
              ;; reduce the applicability of this rule.
              (logbitp m x)
              (syntaxp (quotep mval1))
              (syntaxp (quotep mval2))
              (unsigned-byte-p 32 x)
              (natp m)
              (equal mval1
                     (part-install 0 *2^32-1*
                                   :low m
                                   :width 1))
              (equal mval2 (ash 1 m)))
             (equal (logior mval2 (logand mval1 x))
                    x))
    :hints (("Goal" :use (unsigned-byte-p-logbitp-and-logand-helper-1
                          unsigned-byte-p-logbitp-and-logand-helper-2)))))

 (defthmd !flgi-flgi
   (implies (and (equal x (flgi i x86))
                 (member i *flg-names*)
                 (x86p x86))
            (equal (!flgi i x x86) x86))
   :hints (("Goal" :in-theory
            (e/d
             (flgi !flgi bool->bit xw-xr)
             (member-equal (member-equal))))))

 ) ;; End of encapsulate

;; ======================================================================

;; Making some functions untouchable after proving RoW/WoW thms about
;; them:

(push-untouchable (
                   ;; Accessors
                   env
                   env$a
                   env$c
                   env-read-logic
                   env-write-logic
                   read-x86-file-des-logic
                   read-x86-file-contents-logic
                   ;; Updaters
                   !env
                   !env$a
                   !env$c
                   write-x86-file-des-logic
                   delete-x86-file-des-logic
                   write-x86-file-contents-logic
                   delete-x86-file-contents-logic
                   pop-x86-oracle-logic
                   !undef
                   )
                  t)

;; ======================================================================
