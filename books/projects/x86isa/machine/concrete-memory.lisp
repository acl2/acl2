; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Matt Kaufmann       <kaufmann@cs.utexas.edu>
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>

(in-package "X86ISA")

(include-book "concrete-state")

;; ======================================================================

(defsection concrete-memory
  :parents (machine)
  :short "Definitions of @('mem$ci') and @('!mem$ci'), and their
  read/write theorems."
  )

;; ======================================================================

;; (globally-disable '(unsigned-byte-p signed-byte-p))

(local (in-theory (enable* concrete-stobj-fns-ruleset)))
;; Note, x86$cp-pre and x86$cp are still disabled.

;; ======================================================================
;; Some theorems about loghead, logior, plus:
;; ======================================================================

(encapsulate
 ()

 (local (include-book "centaur/bitops/ihs-extensions" :dir :system))
 (local (include-book "arithmetic/top-with-meta" :dir :system))

 (defthmd expt-to-ash
   (implies (and (natp n)
                 (integerp x))
            (equal (ash x n) (* x (expt 2 n))))
   :hints (("Goal" :in-theory (e/d* (expt ash floor) ()))))

 (defthmd logior-expt-to-plus-helper-1
   (implies (and (natp n)
                 (integerp x)
                 (unsigned-byte-p n y))
            (equal (loghead n (logior y (ash x n))) y))
   :hints (("Goal" :in-theory (e/d* (unsigned-byte-p
                                     ihsext-inductions
                                     ihsext-recursive-redefs)
                                    ()))))

 (defthmd logior-expt-to-plus-helper-2
   (implies (and (natp n)
                 (integerp x)
                 (unsigned-byte-p n y))
            (equal (logtail n (logior y (ash x n))) x))
   :hints (("Goal" :in-theory (e/d* (unsigned-byte-p
                                     ihsext-inductions
                                     ihsext-recursive-redefs)
                                    ()))))

 (defthmd putting-loghead-and-logtail-together
   (implies (and (equal (logtail n w) x)
                 (equal (loghead n w) y)
                 (integerp w)
                 (natp n))
            (equal (+ y (ash x n)) w))
   :hints (("Goal" :in-theory (e/d* (ihsext-recursive-redefs
                                     ihsext-inductions)
                                    ()))))

 (defthmd logior-to-plus-with-ash
   (implies (and (natp n)
                 (integerp x)
                 (unsigned-byte-p n y))
            (equal (logior y (ash x n))
                   (+ y (ash x n))))
   :hints (("Goal"
            :use ((:instance logior-expt-to-plus-helper-1)
                  (:instance logior-expt-to-plus-helper-2)
                  (:instance putting-loghead-and-logtail-together
                             (w (logior y (ash x n))))))))

 ;; Sometimes, it's easier to reason about addition instead of logical
 ;; OR.

 (defthm logior-expt-to-plus
   (implies (and (natp n)
                 (integerp x)
                 (unsigned-byte-p n y))
            (equal (logior y (* x (expt 2 n)))
                   (+ (* (expt 2 n) x) y)))
   :hints (("Goal" :use ((:instance expt-to-ash)
                         (:instance logior-to-plus-with-ash)))))

 ;; Now for a new version of logior-expt-to-plus using a constant in
 ;; place of (expt 2 n)....

 (defthm logior-expt-to-plus-quotep
   (implies (and (bind-free (and (quotep k)
                                 (let* ((k0 (acl2::unquote k))
                                        (n (log-2 k0 0)))
                                   (and (eql k0 (expt 2 n))
                                        (list (cons 'n (kwote n)))))))
                 (natp n)
                 (eql k (expt 2 n))
                 (integerp x)
                 (unsigned-byte-p n y))
            (equal (logior y (* k x))
                   (+ (* k x) y))))

 (defthm constant-upper-bound-of-logior-for-naturals
   (implies (and (bind-free (and (quotep k)
                                 (let* ((k0 (acl2::unquote k))
                                        (n (log-2 k0 0)))
                                   (and (eql k0 (expt 2 n))
                                        (list (cons 'n (kwote n)))))))
                 (eql k (expt 2 n))
                 (< x k)
                 (< y k)
                 (natp x)
                 (natp y)
                 (posp n))
            (< (logior x y) k))
   :hints (("Goal" :use bitops::upper-bound-of-logior-for-naturals))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm break-logand-into-loghead-and-logtail
   (implies (and (natp x)
                 (natp y)
                 (natp n))
            (equal (logand x y)
                   (+
                    (* (expt 2 n)
                       (logand (logtail n x)
                               (logtail n y)))
                    (logand (loghead n x)
                            (loghead n y)))))
   :hints (("Goal" :in-theory (e/d (loghead logtail ifix) ())))
   :rule-classes nil)

 (defthmd logior-loghead-to-+-loghead
   ;; We disabled this rule because it interferes with proof of
   ;; |address < len(mem-array) when page is present|.
   (implies (and (natp n)
                 (integerp x*2^n)
                 (equal 0 (loghead n x*2^n))
                 (natp i))
            (equal (logior (loghead n i) x*2^n)
                   (+ (loghead n i) x*2^n)))
   :hints (("Goal"
            :use ((:instance logior-expt-to-plus
                             (y (loghead n i))
                             (x (ash x*2^n -n))
                             (n n))))))

 (defthm |(ash x 1) != 1|
   (implies (natp x)
            (equal (equal (ash x 1) 1) nil))
   :hints (("Goal" :in-theory (e/d (ash floor) ()))))

 (defthm |(ash a x) <= b ==> (ash (1+ a) x) <= b|
   (implies (and (< (ash a x) b)
                 (equal (loghead x b) 0)
                 (integerp a)
                 (<= 0 a)
                 (integerp x)
                 (<= 0 x)
                 (integerp b)
                 (<= 0 b))
            (<= (ash (1+ a) x) b))
   :hints (("Goal" :in-theory (e/d (ash floor ifix) ()))))

 (defthm logtail-inequality-1
   (implies (and (natp lower)
                 (natp upper)
                 (< (1+ lower) upper))
            (< lower (logtail 1 (+ lower upper))))
   :hints (("Goal" :in-theory (e/d (logtail) ())))
   :rule-classes :linear)

 (defthm logtail-inequality-2
   (implies (and (natp lower)
                 (natp upper)
                 (< (1+ lower) upper))
            (<= (+ 1 (logtail 1 (+ lower upper))) upper))
   :hints (("Goal" :in-theory (e/d (logtail) ())))
   :rule-classes :linear)

 (defthm <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
   (implies (and (< next len)
                 (integerp i)
                 (<= 0 i)
                 (< i *pseudo-page-size-in-bytes*)
                 (force (natp next))
                 (force (natp len))
                 (force (equal (loghead *2^x-byte-pseudo-page* next) 0))
                 (equal (loghead *2^x-byte-pseudo-page* len) 0))
            (< (logior next i) len)))

 (defthm <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
   (implies (and (< next len)
                 (integerp i)
                 (<= 0 i)
                 (< i *pseudo-page-size-in-bytes*)
                 (force (natp next))
                 (force (natp len))
                 (force (equal (loghead *2^x-byte-pseudo-page* next) 0))
                 (equal (loghead *2^x-byte-pseudo-page* len) 0))
            (< (logior i next) len))
   :hints (("Goal"
            :in-theory
            (disable <-preserved-by-adding-<-*pseudo-page-size-in-bytes*)
            :use
            <-preserved-by-adding-<-*pseudo-page-size-in-bytes*)))

 (defthmd mem-table-entries-logic-update-nth-helper-2
   (implies (and (natp next-addr)
                 (natp lower)
                 (integerp (car mem-table))
                 (mem-tablep (cdr mem-table))
                 (< (logtail 1 (nth lower mem-table))
                    next-addr)
                 (<= (ash next-addr 1)
                     (nth lower mem-table)))
            (equal (logtail 1 (nth lower mem-table))
                   next-addr))
   :hints
   (("Goal" :in-theory (e/d (logtail)
                            ((:rewrite acl2::|(equal (if a b c) x)|))))))

 (defthmd mem-table-entries-logic-update-nth-helper-3
   (implies (and (natp next-addr)
                 (mem-tablep (cdr mem-table))
                 (equal (nth index mem-table) 1)
                 (< (logtail 1 (nth index (cdr mem-table)))
                    next-addr)
                 (< (ash next-addr 1)
                    (nth index (cdr mem-table))))
            (equal (logtail 1 (nth index (cdr mem-table)))
                   next-addr))
   :hints
   (("Goal" :in-theory (e/d (logtail)
                            ((:rewrite acl2::|(equal (if a b c) x)|))))))

 (defthm breaking-logior-apart-1
   (implies (and (force (unsigned-byte-p *mem-table-size-bits* low25-i))
                 (force (unsigned-byte-p *mem-table-size-bits* low25-j))
                 (equal (logior (loghead *2^x-byte-pseudo-page* i)
                                (ash low25-i *2^x-byte-pseudo-page*))
                        (logior (loghead *2^x-byte-pseudo-page* j)
                                (ash low25-j *2^x-byte-pseudo-page*))))
            (equal low25-i low25-j))
   :hints
   (("Goal" :in-theory (e/d* (ifix) (not natp))
     :use ((:instance logior-loghead-to-+-loghead
                      (n *2^x-byte-pseudo-page*)
                      (i i)
                      (x*2^n (ash low25-i *2^x-byte-pseudo-page*)))
           (:instance logior-loghead-to-+-loghead
                      (n *2^x-byte-pseudo-page*)
                      (i j)
                      (x*2^n (ash low25-j *2^x-byte-pseudo-page*))))))
   :rule-classes nil)

 (defthmd breaking-logior-apart-2
   (implies (and (force (unsigned-byte-p *mem-table-size-bits* low25-i))
                 (force (unsigned-byte-p *mem-table-size-bits* low25-j))
                 (equal (logior (loghead *2^x-byte-pseudo-page* i)
                                (ash low25-i *2^x-byte-pseudo-page*))
                        (logior (loghead *2^x-byte-pseudo-page* j)
                                (ash low25-j *2^x-byte-pseudo-page*))))
            (equal (loghead *2^x-byte-pseudo-page* i)
                   (loghead *2^x-byte-pseudo-page* j)))
   :hints (("Goal" :in-theory (e/d* (ifix) (not natp))
            :use ((:instance breaking-logior-apart-1)))))

 (defthm logtail-and-loghead-equality
   (implies (and (equal (logtail n x) (logtail n y))
                 (equal (loghead n x) (loghead n y))
                 (natp x)
                 (natp y))
            (equal x y))
   :hints (("Goal" :in-theory (enable logtail loghead)))
   :rule-classes ((:forward-chaining
                   ;; These trigger terms are no good if the hyps of
                   ;; the theorem to be proved have something like
                   ;; (and (equal (logtail n x) 0)
                   ;;      (equal (logtail n x) 0))
                   ;; But, for my use case so far, the following terms
                   ;; do fine, though (equal (loghead n x) (loghead n
                   ;; y)) is not a good candidate since logheads
                   ;; appear separately, like:
                   ;; (and (equal (loghead n x) 0)
                   ;;      (equal (loghead n x) 0))
                   :trigger-terms ((equal (logtail n x) (logtail n y))
                                   ;; (equal (loghead n x) (loghead n y))
                                   ))))

 (defthm equal-ash-ash
   (implies (and (natp x) (natp y) (natp n))
            (equal (equal (ash x n) (ash y n))
                   (equal x y)))
   :hints (("Goal" :in-theory (enable ash))))

 (defthm <=-logior
   (and (implies (and (natp x) (natp y))
                 (<= y (logior x y)))
        (implies (and (natp x) (natp y))
                 (<= x (logior x y))))
   :rule-classes :linear)

 (defthm len-nth-*mem-arrayi*
   (implies (x86$cp x86$c)
            (<= (ash (nth *mem-array-next-addr* x86$c) *2^x-byte-pseudo-page*)
                *mem-size-in-bytes*))
   :hints (("Goal" :in-theory (e/d (x86$cp good-memp))))
   :rule-classes :linear)

 (defthmd concrete-mem-hack ; len = (len (nth *mem-arrayi* x86$c))
   (implies (and (equal (ash e *2^x-byte-pseudo-page*) len)
                 (natp e) ; (expected-mem-array-next-addr 0 33554432 x86$c)
                 (<= e 33554431)
                 ;;(<= *mem-size-in-bytes* (* 2 len))
                 )
            (< (logior (loghead *2^x-byte-pseudo-page* j) len)
               *mem-size-in-bytes*)))

 )

;; ======================================================================

;; Locally including helper arithmetic books:
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ======================================================================
;; Definition of mem$ci
;; ======================================================================

(defsection concrete-memory-byte-read-function

  :parents (concrete-memory)

  :short "Concrete memory byte read function @('mem$ci')"

  ;; mem$ci:

  (defthm-unsigned-byte-p logtail-*2^x-byte-pseudo-page*-of-physical-address
    :hyp (unsigned-byte-p #.*physical-address-size* i)
    :bound #.*mem-table-size-bits*
    :concl (logtail #.*2^x-byte-pseudo-page* i)
    :gen-type t
    :gen-linear t
    :hints-l (("Goal" :in-theory (disable unsigned-byte-p-of-logtail))))

  (defthm good-mem-table-entriesp-logic-property
    (let ((addr (nth i mem-table)))
      (implies (and (good-mem-table-entriesp-logic
                     z table-bound array-next-addr mem-table)
                    (natp i)
                    (<= z i)
                    (<= i table-bound)
                    (not (eql addr 1)))
               (and (natp addr)
                    (equal (loghead 1 addr) 0)
                    (< (logtail 1 addr) array-next-addr))))
    :hints (("Goal"
             :in-theory (enable good-mem-table-entriesp-logic)
             :induct (good-mem-table-entriesp-logic
                      z table-bound array-next-addr mem-table))))

  (defthm |logtail-1 of mem-table value < mem-array-next-addr|
    (implies (and (force (x86$cp x86$c))
                  (force (natp i))
                  (force (< i *mem-table-size*))
                  (not (eql (nth i (nth *mem-tablei* x86$c)) 1)))
             (< (logtail 1 (nth i (nth *mem-tablei* x86$c)))
                (nth *mem-array-next-addr* x86$c)))
    :hints (("Goal" :in-theory (enable x86$cp x86$cp-pre good-memp)))
    :rule-classes :linear)

  (defthm |address < shift(mem-array-next-addr) when page is present|-helper
    (implies (and (natp a)
                  (< a *mem-table-size*)
                  (natp b)
                  (<= b *mem-table-size*)
                  (< a b)
                  (natp x)
                  (< x *pseudo-page-size-in-bytes*))
             (< (logior x (ash a *2^x-byte-pseudo-page*))
                (ash b *2^x-byte-pseudo-page*)))
    :hints (("Goal" :in-theory (enable ash floor)))
    :rule-classes nil)

  (defthm |address < shift(mem-array-next-addr) when page is present|
    (implies (and (integerp addr)
                  (<= 0 addr)
                  (< addr *mem-size-in-bytes*)
                  (x86$cp x86$c)
                  (not (equal (nth (logtail *2^x-byte-pseudo-page* addr)
                                   (nth *mem-tablei* x86$c))
                              1)))
             (< (logior (loghead *2^x-byte-pseudo-page* addr)
                        (ash (logtail 1
                                      (nth (logtail *2^x-byte-pseudo-page* addr)
                                           (nth *mem-tablei* x86$c)))
                             *2^x-byte-pseudo-page*))
                (ash (nth *mem-array-next-addr* x86$c) *2^x-byte-pseudo-page*)))
    :hints (("Goal" :in-theory (e/d* (x86$cp-pre x86$cp) (force (force)))
             :use ((:instance |address < shift(mem-array-next-addr) when page is present|-helper
                              (x (loghead *2^x-byte-pseudo-page* addr))
                              (a (logtail 1
                                          (nth (logtail *2^x-byte-pseudo-page* addr)
                                               (nth *mem-tablei* x86$c))))
                              (b (nth *mem-array-next-addr*
                                      x86$c))))))
    :rule-classes :linear)

  (defthm |address < len(mem-array) when page is present|
    (implies (and (integerp i)
                  (<= 0 i)
                  (< i *mem-size-in-bytes*)
                  (x86$cp x86$c)
                  (not (equal (nth (logtail *2^x-byte-pseudo-page* i)
                                   (nth *mem-tablei* x86$c))
                              1)))
             (< (logior (loghead *2^x-byte-pseudo-page* i)
                        (ash (logtail 1
                                      (nth (logtail *2^x-byte-pseudo-page* i)
                                           (nth *mem-tablei* x86$c)))
                             *2^x-byte-pseudo-page*))
                (len (nth *mem-arrayi* x86$c))))
    :hints (("Goal" :in-theory (e/d (x86$cp-pre good-memp x86$cp)
                                    ())))
    :rule-classes :linear)

  (define mem$ci
    ((i (unsigned-byte-p #.*physical-address-size* i)
        "Physical address"
        :type (unsigned-byte #.*physical-address-size*))
     (x86$c x86$cp "Note that the guard is @('x86$cp'), which is
    different from @('x86$cp-pre') that is added to the guard
    obligation by default with the keyword <tt>:stobj</tt>."))
    :enabled t

    (b* ((i-top (the (unsigned-byte #.*mem-table-size-bits*)
                  (ash i (- #.*2^x-byte-pseudo-page*))))
         (addr (the (unsigned-byte #.*mem-table-size-bits+1*)
                 (mem-tablei i-top x86$c))))

        (cond ((eql addr 1) ;; page is not present
               #.*default-mem-value*)

              (t
               (let ((index
                      (mbe :logic
                           (logior (ash (logtail 1 addr) #.*2^x-byte-pseudo-page*)
                                   (loghead #.*2^x-byte-pseudo-page* i))
                           :exec
                           (logior (ash
                                    (the (unsigned-byte #.*mem-table-size-bits*)
                                      (ash addr -1))
                                    #.*2^x-byte-pseudo-page*)
                                   (logand
                                    #.*pseudo-page-size-in-bytes-1* i)))))

                 (mem-arrayi index x86$c))))))

  )

;; ======================================================================
;; Definition of !mem$ci
;; ======================================================================

(defsection concrete-memory-byte-write-function

  :parents (concrete-memory)

  :short "Concrete memory byte write function @('!mem$ci')"

  (defthm mem-array-next-addr-is-expected-mem-array-next-addr
    (implies (x86$cp x86$c)
             (equal (nth *mem-array-next-addr* x86$c)
                    (expected-mem-array-next-addr
                     0 (mem-table-length x86$c) x86$c)))
    :hints (("Goal" :in-theory (e/d (x86$cp good-memp)
                                    ()))))

  (defthm expected-mem-array-next-addr-bound-general
    (implies (and (equal 1 (nth j (nth *mem-tablei* x86$c)))
                  (natp i)
                  (natp j)
                  (natp k)
                  (<= i j)
                  (< j k))
             (<= (expected-mem-array-next-addr i k x86$c)
                 (1- (- k i))))
    :hints (("Goal" :expand ((expected-mem-array-next-addr j k x86$c))
             :use (expected-mem-array-in-parts)))
    :rule-classes nil)

  (defthm expected-mem-array-next-addr-bound-when-page-absent
    (implies (and (equal 1 (nth i (nth *mem-tablei* x86$c))) ;; i is free
                  (force (natp i))
                  (force (< i *mem-table-size*)))
             (<= (expected-mem-array-next-addr 0 *mem-table-size* x86$c)
                 *mem-table-size-1*))
    :hints (("Goal"
             :use ((:instance expected-mem-array-next-addr-bound-general
                              (i 0)
                              (j i)
                              (k *mem-table-size*)))))
    :rule-classes :linear)

  (defrulel natp-mem-array-next-addr
    (implies (x86$cp-pre x86$c)
             (and (integerp (nth *mem-array-next-addr* x86$c))
                  (<= 0 (nth *mem-array-next-addr* x86$c))))
    :hints (("Goal" :in-theory (enable x86$cp-pre)))
    :rule-classes (:type-prescription :rewrite))

  (define add-page-x86$c
    ((i (unsigned-byte-p #.*mem-table-size-bits* i)
        :type (unsigned-byte #.*mem-table-size-bits*))
     (x86$c x86$cp))

    :guard (equal (mem-tablei i x86$c) 1) ;; page not present

    :guard-hints (("Goal" :in-theory (enable x86$cp ash floor good-memp)))

    :enabled t

    :returns (mv (addr (unsigned-byte-p #.*mem-table-size-bits* addr)
                       :hyp :guard
                       :hints (("Goal" :in-theory (enable x86$cp
                                                          x86$cp-pre
                                                          good-memp))))
                 x86$c)

    (b* (((the (integer 0 #.*mem-table-size*) addr) (mem-array-next-addr x86$c))
         (len (mem-array-length x86$c))
         (x86$c (cond ((equal (ash addr #.*2^x-byte-pseudo-page*)
                              len) ;; must resize!
                       (resize-mem-array (min (* #.*mem-array-resize-factor*
                                                 len)
                                              #.*mem-size-in-bytes*)
                                         x86$c))
                      (t x86$c)))
         (x86$c (!mem-array-next-addr (+ addr 1) x86$c))
         (x86$c (!mem-tablei i (ash addr 1) x86$c)))
        (mv addr x86$c)))

  (defthm len-resize-list
    (equal (len (resize-list lst n default-value))
           (nfix n)))

  (defthmd |addr < 2 * len-mem-array|
    (implies (and (<= *initial-mem-array-length* (len (nth *mem-arrayi* x86$c)))
                  (equal (loghead *2^x-byte-pseudo-page*
                                  (len (nth *mem-arrayi* x86$c)))
                         0)
                  (integerp i)
                  (<= 0 i))
             (< (logior (loghead *2^x-byte-pseudo-page* i)
                        (len (nth *mem-arrayi* x86$c)))
                (* 2 (len (nth *mem-arrayi* x86$c)))))
    :hints (("Goal" :in-theory (enable logior-loghead-to-+-loghead))))

  (defthmd ash-less-than-constant
    (implies (and (natp x)
                  (natp n)
                  (rationalp c))
             (equal (< (ash x n) c)
                    (< x (/ c (expt 2 n)))))
    :hints (("Goal" :in-theory (enable ash floor))))

  (define !mem$ci
    ((i (unsigned-byte-p #.*physical-address-size* i)
        "Physical address"
        :type (unsigned-byte #.*physical-address-size*))
     (v n08p :type (unsigned-byte 8))
     (x86$c x86$cp "Note that the guard is @('x86$cp'), which is
    different from @('x86$cp-pre') that is added to the guard
    obligation by default with the keyword <tt>:stobj</tt>."))

    :enabled t

    :guard-hints (("Goal"
                   :in-theory (enable x86$cp good-memp
                                      ash-less-than-constant
                                      |addr < 2 * len-mem-array|)))

    (b* (((the (unsigned-byte #.*mem-table-size-bits*) i-top)
          (ash i (- #.*2^x-byte-pseudo-page*)))
         ((the (unsigned-byte #.*2^x-byte-pseudo-page*) addr)
          (mem-tablei i-top x86$c))
         ((mv (the (unsigned-byte #.*mem-table-size-bits*) addr) x86$c)
          (cond ((eql addr 1) ;; page is not present
                 (add-page-x86$c i-top x86$c))
                (t (mv (ash addr -1) x86$c))))
         (index (logior (ash (the (unsigned-byte #.*mem-table-size-bits+1*) addr)
                             #.*2^x-byte-pseudo-page*)
                        (logand #.*pseudo-page-size-in-bytes-1* i))))

        (!mem-arrayi index v x86$c)))
  )

;; ======================================================================

(in-theory (disable mem$ci !mem$ci))

;; ======================================================================

(defsection concrete-memory-accessor-returns-n08p

  :parents (concrete-memory)

  :short "We prove that @('mem$ci') returns an @(see n08p)."

  (defthm-unsigned-byte-p n08p-mem$ci

    :hyp (and (x86$cp x86$c)
              (unsigned-byte-p *physical-address-size* addr))
    :bound 8
    :concl (mem$ci addr x86$c)

    :hints (("Goal" :in-theory (e/d (mem$ci) ())))

    :gen-type t
    :gen-linear t))

;; ======================================================================

(defsection concrete-memory-update-preserves-strong-recognizer

  ;; [Shilpi]: This giant section should really be three sections:
  ;; 1. concrete-memory-update-preserves-strong-recognizer
  ;; 2. mem-table-is-one-to-one
  ;; 3. read-write

  :parents (concrete-memory)

  :short "We prove @('x86$cp-!mem$ci') in this section."

  (local
   (encapsulate
    ()

    (local (in-theory (e/d (good-mem-table-entriesp-logic) ())))

    (defthm good-mem-table-entriesp-logic-update
      (implies (and (natp index)
                    (good-mem-table-entriesp-logic lower upper
                                                   array-next-addr mem-table)
                    (natp addr)
                    (equal (logand #x1 addr) 0)
                    (<= (logtail 1 addr) array-next-addr))
               (good-mem-table-entriesp-logic
                lower upper
                (+ 1 array-next-addr)
                (update-nth index addr mem-table))))

    (defrulel good-mem-table-entriesp-logic-preserved-lemma
      (implies (and (good-mem-table-entriesp-logic lower upper1 array-bound
                                                   x86$c)
                    (natp upper2)
                    (<= lower upper2)
                    (<= upper2 upper1))
               (good-mem-table-entriesp-logic lower upper2 array-bound
                                              x86$c)))

    (defthm good-mem-table-entriesp-logic-preserved
      (implies (and (good-mem-table-entriesp-logic lower1 upper1 array-bound
                                                   x86$c)
                    (natp lower2)
                    (natp upper2)
                    (<= lower1 lower2)
                    (<= lower2 upper2)
                    (<= upper2 upper1))
               (good-mem-table-entriesp-logic lower2 upper2 array-bound x86$c)))
    ))

  (defrulel good-mem-arrayp-1-logic-update-nth
    (implies (and (n08p v)
                  (natp addr)
                  (< addr ash-mem-array-next-addr)
                  (good-mem-arrayp-1-logic ash-mem-array-next-addr
                                           (len mem-array)
                                           mem-array))
             (good-mem-arrayp-1-logic ash-mem-array-next-addr
                                      (len mem-array)
                                      (update-nth addr v mem-array)))
    :hints (("Goal" :in-theory (e/d (x86$cp) (force (force))))))

  (defrulel good-mem-arrayp-1-logic-preserved-upward
    (implies (and (good-mem-arrayp-1-logic index1 len mem-array)
                  (natp index1)
                  (natp index2)
                  (<= index1 index2))
             (good-mem-arrayp-1-logic index2 len mem-array)))

  (defrulel x86$cp-pre-update-nth-mem-arrayi
    (implies (forced-and (x86$cp-pre x86$c)
                         (n08p v)
                         (natp addr)
                         (< addr (len (nth *mem-arrayi* x86$c))))
             (x86$cp-pre (update-nth
                          *mem-arrayi*
                          (update-nth addr v (nth *mem-arrayi* x86$c))
                          x86$c)))
    :hints (("Goal" :in-theory (enable x86$cp-pre))))

  (defrulel x86$cp-update-nth-mem-arrayi-generic
    (implies (and (x86$cp x86$c)
                  (n08p v)
                  (natp addr)
                  (< addr (ash (nth *mem-array-next-addr* x86$c)
                               *2^x-byte-pseudo-page*)))
             (x86$cp (update-nth
                      *mem-arrayi*
                      (update-nth addr v (nth *mem-arrayi* x86$c))
                      x86$c)))
    :hints (("Goal" :in-theory (e/d (x86$cp good-memp) ()))))

  (defthmd x86$cp-update-nth-mem-arrayi-less-generic-helper
    (implies (and (x86$cp x86$c)
                  (n08p v)
                  (natp i)
                  (< i *mem-size-in-bytes*)
                  (natp addr)
                  (< addr (nth *mem-array-next-addr* x86$c)))
             (< (logior (loghead *2^x-byte-pseudo-page* i)
                        (ash addr *2^x-byte-pseudo-page*))
                (ash (nth *mem-array-next-addr* x86$c)
                     *2^x-byte-pseudo-page*)))
    :hints (("Goal"
             :in-theory (e/d (x86$cp logior-loghead-to-+-loghead ash floor) ()))))

  (defthm x86$cp-update-nth-mem-arrayi-less-generic
    (implies (and (x86$cp x86$c)
                  (n08p v)
                  (unsigned-byte-p *physical-address-size* i)
                  (natp addr)
                  (< addr (nth *mem-array-next-addr* x86$c)))
             (x86$cp (update-nth
                      *mem-arrayi*
                      (update-nth
                       (logior (loghead *2^x-byte-pseudo-page* i)
                               (ash addr *2^x-byte-pseudo-page*))
                       v
                       (nth *mem-arrayi* x86$c))
                      x86$c)))
    :hints (("Goal" :in-theory (e/d (x86$cp
                                     good-memp
                                     logior-loghead-to-+-loghead
                                     ash-less-than-constant)
                                    ())
             :use ((:instance x86$cp-update-nth-mem-arrayi-less-generic-helper)))))

  (defthm x86$cp-update-nth-mem-arrayi-when-page-present
    ;; Useful for proving !mem$ci preserves x86$cp when no new page is
    ;; added.  This is a checkpoint during the proof of x86$cp-!mem$ci.
    (implies (forced-and (x86$cp x86$c)
                         (n08p v)
                         (integerp i)
                         (<= 0 i)
                         (< i *mem-size-in-bytes*)
                         (not (equal (nth (logtail *2^x-byte-pseudo-page* i)
                                          (nth *mem-tablei* x86$c))
                                     1)))
             (x86$cp (update-nth
                      *mem-arrayi*
                      (update-nth
                       (logior (loghead *2^x-byte-pseudo-page* i)
                               (ash
                                (logtail 1
                                         (nth (logtail *2^x-byte-pseudo-page* i)
                                              (nth *mem-tablei* x86$c)))
                                *2^x-byte-pseudo-page*))
                       v
                       (nth *mem-arrayi* x86$c))
                      x86$c)))
    :hints (("Goal" :in-theory (e/d (x86$cp good-memp) ()))))

  (defthm expected-mem-array-next-addr-update-nth-mem-tablei
    (implies (forced-and (equal (nth index (nth *mem-tablei* x86$c))
                                1)
                         (natp index)
                         (natp lower)
                         (natp upper)
                         (<= upper *mem-table-size*)
                         (not (equal any-value 1))
                         (equal mem-table (nth *mem-tablei* x86$c)))
             (equal (expected-mem-array-next-addr
                     lower upper
                     (update-nth *mem-tablei*
                                 (update-nth index any-value mem-table)
                                 x86$c))
                    (if (and (<= lower index)
                             (< index upper))
                        (+ 1 (expected-mem-array-next-addr
                              lower upper
                              x86$c))
                      (expected-mem-array-next-addr
                       lower upper
                       x86$c))))
    :hints (("Goal" :in-theory (enable expected-mem-array-next-addr))))

  (defthm |address < len(mem-array) when page is absent|
    (implies (and (equal (nth (logtail *2^x-byte-pseudo-page* i)
                              (nth *mem-tablei* x86$c))
                         1)
                  (unsigned-byte-p *physical-address-size* i)
                  (not (equal (ash (nth *mem-array-next-addr* x86$c)
                                   *2^x-byte-pseudo-page*)
                              (len (nth *mem-arrayi* x86$c))))
                  (x86$cp x86$c))
             (< (logior
                 (loghead *2^x-byte-pseudo-page* i)
                 (ash (nth *mem-array-next-addr* x86$c)
                      *2^x-byte-pseudo-page*))
                (len (nth *mem-arrayi* x86$c))))
    :hints (("Goal" :in-theory (e/d (x86$cp x86$cp-pre good-memp
                                            ash-less-than-constant)
                                    ()))))

  (defthm ash-monotone
    (implies (and (<= a b)
                  (integerp a)
                  (<= 0 a)
                  (integerp x)
                  (<= 0 x)
                  (integerp b)
                  (<= 0 b))
             (<= (ash a x) (ash b x)))
    :hints (("Goal" :in-theory (e/d (ash floor ifix) ()))))


  (defruledl x86$cp-pre-!mem$ci-new-page-no-resize-helper
    (implies (and (x86$cp x86$c)
                  (unsigned-byte-p *physical-address-size* i)
                  (n08p v)
                  (equal (nth (logtail *2^x-byte-pseudo-page* i)
                              (nth *mem-tablei* x86$c))
                         1)
                  (not (equal (ash (nth *mem-array-next-addr* x86$c)
                                   *2^x-byte-pseudo-page*)
                              (len (nth *mem-arrayi* x86$c)))))
             (x86$cp-pre
              (update-nth *mem-tablei*
                          (update-nth (logtail *2^x-byte-pseudo-page* i)
                                      (ash (nth *mem-array-next-addr* x86$c) 1)
                                      (nth *mem-tablei* x86$c))
                          (update-nth *mem-array-next-addr*
                                      (+ 1 (nth *mem-array-next-addr* x86$c))
                                      x86$c))))
    :hints (("Goal" :in-theory (e/d (x86$cp-pre x86$cp good-memp ash-less-than-constant)
                                    ()))))

  (local
   (encapsulate
    ()

    ;; Proof of good-mem-table-no-dupsp-logic-update-nth --- updating
    ;; mem-table appropriately preserves good-mem-table-no-dupsp-logic.

    ;; The following two books have lemmas about member and revappend.
    (local (include-book "std/lists/sets" :dir :system))
    (local (include-book "std/lists/revappend" :dir :system))

    (defthm member-merge-<-into->
      (iff (member a (merge-<-into-> x y z))
           (or (member a x)
               (member a y)
               (member a z))))

    (defthm member-merge->-into-<
      (iff (member a (merge->-into-< x y z))
           (or (member a x)
               (member a y)
               (member a z))))

    (local (in-theory (e/d (revappend) (acl2::revappend-removal))))

    (defthm no-duplicatesp-sorted-revappend-2
      (implies (not (no-duplicatesp-sorted y))
               (not (no-duplicatesp-sorted (revappend x y)))))

    (defthm no-duplicatesp-sorted-revappend-1
      (implies (not (no-duplicatesp-sorted x))
               (not (no-duplicatesp-sorted (revappend x y)))))

    (defthm no-duplicatesp-sorted-merge-<-into->-3
      (implies (not (no-duplicatesp-sorted z))
               (not (no-duplicatesp-sorted (merge-<-into-> x y z)))))

    (defthm no-duplicatesp-sorted-merge-<-into->-1
      (implies (not (no-duplicatesp-sorted x))
               (not (no-duplicatesp-sorted (merge-<-into-> x y z)))))

    (defthm no-duplicatesp-sorted-merge-<-into->-2
      (implies (not (no-duplicatesp-sorted y))
               (not (no-duplicatesp-sorted (merge-<-into-> x y z)))))

    (defthm no-duplicatesp-sorted-merge->-into-<-3
      (implies (not (no-duplicatesp-sorted z))
               (not (no-duplicatesp-sorted (merge->-into-< x y z)))))

    (defthm no-duplicatesp-sorted-merge->-into-<-1
      (implies (not (no-duplicatesp-sorted x))
               (not (no-duplicatesp-sorted (merge->-into-< x y z)))))

    (defthm no-duplicatesp-sorted-merge->-into-<-2
      (implies (not (no-duplicatesp-sorted y))
               (not (no-duplicatesp-sorted (merge->-into-< x y z)))))

    (defun all-< (lst x)
      (cond ((endp lst) t)
            ((< (car lst) x)
             (all-< (cdr lst) x))
            (t nil)))

    (defthm member-implies-not-all-<
      (implies (and (not (< b a))
                    (member b y))
               (not (all-< y a))))

    (defthm all-<-revappend
      (equal (all-< (revappend x y) a)
             (and (all-< x a)
                  (all-< y a))))

    (defthm all-<-merge-<-into->
      (equal (all-< (merge-<-into-> x y z) a)
             (and (all-< x a)
                  (all-< y a)
                  (all-< z a))))

    (defthm all-<-merge->-into-<
      (equal (all-< (merge->-into-< x y z) a)
             (and (all-< x a)
                  (all-< y a)
                  (all-< z a))))

    ;; Start proof of all-<-mem-table-entries-logic-next-addr

    (defthm all-<-mem-table-entries-logic-next-addr
      (implies (and (good-mem-table-entriesp-logic lower upper next-addr mem-table)
                    (natp lower))
               (all-< (mem-table-entries-logic lower upper mem-table parity)
                      next-addr))
      :hints
      (("Goal" :expand
        ((good-mem-table-entriesp-logic lower (+ 1 lower)
                                        next-addr mem-table)
         (good-mem-table-entriesp-logic (+ 1 lower)
                                        (+ 1 lower)
                                        next-addr mem-table)
         (good-mem-table-entriesp-logic lower lower next-addr mem-table)))))

    (defthm merge-<-into->-append-1
      (implies (and (all-< x a)
                    (all-< y a))
               (equal (merge-<-into-> (append x (list a)) y z)
                      (cons a (merge-<-into-> x y z)))))

    (defthm merge-<-into->-append-2
      (implies (and (all-< x a)
                    (all-< y a))
               (equal (merge-<-into-> x (append y (list a)) z)
                      (cons a (merge-<-into-> x y z)))))

    (defthm merge->-into-<-append-last
      (equal (merge->-into-< x y (append z1 z2))
             (append (merge->-into-< x y z1)
                     z2))
      :rule-classes nil)

    (defthm merge->-into-<-append-1
      (implies (and (all-< x a)
                    (all-< y a))
               (equal (merge->-into-< (cons a x) y nil)
                      (append (merge->-into-< x y nil)
                              (list a))))
      :hints (("Goal" :use ((:instance merge->-into-<-append-last
                                       (x x)
                                       (y y)
                                       (z1 nil)
                                       (z2 (list a))))
               :expand ((merge->-into-< (cons a x) y nil)))))

    (defthm merge->-into-<-append-2
      (implies (and (all-< x a)
                    (all-< y a))
               (equal (merge->-into-< x (cons a y) nil)
                      (append (merge->-into-< x y nil)
                              (list a))))
      :hints (("Goal" :use ((:instance merge->-into-<-append-last
                                       (x x)
                                       (y y)
                                       (z1 nil)
                                       (z2 (list a))))
               :expand ((merge->-into-< x (cons a y) nil)))))

    (defthm mem-table-entries-logic-update-nth-helper-1
      (implies
       (and (integerp upper)
            (<= 0 upper)
            (integerp index)
            (<= 0 index)
            (< index (len mem-table))
            (or (< upper index) (< index lower)))
       (equal (mem-table-entries-logic lower
                                       upper (update-nth index x mem-table)
                                       parity)
              (mem-table-entries-logic lower upper mem-table parity))))

    (local (in-theory (e/d* (mem-table-entries-logic-update-nth-helper-2
                             mem-table-entries-logic-update-nth-helper-3)
                            ())))

    (defthm mem-table-entries-logic-update-nth
      (implies
       (and (natp next-addr)
            (natp lower)
            (natp upper)
            (natp index)
            (mem-tablep mem-table)
            (equal (nth index mem-table) 1)
            (booleanp parity)
            (all-< (mem-table-entries-logic lower upper mem-table parity)
                   next-addr))
       (equal
        (mem-table-entries-logic lower upper
                                 (update-nth index (ash next-addr 1)
                                             mem-table)
                                 parity)
        (if (and (<= lower index) (<= index upper))
            (if parity
                (append (mem-table-entries-logic lower upper mem-table parity)
                        (list next-addr))
              (cons next-addr
                    (mem-table-entries-logic lower upper mem-table parity)))
          (mem-table-entries-logic lower upper mem-table parity)))))

    (defthm good-mem-table-no-dupsp-logic-update-nth-lemma-0-helper-1
      (implies (and (no-duplicatesp-sorted x)
                    (natp y)
                    (all-< x y))
               (no-duplicatesp-sorted (cons y x))))

    (defthm good-mem-table-no-dupsp-logic-update-nth-lemma-0-helper-2
      (implies (and (no-duplicatesp-sorted x)
                    (natp y)
                    (all-< x y))
               (no-duplicatesp-sorted (append x (list y)))))

    (local (in-theory (disable mem-table-entries-logic)))

    (defthm good-mem-table-no-dupsp-logic-update-nth-lemma-0
      (implies (and (natp lower)
                    (natp upper)
                    (natp index)
                    (mem-tablep mem-table)
                    (natp next-addr)
                    (booleanp parity)
                    (equal (nth index mem-table) 1)
                    (no-duplicatesp-sorted
                     (mem-table-entries-logic lower upper mem-table parity))
                    (all-< (mem-table-entries-logic lower upper mem-table parity)
                           next-addr))
               (no-duplicatesp-sorted
                (mem-table-entries-logic lower upper
                                         (update-nth index (ash next-addr 1)
                                                     mem-table)
                                         parity))))

    (defthm good-mem-table-no-dupsp-logic-update-nth-lemma
      (implies
       (and (natp lower)
            (natp upper)
            (natp index)
            (mem-tablep mem-table)
            (natp next-addr)
            (booleanp parity)
            (equal (nth index mem-table) 1)
            (no-duplicatesp-sorted
             (mem-table-entries-logic lower upper mem-table parity))
            (good-mem-table-entriesp-logic lower upper next-addr mem-table))
       (no-duplicatesp-sorted
        (mem-table-entries-logic lower upper
                                 (update-nth index (ash next-addr 1)
                                             mem-table)
                                 parity))))

    (defthm good-mem-table-no-dupsp-logic-update-nth
      (implies (and (natp lower)
                    (natp upper)
                    (natp index)
                    (mem-tablep mem-table)
                    (natp next-addr)
                    (equal (nth index mem-table) 1)
                    (good-mem-table-no-dupsp-logic lower upper mem-table)
                    (good-mem-table-entriesp-logic lower upper next-addr mem-table))
               (good-mem-table-no-dupsp-logic
                lower upper (update-nth index (ash next-addr 1) mem-table)))
      :hints
      (("Goal" :in-theory
        (e/d (good-mem-table-no-dupsp-logic good-mem-table-entriesp-logic)
             ()))))

    )) ;; End of encapsulate

  (defruledl dumb-x86$cp-!mem$ci-new-page-no-resize-helper
    ;; Just a dumb checkpoint from the proof
    ;; x86$cp-!mem$ci-new-page-no-resize --- I'm proving this
    ;; separately to avoid giving tedious subgoal hints.
    (implies
     (and
      (not (good-mem-table-no-dupsp-logic
            0 *mem-table-size-1*
            (update-nth (logtail *2^x-byte-pseudo-page* i)
                        (ash (nth *mem-array-next-addr* x86$c)
                             1)
                        (nth *mem-tablei* x86$c))))
      (x86$cp-pre x86$c)
      (good-mem-table-entriesp-logic 0 *mem-table-size-1*
                                     (nth *mem-array-next-addr* x86$c)
                                     (nth *mem-tablei* x86$c))
      (good-mem-table-no-dupsp-logic 0 *mem-table-size-1* (nth *mem-tablei* x86$c))
      (good-mem-arrayp-1-logic (ash (nth *mem-array-next-addr* x86$c)
                                    *2^x-byte-pseudo-page*)
                               (len (nth *mem-arrayi* x86$c))
                               (nth *mem-arrayi* x86$c))
      (unsigned-byte-p *physical-address-size* i)
      (n08p v)
      (equal (nth (logtail *2^x-byte-pseudo-page* i)
                  (nth *mem-tablei* x86$c)) 1))
     (equal (ash (nth *mem-array-next-addr* x86$c)
                 *2^x-byte-pseudo-page*)
            (len (nth *mem-arrayi* x86$c))))
    :hints (("Goal" :in-theory (e/d (x86$cp-pre)
                                    (good-mem-table-no-dupsp-logic-update-nth))
             :use ((:instance good-mem-table-no-dupsp-logic-update-nth
                              (lower 0)
                              (upper *mem-table-size-1*)
                              (index (logtail *2^x-byte-pseudo-page* i))
                              (mem-table (nth *mem-tablei* x86$c))
                              (next-addr (nth *mem-array-next-addr* x86$c)))))))


  (defrulel x86$cp-!mem$ci-new-page-no-resize
    ;; Basically, needs x86$cp-pre-!mem$ci-new-page-no-resize-helper and
    ;; good-mem-table-no-dupsp-logic-update-nth.  This is a checkpoint
    ;; during the proof of x86$cp-!mem$ci.
    (implies (and (x86$cp x86$c)
                  (unsigned-byte-p *physical-address-size* i)
                  (n08p v)
                  (equal (nth (logtail *2^x-byte-pseudo-page* i)
                              (nth *mem-tablei* x86$c))
                         1)
                  (not (equal (ash (nth *mem-array-next-addr* x86$c)
                                   *2^x-byte-pseudo-page*)
                              (len (nth *mem-arrayi* x86$c)))))
             (x86$cp
              (update-nth
               *mem-arrayi*
               (update-nth (logior
                            (loghead *2^x-byte-pseudo-page* i)
                            (ash (nth *mem-array-next-addr* x86$c)
                                 *2^x-byte-pseudo-page*))
                           v (nth *mem-arrayi* x86$c))
               (update-nth *mem-tablei*
                           (update-nth (logtail *2^x-byte-pseudo-page* i)
                                       (ash (nth *mem-array-next-addr* x86$c) 1)
                                       (nth *mem-tablei* x86$c))
                           (update-nth *mem-array-next-addr*
                                       (+ 1 (nth *mem-array-next-addr* x86$c))
                                       x86$c)))))
    :hints (("Goal"
             :in-theory (e/d (x86$cp
                              good-memp)
                             (x86$cp-update-nth-mem-arrayi-less-generic
                              good-mem-table-no-dupsp-logic-update-nth))
             :use ((:instance x86$cp-update-nth-mem-arrayi-less-generic
                              (addr (nth *mem-array-next-addr* x86$c))
                              (x86$c (update-nth
                                      *mem-tablei*
                                      (update-nth (logtail *2^x-byte-pseudo-page* i)
                                                  (ash (nth *mem-array-next-addr* x86$c) 1)
                                                  (nth *mem-tablei* x86$c))
                                      (update-nth *mem-array-next-addr*
                                                  (+ 1 (nth *mem-array-next-addr* x86$c))
                                                  x86$c))))
                   (:instance
                    x86$cp-pre-!mem$ci-new-page-no-resize-helper)
                   (:instance dumb-x86$cp-!mem$ci-new-page-no-resize-helper)))))


  (defrulel mem-arrayp-resize-list
    (implies (and (mem-arrayp lst)
                  (unsigned-byte-p 8 default-value))
             (mem-arrayp (resize-list lst new-len default-value))))

  (local
   (defun nth-resize-list-induction (i lst n default-value)
     (declare (ignorable i lst n default-value))
     (if (posp n)
         (nth-resize-list-induction (1- i)
                                    (if (atom lst) lst (cdr lst))
                                    (1- n)
                                    default-value)
       nil)))

  (defrulel nth-resize-list
    (implies (and (natp i)
                  (natp n)
                  (<= (len lst) n)
                  (< i n))
             (equal (nth i (resize-list lst n default))
                    (if (< i (len lst))
                        (nth i lst)
                      default)))
    :hints (("Goal" :in-theory (enable resize-list nth)
             :induct (nth-resize-list-induction i lst n default-value))))

  (defrulel good-mem-arrayp-1-logic-resize-list
    (implies (and (natp next-addr)
                  (natp new-len)
                  (<= (len mem-array) new-len)
                  (good-mem-arrayp-1-logic next-addr
                                           (len mem-array)
                                           mem-array))
             (good-mem-arrayp-1-logic next-addr
                                      new-len
                                      (resize-list mem-array new-len 0)))
    ;; It's very unusual that the following works but :hints (("Goal" :induct t))
    ;; does not!
    :instructions ((then induct prove)))

  (defrulel x86$cp-pre-resize-mem-array
    (implies
     (and (x86$cp x86$c)
          (natp new-len)
          (equal (loghead *2^x-byte-pseudo-page* new-len) 0)
          (<= (len (nth *mem-arrayi* x86$c)) new-len)
          (<= new-len *mem-size-in-bytes*))
     (x86$cp-pre (update-nth *mem-arrayi*
                             (resize-list (nth *mem-arrayi* x86$c)
                                          new-len 0)
                             x86$c)))
    :hints (("Goal" :in-theory (enable x86$cp x86$cp-pre))))

  (defruledl x86$cp-!mem$ci-new-page-resize-pre
    (implies
     (and (x86$cp x86$c)
          (unsigned-byte-p *physical-address-size* i)
          (n08p v)
          (equal (nth (logtail *2^x-byte-pseudo-page* i)
                      (nth *mem-tablei* x86$c))
                 1)
          (natp new-len)
          (equal (loghead *2^x-byte-pseudo-page* new-len) 0)
          (< (len (nth *mem-arrayi* x86$c)) new-len)
          (<= new-len *mem-size-in-bytes*))
     (x86$cp
      (update-nth
       *mem-arrayi*
       (update-nth (logior (ash (nth *mem-array-next-addr* x86$c)
                                *2^x-byte-pseudo-page*)
                           (loghead *2^x-byte-pseudo-page* i))
                   v
                   (resize-list (nth *mem-arrayi* x86$c)
                                new-len 0))
       (update-nth *mem-tablei*
                   (update-nth (logtail *2^x-byte-pseudo-page* i)
                               (ash (nth *mem-array-next-addr* x86$c)
                                    1)
                               (nth *mem-tablei* x86$c))
                   (update-nth *mem-array-next-addr*
                               (+ 1 (nth *mem-array-next-addr* x86$c))
                               (update-nth *mem-arrayi*
                                           (resize-list (nth *mem-arrayi* x86$c)
                                                        new-len 0)
                                           x86$c))))))
    :hints
    (("Goal"
      :do-not-induct t
      :in-theory (e/d (x86$cp good-memp) ())
      :use ((:instance x86$cp-!mem$ci-new-page-no-resize
                       (x86$c (update-nth *mem-arrayi*
                                          (resize-list (nth *mem-arrayi* x86$c)
                                                       new-len 0)
                                          x86$c)))))))

  (encapsulate
   ()

   (defrulel |(loghead n x) = 0 ==> (loghead n (ash x 1)) = 0|
     (implies (and (natp n)
                   (natp m)
                   (equal (loghead n x) 0))
              (equal (loghead n (ash x 1)) 0))
     :hints
     (("Goal" :in-theory
       (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)))))

   (defrulel ash-and-*-2
     (implies (integerp x)
              (equal (* 2 x)
                     (ash x 1)))
     :hints (("Goal" :in-theory (e/d (ash floor ifix) ()))))

   (defthmd x86$cp-!mem$ci-new-page-resize-helper
     ;; For relieving the hyp (equal (loghead *2^x-byte-pseudo-page*
     ;; new-len) 0) of x86$cp-!mem$ci-new-page-resize-pre during the
     ;; proof of x86$cp-!mem$ci-new-page-resize.
     (implies (and (natp a)
                   (equal (loghead *2^x-byte-pseudo-page* a) 0))
              (equal (loghead *2^x-byte-pseudo-page* (* 2 a)) 0)))
   )

  (defruledl x86$cp-!mem$ci-new-page-resize-within-*mem-size-in-bytes*
    ;; This is a checkpoint during the proof of x86$cp-!mem$ci.
    (implies
     (and (x86$cp x86$c)
          (unsigned-byte-p *physical-address-size* i)
          (n08p v)
          (equal (nth (logtail *2^x-byte-pseudo-page* i) (nth *mem-tablei* x86$c)) 1)
          (<= (* 2 (len (nth *mem-arrayi* x86$c))) *mem-size-in-bytes*))
     (x86$cp
      (update-nth
       *mem-arrayi*
       (update-nth (logior (ash (nth *mem-array-next-addr* x86$c)
                                *2^x-byte-pseudo-page*)
                           (loghead *2^x-byte-pseudo-page* i))
                   v
                   (resize-list (nth *mem-arrayi* x86$c)
                                (* 2 (len (nth *mem-arrayi* x86$c))) 0))
       (update-nth *mem-tablei*
                   (update-nth (logtail *2^x-byte-pseudo-page* i)
                               (ash (nth *mem-array-next-addr* x86$c)
                                    1)
                               (nth *mem-tablei* x86$c))
                   (update-nth *mem-array-next-addr*
                               (+ 1 (nth *mem-array-next-addr* x86$c))
                               (update-nth *mem-arrayi*
                                           (resize-list
                                            (nth *mem-arrayi* x86$c)
                                            (* 2 (len (nth *mem-arrayi* x86$c))) 0)
                                           x86$c))))))
    :hints
    (("Goal"
      :do-not-induct t
      :in-theory (e/d (x86$cp good-memp) ())
      :use ((:instance x86$cp-!mem$ci-new-page-resize-pre
                       (new-len (* 2 (len (nth *mem-arrayi* x86$c)))))
            (:instance x86$cp-!mem$ci-new-page-resize-helper
                       (a (len (nth *mem-arrayi* x86$c))))))))

  (defruledl x86$cp-!mem$ci-new-page-resize-attempt-beyond-*mem-size-in-bytes*
    ;; This is a checkpoint during the proof of x86$cp-!mem$ci.
    (implies
     (and (x86$cp x86$c)
          (unsigned-byte-p *physical-address-size* i)
          (n08p v)
          (equal (nth (logtail *2^x-byte-pseudo-page* i)
                      (nth *mem-tablei* x86$c))
                 1)
          (equal (ash (nth *mem-array-next-addr* x86$c)
                      *2^x-byte-pseudo-page*)
                 (len (nth *mem-arrayi* x86$c)))
          (<= *mem-size-in-bytes*
              (* 2 (len (nth *mem-arrayi* x86$c)))))
     (x86$cp
      (update-nth
       *mem-arrayi*
       (update-nth (logior (loghead *2^x-byte-pseudo-page* i)
                           (len (nth *mem-arrayi* x86$c)))
                   v
                   (resize-list (nth *mem-arrayi* x86$c)
                                *mem-size-in-bytes* 0))
       (update-nth *mem-tablei*
                   (update-nth (logtail *2^x-byte-pseudo-page* i)
                               (ash (nth *mem-array-next-addr* x86$c)
                                    1)
                               (nth *mem-tablei* x86$c))
                   (update-nth *mem-array-next-addr*
                               (+ 1 (nth *mem-array-next-addr* x86$c))
                               (update-nth *mem-arrayi*
                                           (resize-list (nth *mem-arrayi* x86$c)
                                                        *mem-size-in-bytes* 0)
                                           x86$c))))))
    :hints (("Goal" :in-theory (e/d (ash-less-than-constant)
                                    (expected-mem-array-next-addr-bound-when-page-absent))
             :use ((:instance x86$cp-!mem$ci-new-page-resize-pre
                              (new-len *mem-size-in-bytes*))
                   (:instance
                    expected-mem-array-next-addr-bound-when-page-absent
                    ;; i was a free var in this thm.
                    (i (logtail *2^x-byte-pseudo-page* i)))))))

  (defthm x86$cp-!mem$ci
    (implies (forced-and (x86$cp x86$c)
                         (integerp i)
                         (<= 0 i)
                         (< i *mem-size-in-bytes*)
                         (n08p v))
             (x86$cp (!mem$ci i v x86$c)))
    :hints (("Goal" :in-theory (e/d (!mem$ci)
                                    (mem-array-next-addr-is-expected-mem-array-next-addr))
             :use ((:instance
                    x86$cp-!mem$ci-new-page-resize-within-*mem-size-in-bytes*)
                   (:instance
                    x86$cp-!mem$ci-new-page-resize-attempt-beyond-*mem-size-in-bytes*)))))


  ;; [Shilpi]:
  ;; Proof of mem-table-is-one-to-one --- this theorem will be used
  ;; to prove read-over-write theorems about mem$ci and !mem$ci, but
  ;; I've put this encapsulate in this section because this proof
  ;; requires some events local to this defsection.  Maybe I can
  ;; think about better organization some time in the future.


  (encapsulate

   ()

   ;; The following two books have lemmas about member and revappend.
   (local (include-book "std/lists/sets" :dir :system))
   (local (include-book "std/lists/revappend" :dir :system))

   (encapsulate
    ()

    (defrulel member-mem-table-entries-logic-lema-1
      (implies (and (syntaxp (equal i 'i))
                    (integerp i)
                    (natp lower)
                    (<= lower i)
                    (<= i (+ 1 lower))
                    (not (equal (logtail 1 (nth i mem-table))
                                (logtail 1 (nth lower (cdr mem-table))))))
               (equal (logtail 1 (nth i mem-table))
                      (logtail 1 (nth lower mem-table)))))

    (defrulel member-mem-table-entries-logic-lema-2
      (implies (and (equal (nth lower mem-table) 1)
                    (equal (nth lower (cdr mem-table)) 1)
                    (integerp i)
                    (natp lower)
                    (<= lower i)
                    (<= i (+ 1 lower)))
               (equal (nth i mem-table) 1)))

    (defrulel member-mem-table-entries-logic-lema-3
      (implies (and (syntaxp (equal i 'i))
                    (equal (nth lower (cdr mem-table)) 1)
                    (integerp i)
                    (natp lower)
                    (<= lower i)
                    (<= i (+ 1 lower))
                    (not (equal (nth i mem-table) 1)))
               (equal (logtail 1 (nth i mem-table))
                      (logtail 1 (nth lower mem-table)))))

    (defrulel member-mem-table-entries-logic-lemma-4
      (implies (and (syntaxp (equal i 'i))
                    (equal (nth lower mem-table) 1)
                    (integerp i)
                    (natp lower)
                    (<= lower i)
                    (<= i (+ 1 lower))
                    (not (equal (nth i mem-table) 1)))
               (equal (logtail 1 (nth i mem-table))
                      (logtail 1 (nth lower (cdr mem-table))))))

    (defthm member-mem-table-entries-logic
      (implies (and (natp i)
                    (natp lower)
                    (natp upper)
                    (<= lower i)
                    (<= i upper)
                    (not (equal (nth i mem-table) 1)))
               (member (logtail 1 (nth i mem-table))
                       (mem-table-entries-logic lower upper mem-table parity)))
      :hints (("Goal" :in-theory (enable mem-table-entries-logic)
               :induct (mem-table-entries-logic lower upper mem-table parity))))

    )

   (in-theory (e/d () (mem-table-entries-logic)))

   (local
    (defun sortedp (x parity)

      ;; A parity of true means that x should be increasing.

      (cond ((or (endp x) (endp (cdr x)))
             t)
            ((if parity
                 (<= (car x) (cadr x))
               (>= (car x) (cadr x)))
             (sortedp (cdr x) parity))
            (t nil))))

   (defrulel sortedp-revappend
     (iff (and (sortedp x (not parity))
               (sortedp y parity)
               (or (atom x)
                   (atom y)
                   (if parity
                       (<= (car x) (car y))
                     (>= (car x) (car y)))))
          (sortedp (revappend x y) parity))
     :rule-classes ((:rewrite
                     :corollary
                     (equal (sortedp (revappend x y) parity)
                            (and (sortedp x (not parity))
                                 (sortedp y parity)
                                 (or (atom x)
                                     (atom y)
                                     (if parity
                                         (<= (car x) (car y))
                                       (>= (car x) (car y)))))))))

   (defrulel sortedp-merge-<-into->
     (implies (and (sortedp x t)
                   (sortedp y t)
                   (sortedp z nil)
                   (or (atom z) (atom x) (>= (car x) (car z)))
                   (or (atom z) (atom y) (>= (car y) (car z))))
              (sortedp (merge-<-into-> x y z) nil))
     :hints (("Goal" :in-theory (enable merge-<-into->))))

   (defrulel sortedp-merge->-into-<
     (implies (and (sortedp x nil)
                   (sortedp y nil)
                   (sortedp z t)
                   (or (atom z) (atom x) (<= (car x) (car z)))
                   (or (atom z) (atom y) (<= (car y) (car z))))
              (sortedp (merge->-into-< x y z) t))
     :hints (("Goal" :in-theory (enable merge->-into-<))))

   (defrulel no-duplicatesp-sorted-revappend
     (equal (no-duplicatesp-sorted (revappend x y))
            (and (no-duplicatesp-sorted x)
                 (no-duplicatesp-sorted y)
                 (or (atom x)
                     (atom y)
                     (not (equal (car x) (car y))))))
     :hints (("Goal" :in-theory (enable no-duplicatesp-sorted acl2::rev))))

   (defrulel not-member-sortedp-t
     (implies (and (sortedp x t)
                   (< a (car x)))
              (not (member a x))))

   (defrulel member-sortedp-t
     (implies (and (sortedp x t)
                   (consp x)
                   (<= a (car x))
                   (rational-listp x))
              (iff (member a x)
                   (equal a (car x))))
     :hints (("Goal" :induct t)))

   (defrulel member-of-both-implies-not-no-duplicatesp-sorted-merge-<-into->
     (implies (and (rational-listp x)
                   (rational-listp y)
                   (member a x)
                   (member b y)
                   (equal a b)
                   (sortedp x t)
                   (sortedp y t))
              (not (no-duplicatesp-sorted (merge-<-into-> x y z))))
     :hints (("Goal"
              :in-theory (enable no-duplicatesp-sorted
                                 merge-<-into->)
              :induct (merge-<-into-> x y z)
              :expand ((merge-<-into-> x y z)
                       (sortedp x t)
                       (merge-<-into-> x
                                       (cdr y)
                                       (cons (car x) z))))))

   (defrulel not-member-sortedp-nil
     (implies (and (sortedp x nil)
                   (> a (car x)))
              (not (member a x))))

   (defrulel member-sortedp-nil
     (implies (and (sortedp x nil)
                   (consp x)
                   (>= a (car x))
                   (rational-listp x))
              (iff (member a x)
                   (equal a (car x))))
     :hints (("Goal" :induct t)))

   (defrulel member-of-both-implies-not-no-duplicatesp-sorted-merge->-into-<
     (implies (and (rational-listp x)
                   (rational-listp y)
                   (member a x)
                   (member b y)
                   (equal a b)
                   (sortedp x nil)
                   (sortedp y nil))
              (not (no-duplicatesp-sorted (merge->-into-< x y z))))
     :hints (("Goal"
              :in-theory (enable no-duplicatesp-sorted
                                 merge->-into-<)
              :induct (merge->-into-< x y z)
              :expand ((merge->-into-< x y z)
                       (sortedp x nil)
                       (merge->-into-< x
                                       (cdr y)
                                       (cons (car x) z))))))

   (defthm rational-listp-mem-table-entries-logic
     (implies (and (rational-listp mem-table)
                   (natp lower)
                   (<= lower upper)
                   (natp upper)
                   (< upper (len mem-table)))
              (rational-listp (mem-table-entries-logic lower upper mem-table parity)))
     :hints (("Goal" :in-theory (e/d (mem-table-entries-logic) ())
              :induct (mem-table-entries-logic lower upper mem-table parity))))


   (defrulel natp-nth-mem-table
     (implies (and (mem-tablep x)
                   (natp n)
                   (< n (len x)))
              (natp (nth n x)))
     :hints (("Goal" :in-theory (enable nth))))

   (defthm logtail-monotone-1
     (implies (and (natp a)
                   (natp b)
                   (<= a b))
              (<= (logtail x a) (logtail x b)))
     :hints
     (("Goal" :in-theory
       (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)))))

   (defthm logtail-monotone-2
     (implies (and (< (logtail x a) (logtail x b))
                   (natp a)
                   (natp b))
              (< a b))
     :hints
     (("Goal" :in-theory
       (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs))))
     :rule-classes :forward-chaining)

   (defrulel sortedp-mem-table-entries-logic
     (implies (and
               (rational-listp mem-table)
               (mem-tablep mem-table)
               (natp lower)
               (natp upper)
               (< upper (len mem-table))
               (booleanp parity))
              (sortedp (mem-table-entries-logic lower upper mem-table parity)
                       parity))
     :hints (("Goal" :in-theory (e/d (mem-table-entries-logic) ())
              :induct (mem-table-entries-logic lower upper mem-table
                                               parity))))

   (defruledl mem-table-is-one-to-one-lemma-helper-1
     (implies
      (and
       (implies
        (and (integerp lower)
             (<= 0 lower)
             (integerp upper)
             (<= 0 upper)
             (< (+ 1 lower) upper)
             (< (logtail 1 (+ lower upper)) j)
             (< i (+ 1 (logtail 1 (+ lower upper))))
             (integerp i)
             (<= 0 i)
             (integerp j)
             (<= 0 j)
             (<= lower i)
             (< i j)
             (<= j upper)
             (not (equal (nth i mem-table) 1))
             (equal (nth i mem-table)
                    (nth j mem-table)))
        (and
         (member-equal (logtail 1 (nth i mem-table))
                       (mem-table-entries-logic lower (logtail 1 (+ lower upper))
                                                mem-table t))
         (member-equal (ash (nth j mem-table) -1)
                       (mem-table-entries-logic (+ 1 (logtail 1 (+ lower upper)))
                                                upper mem-table t))))
       (integerp lower)
       (<= 0 lower)
       (integerp upper)
       (< (+ 1 lower) upper)
       (< (logtail 1 (+ lower upper)) j)
       (< i (+ 1 (logtail 1 (+ lower upper))))
       (mem-tablep mem-table)
       (integerp i)
       (integerp j)
       (<= lower i)
       (<= j upper)
       (< upper (len mem-table))
       (not (equal (nth i mem-table) 1))
       (equal (nth i mem-table)
              (nth j mem-table)))
      (not (no-duplicatesp-sorted
            (merge-<-into->
             (mem-table-entries-logic lower (logtail 1 (+ lower upper))
                                      mem-table t)
             (mem-table-entries-logic (+ 1 (logtail 1 (+ lower upper)))
                                      upper mem-table t)
             nil))))
     :instructions ((:dive 1) :s :top :prove))


   (defrulel mem-table-is-one-to-one-lemma-helper-2
     (implies
      (and (integerp lower)
           (<= 0 lower)
           (integerp upper)
           (< (+ 1 lower) upper)
           (< (logtail 1 (+ lower upper)) j)
           (< i (+ 1 (logtail 1 (+ lower upper))))
           (mem-tablep mem-table)
           (integerp i)
           (integerp j)
           (<= lower i)
           (<= j upper)
           (< upper (len mem-table))
           (not (equal (nth i mem-table) 1))
           (equal (nth i mem-table)
                  (nth j mem-table)))
      (not
       (no-duplicatesp-sorted
        (merge-<-into-> (mem-table-entries-logic lower (logtail 1 (+ lower upper))
                                                 mem-table t)
                        (mem-table-entries-logic (+ 1 (logtail 1 (+ lower upper)))
                                                 upper mem-table t)
                        nil))))
     :hints (("Goal" :use mem-table-is-one-to-one-lemma-helper-1)))


   (defrulel mem-table-is-one-to-one-lemma-helper-3
     (implies
      (and
       (implies
        (and (integerp lower)
             (<= 0 lower)
             (integerp upper)
             (<= 0 upper)
             (< (+ 1 lower) upper)
             (< (logtail 1 (+ lower upper)) j)
             (< i (+ 1 (logtail 1 (+ lower upper))))
             (integerp i)
             (<= 0 i)
             (integerp j)
             (<= 0 j)
             (<= lower i)
             (< i j)
             (<= j upper)
             (not (equal (nth i mem-table) 1))
             (equal (nth i mem-table)
                    (nth j mem-table)))
        (and
         (member-equal (logtail 1 (nth i mem-table))
                       (mem-table-entries-logic lower (logtail 1 (+ lower upper))
                                                mem-table nil))
         (member-equal (logtail 1 (nth j mem-table))
                       (mem-table-entries-logic (+ 1 (logtail 1 (+ lower upper)))
                                                upper mem-table nil))))
       (integerp lower)
       (<= 0 lower)
       (integerp upper)
       (< (+ 1 lower) upper)
       (< (logtail 1 (+ lower upper)) j)
       (< i (+ 1 (logtail 1 (+ lower upper))))
       (mem-tablep mem-table)
       (integerp i)
       (integerp j)
       (<= lower i)
       (<= j upper)
       (< upper (len mem-table))
       (not (equal (nth i mem-table) 1))
       (equal (nth i mem-table)
              (nth j mem-table)))
      (not (no-duplicatesp-sorted
            (merge->-into-<
             (mem-table-entries-logic lower (logtail 1 (+ lower upper))
                                      mem-table nil)
             (mem-table-entries-logic (+ 1 (logtail 1 (+ lower upper)))
                                      upper mem-table nil)
             nil))))
     :instructions ((:dive 1) :s :top :prove))

   (defthm mem-table-is-one-to-one-lemma-helper-4
     (implies
      (and (integerp lower)
           (<= 0 lower)
           (integerp upper)
           (< (+ 1 lower) upper)
           (< (logtail 1 (+ lower upper)) j)
           (< i (+ 1 (logtail 1 (+ lower upper))))
           (mem-tablep mem-table)
           (integerp i)
           (integerp j)
           (<= lower i)
           (<= j upper)
           (< upper (len mem-table))
           (not (equal (nth i mem-table) 1))
           (equal (nth i mem-table)
                  (nth j mem-table)))
      (not (no-duplicatesp-sorted
            (merge->-into-<
             (mem-table-entries-logic lower (logtail 1 (+ lower upper))
                                      mem-table nil)
             (mem-table-entries-logic (+ 1 (logtail 1 (+ lower upper)))
                                      upper mem-table nil)
             nil))))
     :hints (("Goal" :use mem-table-is-one-to-one-lemma-helper-3)))

   (defrulel mem-table-is-one-to-one-lemma
     (implies (and (rational-listp mem-table)
                   (mem-tablep mem-table)
                   (natp lower)
                   (natp upper)
                   (natp i)
                   (natp j)
                   (<= lower i)
                   (< i j)
                   (<= j upper)
                   (< upper (len mem-table))
                   (booleanp parity)
                   (not (equal (nth i mem-table) 1))
                   (equal (nth i mem-table)
                          (nth j mem-table)))
              (not (no-duplicatesp-sorted
                    (mem-table-entries-logic lower upper mem-table parity))))
     :hints
     (("Goal"
       :in-theory (e/d (mem-table-entries-logic)
                       ())
       :induct (mem-table-entries-logic lower upper mem-table parity)
       :restrict
       ((member-of-both-implies-not-no-duplicatesp-sorted-merge->-into-<
         ((a (logtail 1 (nth i mem-table)))
          (b (logtail 1 (nth j mem-table)))))
        (member-of-both-implies-not-no-duplicatesp-sorted-merge-<-into->
         ((a (logtail 1 (nth i mem-table)))
          (b (logtail 1 (nth j mem-table))))))))
     :rule-classes nil)


   (defrulel mem-table-is-one-to-one-helper
     (implies (and (x86$cp x86$c)
                   (integerp i)
                   (<= 0 i)
                   (<= i *mem-table-size-1*)
                   (integerp j)
                   (<= 0 j)
                   (<= j *mem-table-size-1*)
                   (<= i j)
                   (not (equal (mem-tablei i x86$c)
                               1)))
              (equal (equal (mem-tablei i x86$c)
                            (mem-tablei j x86$c))
                     (equal i j)))
     :hints (("Goal"
              :in-theory (enable x86$cp
                                 x86$cp-pre
                                 good-memp
                                 good-mem-table-no-dupsp-logic
                                 mem-tablei
                                 mem-table-length)
              :use ((:instance mem-table-is-one-to-one-lemma
                               (lower 0)
                               (upper *mem-table-size-1*)
                               (mem-table (nth *mem-tablei* x86$c))
                               (parity t))
                    (:instance mem-table-is-one-to-one-lemma
                               (lower 0)
                               (upper *mem-table-size-1*)
                               (i j) (j i)
                               (mem-table (nth *mem-tablei* x86$c))
                               (parity t)))))
     :rule-classes nil)

   (defthm mem-table-is-one-to-one
     (implies (and (x86$cp x86$c)
                   (integerp i)
                   (<= 0 i)
                   (<= i *mem-table-size-1*)
                   (integerp j)
                   (<= 0 j)
                   (<= j *mem-table-size-1*)
                   (not (equal (nth i (nth *mem-tablei* x86$c))
                               1)))
              (equal (equal (nth i (nth *mem-tablei* x86$c))
                            (nth j (nth *mem-tablei* x86$c)))
                     (equal i j)))
     :hints (("Goal" :use ((:instance mem-table-is-one-to-one-helper
                                      (i i)
                                      (j j))
                           (:instance mem-table-is-one-to-one-helper
                                      (i j)
                                      (j i))))))

   )

  ;; [Shilpi]: Separate out the proof of read-write into its own
  ;; section.

  ;; Concrete memory read-write theorem

  (defthm read-write-same
    (implies (forced-and (x86$cp x86$c)
                         (unsigned-byte-p *physical-address-size* i)
                         (unsigned-byte-p *physical-address-size* j)
                         (n08p v)
                         (equal i j))
             (equal (mem$ci j (!mem$ci i v x86$c)) v))
    :hints (("Goal"
             :in-theory (e/d (mem$ci !mem$ci) ())))
    :rule-classes nil)

  (defruledl lsb-of-mem-table
    (implies (and (x86$cp x86$c)
                  (unsigned-byte-p *mem-table-size-bits* i)
                  (not (equal (nth i (nth *mem-tablei* x86$c)) 1)))
             (equal (loghead 1 (nth i (nth *mem-tablei* x86$c))) 0))
    :hints (("Goal" :in-theory (e/d (x86$cp good-memp ash-less-than-constant)
                                    ()))))

  (defrulel mem-table-is-one-to-one-logtail
    (implies (and (x86$cp x86$c)
                  (unsigned-byte-p *mem-table-size-bits* i)
                  (unsigned-byte-p *mem-table-size-bits* j)
                  (not (equal (nth i (nth *mem-tablei* x86$c)) 1))
                  (not (equal (nth j (nth *mem-tablei* x86$c)) 1)))
             (equal (equal (logtail 1 (nth i (nth *mem-tablei* x86$c)))
                           (logtail 1 (nth j (nth *mem-tablei* x86$c))))
                    (equal i j)))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d () (mem-table-is-one-to-one))
             :use ((:instance lsb-of-mem-table)
                   (:instance lsb-of-mem-table (i j))
                   (:instance mem-table-is-one-to-one)))))

  (defrulel read-write-different-helper-lemma-1
    ;; This is a checkpoint during the proof of read-write-different.
    (implies
     (and (x86$cp x86$c)
          (unsigned-byte-p *physical-address-size* i)
          (unsigned-byte-p *physical-address-size* j)
          (not (equal (nth (logtail *2^x-byte-pseudo-page* i)
                           (nth *mem-tablei* x86$c))
                      1))
          (not (equal (nth (logtail *2^x-byte-pseudo-page* j)
                           (nth *mem-tablei* x86$c))
                      1))
          (not (equal i j)))
     (not (equal (logior (loghead *2^x-byte-pseudo-page* j)
                         (ash
                          (logtail 1 (nth (logtail *2^x-byte-pseudo-page* j)
                                          (nth *mem-tablei* x86$c)))
                          *2^x-byte-pseudo-page*))
                 (logior (loghead *2^x-byte-pseudo-page* i)
                         (ash
                          (logtail 1 (nth (logtail *2^x-byte-pseudo-page* i)
                                          (nth *mem-tablei* x86$c)))
                          *2^x-byte-pseudo-page*)))))
    :hints
    (("Goal"
      :use ((:instance breaking-logior-apart-1
                       (low25-i (logtail 1
                                         (nth (logtail *2^x-byte-pseudo-page* i)
                                              (nth *mem-tablei* x86$c))))
                       (low25-j (logtail 1
                                         (nth (logtail *2^x-byte-pseudo-page* j)
                                              (nth *mem-tablei* x86$c))))
                       (i i)
                       (j j))
            (:instance breaking-logior-apart-2
                       (low25-i (logtail 1
                                         (nth (logtail *2^x-byte-pseudo-page* i)
                                              (nth *mem-tablei* x86$c))))
                       (low25-j (logtail 1
                                         (nth (logtail *2^x-byte-pseudo-page* j)
                                              (nth *mem-tablei* x86$c))))
                       (i i)
                       (j j))))))

  (defrulel read-write-different-helper-lemma-2
    (implies (and (x86$cp x86$c)
                  (unsigned-byte-p *physical-address-size* i)
                  (unsigned-byte-p *physical-address-size* j)
                  (equal (logtail *2^x-byte-pseudo-page* j)
                         (logtail *2^x-byte-pseudo-page* i))
                  (not (equal (loghead *2^x-byte-pseudo-page* i)
                              (loghead *2^x-byte-pseudo-page* j)))

                  (not (equal (ash (nth *mem-array-next-addr* x86$c)
                                   *2^x-byte-pseudo-page*)
                              (len (nth *mem-arrayi* x86$c))))
                  (equal (nth (logtail *2^x-byte-pseudo-page* i)
                              (nth *mem-tablei* x86$c))
                         1))
             (not (equal (logior (loghead *2^x-byte-pseudo-page* j)
                                 (ash (nth *mem-array-next-addr* x86$c)
                                      *2^x-byte-pseudo-page*))
                         (logior (loghead *2^x-byte-pseudo-page* i)
                                 (ash (nth *mem-array-next-addr* x86$c)
                                      *2^x-byte-pseudo-page*)))))
    :hints (("Goal"
             :in-theory (e/d (x86$cp x86$cp-pre)
                             (expected-mem-array-next-addr-bound-when-page-absent
                              mem-array-next-addr-is-expected-mem-array-next-addr))
             :use
             ((:instance expected-mem-array-next-addr-bound-when-page-absent
                         (i (logtail *2^x-byte-pseudo-page* i)))
              (:instance mem-array-next-addr-is-expected-mem-array-next-addr)
              (:instance breaking-logior-apart-2
                         (low25-i (nth *mem-array-next-addr* x86$c))
                         (low25-j (nth *mem-array-next-addr* x86$c))
                         (i i)
                         (j j))))))

  (defrulel read-write-different-helper-lemma-3
    (implies (and (x86$cp x86$c)
                  (unsigned-byte-p *physical-address-size* i)
                  (unsigned-byte-p *physical-address-size* j)
                  (equal (nth (logtail *2^x-byte-pseudo-page* i)
                              (nth *mem-tablei* x86$c))
                         1)
                  (equal (ash (nth *mem-array-next-addr* x86$c)
                              *2^x-byte-pseudo-page*)
                         (len (nth *mem-arrayi* x86$c)))

                  (equal (logtail *2^x-byte-pseudo-page* j)
                         (logtail *2^x-byte-pseudo-page* i))
                  (not (equal i j)))
             (not (equal (logior (loghead *2^x-byte-pseudo-page* j)
                                 (len (nth *mem-arrayi* x86$c)))
                         (logior (loghead *2^x-byte-pseudo-page* i)
                                 (len (nth *mem-arrayi* x86$c))))))
    :hints (("Goal"
             :in-theory (e/d (x86$cp x86$cp-pre)
                             (expected-mem-array-next-addr-bound-when-page-absent
                              mem-array-next-addr-is-expected-mem-array-next-addr))
             :use
             ((:instance expected-mem-array-next-addr-bound-when-page-absent
                         (i (logtail *2^x-byte-pseudo-page* i)))
              (:instance mem-array-next-addr-is-expected-mem-array-next-addr)
              (:instance breaking-logior-apart-2
                         (low25-i (nth *mem-array-next-addr* x86$c))
                         (low25-j (nth *mem-array-next-addr* x86$c))
                         (i i)
                         (j j))))))

  (defrulel good-mem-arrayp-thm-1-helper
    (implies (and (good-mem-arrayp-1-logic start len mem-array)
                  (integerp start)
                  (<= 0 start)
                  (integerp len)
                  (<= 0 len)
                  (<= start len)
                  (integerp addr)
                  (<= 0 addr)
                  (<= start addr)
                  (< addr len))
             (equal (nth addr mem-array) 0)))

  ;; (defthm good-mem-arrayp-thm-1
  ;;   (implies (and (x86$cp x86$c)
  ;;                 (integerp addr)
  ;;                 (<= 0 addr)
  ;;                 (<= (nth *mem-array-next-addr* x86$c) addr)
  ;;                 (< (ash addr *2^x-byte-pseudo-page*) (len (nth *mem-arrayi* x86$c))))
  ;;            (equal (nth (ash addr *2^x-byte-pseudo-page*)
  ;;                        (nth *mem-arrayi* x86$c))
  ;;                   0))
  ;;   :hints (("Goal" :in-theory (e/d (x86$cp good-memp good-mem-arrayp)
  ;;                                   (force (force))))))

  (defrulel good-mem-arrayp-thm-2
    (implies (and (x86$cp x86$c)

                  ;; [Shilpi]: Eliminate the following two hypotheses
                  ;; so that this lemma can be used to prove away a
                  ;; checkpoint of read-write-different.
                  (< (logior (loghead *2^x-byte-pseudo-page* j)
                             (ash (nth *mem-array-next-addr* x86$c)
                                  *2^x-byte-pseudo-page*))
                     (len (nth *mem-arrayi* x86$c)))

                  (<= (ash (nth *mem-array-next-addr* x86$c) *2^x-byte-pseudo-page*)
                      (logior (loghead *2^x-byte-pseudo-page* j)
                              (ash (nth *mem-array-next-addr* x86$c)
                                   *2^x-byte-pseudo-page*)))

                  )
             (equal (nth (logior (loghead *2^x-byte-pseudo-page* j)
                                 (ash (nth *mem-array-next-addr* x86$c)
                                      *2^x-byte-pseudo-page*))
                         (nth *mem-arrayi* x86$c))
                    0))
    :hints (("Goal" :in-theory (e/d (x86$cp good-memp)
                                    (good-mem-arrayp-thm-1-helper))
             :use ((:instance good-mem-arrayp-thm-1-helper
                              (start (ash (nth *mem-array-next-addr* x86$c) *2^x-byte-pseudo-page*))
                              (len (len (nth *mem-arrayi* x86$c)))
                              (mem-array (nth *mem-arrayi* x86$c))
                              (addr (logior (loghead *2^x-byte-pseudo-page* j)
                                            (ash (nth *mem-array-next-addr* x86$c)
                                                 *2^x-byte-pseudo-page*)))))
             )))


  ;; (defthm good-mem-arrayp-thm-2
  ;;   (implies (and (x86$cp x86$c)
  ;;                 (integerp addr)
  ;;                 (<= 0 addr)
  ;;                 (integerp i)
  ;;                 (<= 0 i)

  ;;                 (< (logior (loghead *2^x-byte-pseudo-page* j)
  ;;                            (ash (nth *mem-array-next-addr* x86$c)
  ;;                                 *2^x-byte-pseudo-page*))
  ;;                    (len (nth *mem-arrayi* x86$c)))

  ;;                 (< (ash (nth *mem-array-next-addr* x86$c) *2^x-byte-pseudo-page*)
  ;;                    (logior (loghead *2^x-byte-pseudo-page* j)
  ;;                            (ash (nth *mem-array-next-addr* x86$c)
  ;;                                 *2^x-byte-pseudo-page*)))

  ;;                 )
  ;;            (equal (nth (logior (loghead *2^x-byte-pseudo-page* j)
  ;;                                (ash (nth *mem-array-next-addr* x86$c)
  ;;                                     *2^x-byte-pseudo-page*))
  ;;                        (nth *mem-arrayi* x86$c))
  ;;                   0))
  ;;   :hints (("Goal" :in-theory (e/d (x86$cp good-memp)
  ;;                                   (good-mem-arrayp-thm-1-helper))
  ;;            :use ((:instance good-mem-arrayp-thm-1-helper
  ;;                             (start (ash (nth *mem-array-next-addr* x86$c) *2^x-byte-pseudo-page*))
  ;;                             (len (len (nth *mem-arrayi* x86$c)))
  ;;                             (mem-array (nth *mem-arrayi* x86$c))
  ;;                             (addr (logior (loghead *2^x-byte-pseudo-page* j)
  ;;                                           (ash (nth *mem-array-next-addr* x86$c)
  ;;                                                *2^x-byte-pseudo-page*)))))
  ;;            )))

  (defthm equal-logior-logior
    (implies (and (natp x1) (natp x2) (natp y1) (natp y2))
             (iff (equal (logior (loghead *2^x-byte-pseudo-page* x1)
                                 (ash y1 *2^x-byte-pseudo-page*))
                         (logior (loghead *2^x-byte-pseudo-page* x2)
                                 (ash y2 *2^x-byte-pseudo-page*)))
                  (and (equal (loghead *2^x-byte-pseudo-page* x1)
                              (loghead *2^x-byte-pseudo-page* x2))
                       (equal (ash y1 *2^x-byte-pseudo-page*)
                              (ash y2 *2^x-byte-pseudo-page*)))))
    :hints (("Goal"
             :in-theory (disable bitops::loghead-of-logior bitops::logtail-of-logior)
             :use ((:instance bitops::loghead-of-logior
                              (a *2^x-byte-pseudo-page*)
                              (x (loghead *2^x-byte-pseudo-page* x1))
                              (y (ash y1 *2^x-byte-pseudo-page*)))
                   (:instance bitops::loghead-of-logior
                              (a *2^x-byte-pseudo-page*)
                              (x (loghead *2^x-byte-pseudo-page* x2))
                              (y (ash y2 *2^x-byte-pseudo-page*)))
                   (:instance bitops::logtail-of-logior
                              (a *2^x-byte-pseudo-page*)
                              (x (loghead *2^x-byte-pseudo-page* x1))
                              (y (ash y1 *2^x-byte-pseudo-page*)))
                   (:instance bitops::logtail-of-logior
                              (a *2^x-byte-pseudo-page*)
                              (x (loghead *2^x-byte-pseudo-page* x2))
                              (y (ash y2 *2^x-byte-pseudo-page*)))))))

  (defthm x86$cp-implies-natp-next-addr
    (implies (force (x86$cp x86$c))
             (natp (nth *mem-array-next-addr* x86$c)))
    :rule-classes :type-prescription)

  (defthm |addr < 2 * len-mem-array FORCED|
    (implies (forced-and (<= *initial-mem-array-length* (len (nth *mem-arrayi* x86$c)))
                         (equal (loghead *2^x-byte-pseudo-page*
                                         (len (nth *mem-arrayi* x86$c)))
                                0)
                         (integerp i)
                         (<= 0 i))
             (< (logior (loghead *2^x-byte-pseudo-page* i)
                        (len (nth *mem-arrayi* x86$c)))
                (* 2 (len (nth *mem-arrayi* x86$c)))))
    :hints (("Goal" :use |addr < 2 * len-mem-array|)))

  (defthm read-write-different-helper-lemma-4
    (implies (x86$cp x86$c)
             (<= *initial-mem-array-length*
                 (len (nth *mem-arrayi* x86$c))))
    :hints (("Goal" :in-theory (enable x86$cp good-memp)))
    :rule-classes :linear)

  (defthm expected-mem-array-bound-better
    (implies (force (natp table-len))
             (<= (expected-mem-array-next-addr 0 table-len x86$c)
                 table-len))
    :hints (("Goal" :use ((:instance expected-mem-array-bound-general
                                     (i 0)
                                     (table-len table-len)))))
    :rule-classes :linear)

  (encapsulate
   ()

   (local (in-theory (e/d (concrete-mem-hack) ())))

   (local
    (defthm mem-array-next-addr-is-expected-mem-array-next-addr-alt
      (implies
       (and (x86$cp x86$c)
            (equal len (mem-table-length x86$c)))
       (equal
        (expected-mem-array-next-addr 0 len x86$c)
        (nth *mem-array-next-addr* x86$c)))))

   (encapsulate
    ()
    (local (in-theory ; cover forcing rounds, not just children of "Goal"
            (e/d (mem$ci !mem$ci nfix |addr < 2 * len-mem-array|)
                 (mem-array-next-addr-is-expected-mem-array-next-addr))))

    (defthm read-write-different
      (implies (forced-and (x86$cp x86$c)
                           (unsigned-byte-p *physical-address-size* i)
                           (unsigned-byte-p *physical-address-size* j)
                           (n08p v)
                           ;; (not (equal (logtail *2^x-byte-pseudo-page* i) (logtail *2^x-byte-pseudo-page* j)))
                           (not (equal i j)))
               (equal (mem$ci j (!mem$ci i v x86$c))
                      (mem$ci j x86$c)))
      :hints (("Goal"
               :use ((:instance expected-mem-array-next-addr-bound-when-page-absent
                                (i (logtail *2^x-byte-pseudo-page* i))))))))

   (defthm read-write
     (implies (forced-and (x86$cp x86$c)
                          (unsigned-byte-p *physical-address-size* i)
                          (unsigned-byte-p *physical-address-size* j)
                          (n08p v))
              (equal (mem$ci i (!mem$ci j v x86$c))
                     (if (equal i j)
                         v
                       (mem$ci i x86$c))))
     :hints (("Goal" :use (read-write-same
                           read-write-different))))
   ))

;; ======================================================================

;; Prevent leaks from this book:
;; [Shilpi]: Disable more such thms, or make them local once you
;; figure out what's not needed, etc...
(in-theory (disable |logtail-1 of mem-table value < mem-array-next-addr|
                    |address < shift(mem-array-next-addr) when page is present|
                    |address < len(mem-array) when page is present|
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted))

;; ======================================================================
