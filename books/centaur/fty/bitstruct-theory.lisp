; FTY type support library
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FTY")

;; (include-book "basetypes")
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "centaur/bitops/part-install" :dir :system)
(include-book "centaur/bitops/extra-defs" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)
(include-book "centaur/misc/rewrite-rule" :dir :system)
(include-book "fixequiv")
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (disable bitops::part-install-width-low
                           bitops::part-select-width-low
                           install-bit
                           unsigned-byte-p
                           signed-byte-p
                           logmask)))





;; Misc stuff needed for guards
(defthmd logbit-at-zero-is-loghead-of-1
  ;; [Shilpi] For guard proofs of accessors of fields of width 1.
  (equal (bool->bit (logbitp 0 x))
         (loghead 1 x))
  :hints ((logbitp-reasoning)))

(defthmd part-select-width-low-in-terms-of-loghead-and-logtail
  ;; [Shilpi] For the accessor guard proofs.
  (equal (bitops::part-select-width-low x width low)
         (loghead width (logtail low x)))
  :hints (("Goal" :in-theory (e/d (bitops::part-select-width-low) ()))))

(defthmd part-install-width-low-in-terms-of-logior-logmask-ash
  ;; [Shilpi] For the updater guard proofs.
  (implies (syntaxp (and (or (atom val)
                             (and (consp val)
                                  (eql (car val) 'acl2::bool->bit$inline)))
                         (atom x)))
           (equal (bitops::part-install-width-low val x width low)
                  (logior (logand (lognot (ash (logmask width) (nfix low))) x)
                          (ash (loghead width val) (nfix low)))))
  :hints (("Goal" :in-theory (e/d (bitops::part-install-width-low) ()))))

(defthmd remove-inner-logext-from-logext-logtail-nest
  ;; [Shilpi] For the subfield-related accesor guard proofs.
  (implies (and (< i (- k j))
                (posp i) (natp j) (natp k))
           (equal (logext i (logtail j (logext k x)))
                  (logext i (logtail j x))))
  :hints ((logbitp-reasoning)))

(encapsulate
  ()

  (local
   (defthm crock
     ;; Ugh, dumb arithmetic.
     (equal (+ -1 i (- i) j k) (+ -1 j k))))

  (defthmd remove-outer-logtail-from-logtail-logext-nest
    ;; [Shilpi] For the subfield-related accessor guard proofs.
    (implies (and (< (+ i k) j)
                  (natp i) (natp j) (natp k))
             (equal (logtail i (logext j (logtail k x)))
                    (logext (- j i) (logtail (+ i k) x))))
    :hints ((logbitp-reasoning))))

(defthmd simplify-subfield-updater-guard-expression-with-inner-logext
  ;; [Shilpi] For subfield updater guard proofs
  ;; foo->bar and bar->a: foo->a.  This lemma is applicable when bar is a
  ;; signed subfield of foo.
  (implies (<= (+ (nfix i) (nfix width-a)) (nfix width))
           (equal

            (bitops::part-install-width-low
             (bitops::part-install-width-low
              a
              (logext width (bitops::part-select-width-low x width low))
              width-a i)
             x width low)

            (logior
             (logand
              (lognot (ash (logmask width-a) (+ (nfix i) (nfix low))))
              x)
             (ash (loghead width-a a) (+ (nfix i) (nfix low))))))
  :hints ((logbitp-reasoning)))

(defthmd simplify-subfield-updater-guard-expression-with-more-logext
  ;; [Shilpi] For subfield updater guard proofs
  ;; foo->bar and bar->a: foo->a.  This lemma is applicable when bar is a
  ;; signed subfield of foo,  and a is a signed subfield of foo.
  (implies (<= (+ (nfix i) (nfix width-a)) (nfix width))
           (equal

            (bitops::part-install-width-low
             (logext
              width
              (bitops::part-install-width-low
               a
               (logext width (bitops::part-select-width-low x width low))
               width-a i))
             x width low)

            (logior
             (logand
              (lognot (ash (logmask width-a) (+ (nfix i) (nfix low))))
              x)
             (ash (loghead width-a a) (+ (nfix i) (nfix low))))))
  :hints ((logbitp-reasoning)))


(defthmd unsigned-byte-p-of-bool->bit
  (implies (and (<= 1 n) (natp n))
           (unsigned-byte-p n (bool->bit b))))

(defthmd signed-byte-p-of-bool->bit
  (implies (and (<= 2 n) (natp n))
           (signed-byte-p n (bool->bit b)))
  :hints (("Goal" :in-theory (e/d (signed-byte-p) ()))))

(defthm unsigned-byte-p-of-part-select
  (implies (natp n)
           (unsigned-byte-p n (part-select x :width n :low low)))
  :hints(("Goal" :in-theory (enable part-select))))


(defthmd logbitp-past-width
  (implies (and (unsigned-byte-p n x)
                (<= n (nfix m)))
           (not (logbitp m x)))
  :hints(("Goal" :in-theory (enable* ihsext-inductions
                                     ihsext-recursive-redefs))))

(defthmd logbitp-past-signed-width
  (implies (and (signed-byte-p n x)
                (<= n m)
                (integerp m))
           (equal (logbitp m x) (logbitp (1- n) x)))
  :hints(("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                   bitops::ihsext-inductions)
                                  (signed-byte-p)))))

(defthmd logbitp-past-signed-width2
  (implies (and (<= n m)
                (integerp m)
                (signed-byte-p n x))
           (equal (logbitp m x) (logbitp (1- n) x)))
  :hints(("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                   bitops::ihsext-inductions)
                                  (signed-byte-p)))))




(encapsulate nil
  (local (defthm crock
           (implies (< (+ (nfix a) (nfix b)) c)
                    (< (nfix a) (- c (nfix b))))))
  (local (in-theory (enable bitops::signed-byte-p-of-ash-split)))

  (defthm signed-byte-p-preserved-by-part-install
    (implies (and (< (+ (nfix instwidth) (nfix low)) (nfix width))
                  (signed-byte-p width x))
             (signed-byte-p width (part-install val x :low low :width instwidth)))
    :hints(("Goal" :in-theory (enable part-install)))))



;; Misc stuff needed for guards
(defthm unsigned-byte-p-of-part-select
  (implies (natp n)
           (unsigned-byte-p n (part-select x :width n :low low)))
  :hints(("Goal" :in-theory (enable part-select))))

;; To make things easy for us, we're going to logically phrase all of our
;; operations in terms of just part-select and part-install, including
;; single-bit ones.  But we'll provide exec versions using
;; logbit/logbitp/install-bit, so we need to prove that these are equivalent to
;; part-selects/installs.  These will be enabled only for the guards for these
;; functions.

; Matt K. addition: Avoid ACL2(p) failure due to logbitp-reasoning.
(local (include-book "std/system/non-parallel-book" :dir :system))
(local (acl2::non-parallel-book))

(defthmd part-select-is-logbit
  (equal (part-select x :width 1 :low n)
         (logbit n x))
  :hints ((logbitp-reasoning)))

(local (in-theory (enable bitops::logbitp-of-install-bit-split)))

(defthmd install-bit-is-part-install
  (implies (bitp b)
           (equal (install-bit n b x)
                  (part-install b x :width 1 :low n)))
  :hints ((logbitp-reasoning)))

;; For read-over-write theorems, we have what we need about part-select of
;; part-install from the part-install book.

;; However, we also use logext to produce signed results of both selects and
;; installs, so we also need to know that logext is transparent to selects.  We
;; already have logbitp-of-logext in ihsext-basics

(defthm part-select-of-logext
  (implies (<= (+ (nfix selwidth) (nfix low)) (nfix width))
           (equal (part-select (logext width x) :width selwidth :low low)
                  (part-select x :width selwidth :low low)))
  :hints ((logbitp-reasoning :prune-examples nil)))


;; For accessor-of-constructor theorems: we use logapp as the basic constructor
;; operator.  We have logbitp-of-logapp-split from ihsext-basics, so we just
;; need part-select-of-logapp.

(defthm part-select-of-logapp-below
  (implies (<= (+ (nfix low) (nfix selwidth)) (nfix width))
           (equal (part-select (logapp width x y) :low low :width selwidth)
                  (part-select x :low low :width selwidth)))
  :hints ((logbitp-reasoning)))

(defthm part-select-of-logapp-above
  (implies (<= (nfix width) (nfix low))
           (equal (part-select (logapp width x y) :low low :width selwidth)
                  (part-select y :low (- (nfix low) (nfix width)) :width selwidth)))
  :hints ((logbitp-reasoning)))


;; For fix-equals-constructor, we need to rewrite the constructor inside out
;; into the fix.
;; E.g. (logapp field1-width (part-select x :low field1-low :width field1-width)
;;              (logapp field2-width (part-select x :low field2-low :width field2-width)
;;                      (part-select x :low field3-low :width field3-width)))
;; Variations: the last part-select might have a logext around it to
;; enforce sign.  Each part-select might alternatively be a (bool->bit (logbitp ...)).

(deffixequiv bitops::part-select-width-low$inline :args ((x integerp)
                                                         (bitops::width natp)
                                                         (bitops::low natp)))

(local
 (defthmd logapp-of-part-selects-consolidate-lemma
   (equal (logapp width (part-select x :width width :low low)
                  (part-select x :width width2 :low (+ (nfix low) (nfix  width))))
          (part-select x :width (+ (nfix width) (nfix width2)) :low low))
   :hints ((logbitp-reasoning))))

(defthm logapp-of-part-selects-consolidate
  (implies (equal (nfix low2) (+ (nfix low) (nfix  width)))
           (equal (logapp width (part-select x :width width :low low)
                          (part-select x :width width2 :low low2))
                  (part-select x :width (+ (nfix width) (nfix width2)) :low low)))
  :hints (("goal" :in-theory (enable* arith-equiv-forwarding)
           :use logapp-of-part-selects-consolidate-lemma)))

(local
 (defthmd logapp-of-part-selects-with-logext-consolidate-lemma
   (implies (posp width2)
            (equal (logapp width (part-select x :width width :low low)
                           (logext width2 (part-select x :width width2 :low (+ (nfix low) (nfix  width)))))
                   (logext (+ (nfix width) (nfix width2))
                           (part-select x :width (+ (nfix width) (nfix width2)) :low low))))
   :hints ((logbitp-reasoning))))

(defthm logapp-of-part-selects-with-logext-consolidate
   (implies (and (equal (nfix low2) (+ (nfix low) (nfix  width)))
                 (posp width2))
            (equal (logapp width (part-select x :width width :low low)
                           (logext width2 (part-select x :width width2 :low low2)))
                   (logext (+ (nfix width) (nfix width2))
                           (part-select x :width (+ (nfix width) (nfix width2)) :low low))))
  :hints (("goal" :in-theory (enable* arith-equiv-forwarding)
           :use logapp-of-part-selects-with-logext-consolidate-lemma)))


(defthm logapp-with-part-select-of-head
  (equal (logapp width x (part-select x :width selwidth :low width))
         (loghead (+ (nfix selwidth) (nfix width)) x))
  :hints ((logbitp-reasoning)))

;; When we've rewritten away the logapps, we have one part-select left and it's
;; the whole thing.  We just need to know that it equals the fix, which is
;; loghead for unsigned or logext for signed.

(defthm part-select-at-0-is-loghead
  (equal (equal (part-select x :low 0 :width width) (loghead width x))
         t)
  :hints ((logbitp-reasoning)))

(defthm part-select-at-0-of-loghead-is-loghead
  (equal (equal (part-select (loghead width x) :low 0 :width width) (loghead width x))
         t)
  :hints ((logbitp-reasoning)))

(defthm part-select-at-0-of-bfix-is-bfix
  (equal (equal (part-select (bfix x) :low 0 :width 1) (bfix x))
         t)
  :hints ((logbitp-reasoning)))


(local (defthm unsigned-byte-p-implies-natp-width
         (implies (unsigned-byte-p n x)
                  (natp n))
         :hints(("Goal" :in-theory (enable unsigned-byte-p)))
         :rule-classes :forward-chaining))

(defthm part-select-at-0-of-unsigned-byte-is-x
  (implies (unsigned-byte-p width x)
           (equal (equal (part-select x :low 0 :width width) x)
                  t))
  :hints ((logbitp-reasoning)
          (and stable-under-simplificationp
               '(:in-theory (enable logbitp-past-width)))))

(defthmd part-select-at-0-of-unsigned-byte-identity
  (implies (unsigned-byte-p width x)
           (equal (part-select x :low 0 :width width) x))
  :hints ((logbitp-reasoning)
          (and stable-under-simplificationp
               '(:in-theory (enable logbitp-past-width)))))


(defthm bit->bool-of-part-select-at-0-of-bool->bit-is-bool-fix
  (equal (equal (bit->bool (part-select (bool->bit x) :low 0 :width 1)) (acl2::bool-fix x))
         t)
  :hints (("goal" :in-theory (enable bool->bit bit->bool))
          (logbitp-reasoning)))

(defthmd logext-part-select-at-0-identity
  (implies (posp width)
           (equal (logext width (part-select x :low 0 :width width)) (logext width x)))
  :hints ((logbitp-reasoning)))

(defthm logapp-of-logext
  (implies (<= (nfix n) (nfix m))
           (equal (logapp n (logext m x) y)
                  (logapp n x y)))
  :hints ((logbitp-reasoning)))


;; For update-is-change, we use fix-is-constructor and are left with a
;; part-install of a logapp equalling a logapp, so we rewrite part-install of
;; logapp:

(defthm part-install-of-logapp-here
  (equal (part-install val (logapp width prev rest) :width width :low 0)
         (logapp width val rest))
  :hints ((logbitp-reasoning)))

(defthm part-install-of-logapp-above
  (implies (<= (nfix width) (nfix low))
           (equal (part-install val (logapp width prev rest) :width instwidth :low low)
                  (logapp width prev
                          (part-install val rest :width instwidth :low (- (nfix low) (nfix width))))))
  :hints ((logbitp-reasoning)))

;; Then for the last field, we need to rewrite part-install of a given width
;; into an unsigned-byte of a given width to just the value.



(defthmd part-install-identity
  (implies (unsigned-byte-p width x)
           (equal (part-install val x :width width :low 0)
                  (loghead width val)))
  :hints ((logbitp-reasoning)
          (and stable-under-simplificationp
               '(:in-theory (enable logbitp-past-width)))))

(defthmd part-install-identity-signed
  (implies (posp width)
           (equal (logext width (part-install val x :width width :low 0))
                  (logext width val)))
  :hints ((logbitp-reasoning)))






(defthm logext-of-logapp-above
  (implies (< (nfix width1) (nfix width))
           (equal (logext width (logapp width1 a b))
                  (logapp width1 a (logext (- (nfix width) (nfix width1)) b))))
  :hints ((logbitp-reasoning)))

(defthm logext-of-logapp-below
  (implies (and (<= (nfix width) (nfix width1))
                (posp width))
           (equal (logext width (logapp width1 a b))
                  (logext width a)))
  :hints ((logbitp-reasoning)))


(defthm logapp-with-logext-part-select-of-head
  (implies (posp selwidth)
           (equal (logapp width x (logext selwidth (part-select x :width selwidth :low width)))
                  (logext (+ selwidth (nfix width)) x)))
  :hints (("goal" :use ((:instance logext-of-logapp-above
                         (a x)
                         (b (part-select x :width selwidth :low width))
                         (width (+ selwidth (nfix width)))
                         (width1 width)))
           :in-theory (e/d (logext-part-select-at-0-identity)
                           (logext-of-logapp-above)))))

;; For read-over-write theorems we'll use a function equiv-under-mask,
;; customized to each type.  Each writer will have a rule saying it is
;; equivalent under some mask to the base variable, and each reader will have a
;; bind-free rule that looks up the mask for the writer function.  Illustrated below.

(define int-equiv-under-mask ((x integerp)
                              (y integerp)
                              (mask integerp))
  (equal (logand (logxor x y) mask) 0)
  ///
  (deffixequiv int-equiv-under-mask))

(defun bitstruct-read-over-write-find-rule (term lemmas)
  (declare (xargs :mode :program))
  (if (atom lemmas)
      (mv nil nil)
    (b* (((acl2::rewrite-rule rule) (car lemmas))
         ((unless (equal rule.rhs ''t))
          (bitstruct-read-over-write-find-rule term (cdr lemmas))))
      (case-match rule.lhs
        ((& left right ('quote mask))
         (b* (((mv ok subst) (acl2::one-way-unify left term))
              ((unless ok)
               (bitstruct-read-over-write-find-rule term (cdr lemmas)))
              ((unless (subsetp (all-vars right) (strip-cars subst)))
               (bitstruct-read-over-write-find-rule term (cdr lemmas))))
           (mv mask (acl2::sublis-var subst right))))
        (& (bitstruct-read-over-write-find-rule term (cdr lemmas)))))))


(defun bitstruct-read-over-write-bind-free (write-term
                                            equiv-under-mask-fn
                                            mask-var y-var
                                            mfc state)
  (declare (ignore mfc)
           (xargs :stobjs state
                  :mode :program))
  (b* ((wrld (w state))
       (lemmas (getpropc equiv-under-mask-fn 'acl2::lemmas nil wrld))
       ((mv mask ans) (bitstruct-read-over-write-find-rule write-term lemmas))
       ((unless mask) nil))
    `((,mask-var . ',mask)
      (,y-var . ,ans))))

(defmacro bitstruct-read-over-write-hyps (write-term
                                          equiv-under-mask-fn
                                          &key
                                          (mask-var 'mask)
                                          (y-var 'y))
  `(and (syntaxp (and (consp ,write-term)
                      (symbolp (car ,write-term))
                      (not (eq (car ,write-term) 'quote))))
        (bind-free (bitstruct-read-over-write-bind-free
                    ,write-term ',equiv-under-mask-fn ',mask-var ',y-var
                    mfc state)
                   (,mask-var ,y-var))))

(defthm b-xor-equals-0
  (equal (equal (b-xor a b) 0)
         (bit-equiv a b))
  :hints(("Goal" :in-theory (enable bit-equiv b-xor))))

(defthmd not-of-b-xor
  (iff (bit->bool (b-xor a b))
       (not (bit-equiv a b)))
  :hints(("Goal" :in-theory (enable bit-equiv b-xor))))

(defthmd equal-of-bool->bit
  (equal (equal (bool->bit a) (bool->bit b))
         (equal (acl2::bool-fix a) (acl2::bool-fix b)))
  :hints(("Goal" :in-theory (enable bool->bit))))

(defthmd equal-of-bit->bool
  (equal (equal (bit->bool a) (bit->bool b))
         (equal (bfix a) (bfix b)))
  :hints(("Goal" :in-theory (enable bit->bool))))

(defmacro bitstruct-logbitp-reasoning ()
  '(logbitp-reasoning :simp-hint (:in-theory (enable* logbitp-case-splits
                                                      bitops::logbitp-of-const-split))
                      :add-hints (:in-theory (enable* logbitp-case-splits
                                                      bitops::logbitp-of-const-split
                                                      equal-of-bool->bit
                                                      not-of-b-xor))
                      :prune-examples nil
                      :passes 2))


(defthmd logand-mask-logxor-equal-0
  (equal (equal (logand mask (logxor x y)) 0)
         (equal (logand mask x) (logand mask y)))
  :hints ((bitstruct-logbitp-reasoning)))

(defthmd logand-const-of-logapp
  (implies (syntaxp (and (quotep mask) (quotep width)))
           (equal (logand mask (logapp width a b))
                  (logapp width (logand (loghead width mask) a)
                          (logand (logtail width mask) b))))
  :hints ((bitstruct-logbitp-reasoning)
          (and stable-under-simplificationp
               '(:in-theory (enable bool->bit)))))

(defthmd int-equiv-under-mask-of-submask
  (implies (and (int-equiv-under-mask x y mask)
                (equal (logand mask1 (lognot mask)) 0))
           (int-equiv-under-mask x y mask1))
  :hints(("Goal" :in-theory (enable int-equiv-under-mask))
         (bitstruct-logbitp-reasoning)))

;; practice
(local
 (progn
   (define write-field1 ((val integerp)
                         (x integerp))
     (part-install val x :width 4 :low 3)
     ///
     (make-event
      `(defthm write-field1-equiv-mask
         (int-equiv-under-mask (write-field1 val x) x ,(lognot (ash (logmask 4) 3)))
         :hints (("goal" :in-theory (enable int-equiv-under-mask))
                 (logbitp-reasoning)))))


   (define read-field2 ((x integerp))
     (part-select x :width 3 :low 7)
     ///
     (local (in-theory (enable equal-of-bool->bit)))
     (defthm read-field2-when-equiv-under-mask
       (implies (and (bitstruct-read-over-write-hyps x int-equiv-under-mask)
                     (int-equiv-under-mask x y mask)
                     (equal (logand (lognot mask) (ash (logmask 3) 7)) 0))
                (equal (read-field2 x)
                       (read-field2 y)))
       :hints(("Goal" :in-theory (enable int-equiv-under-mask))
              (logbitp-reasoning))))

   ;; this is the kind of thing you don't need to prove when you have
   ;; read-field2-when-equiv-under-mask.
   (defthm read-field2-of-write-field1
     (equal (read-field2 (write-field1 v x)) (read-field2 x)))))


(defthm part-install-of-select-same
  (equal (part-install (part-select x :width width :low low)
                       x :width width :low low)
         (ifix x))
  :hints ((logbitp-reasoning)))



(defthm part-install-of-part-install-same
  (implies (<= (+ (nfix width2) (nfix low2)) (nfix width1))
           (equal (part-install (part-install val (part-select x :width width1 :low low1)
                                              :width width2 :low low2)
                                x :width width1 :low low1)
                  (part-install val x :width width2 :low (+ (nfix low2) (nfix low1)))))
  :hints ((logbitp-reasoning)))

(defthm unsigned-byte-p-1-when-bitp
  (implies (bitp x)
           (unsigned-byte-p 1 x)))

(defthm bitp-when-unsigned-byte-p-1
  (implies (unsigned-byte-p 1 x)
           (bitp x))
  :hints(("Goal" :in-theory (enable unsigned-byte-p bitp))))

(defthm signed-byte-p-2-when-bitp
  (implies (bitp x)
           (signed-byte-p 2 x))
  :hints (("Goal" :in-theory (e/d (signed-byte-p bitp) ()))))

(defthmd signed-byte-p-+1
  ;; A less general version of bitops::signed-byte-p-incr.
  (implies (signed-byte-p (1- n) x)
           (signed-byte-p n x))
  :hints (("Goal" :in-theory (e/d (signed-byte-p) ()))))

(defthmd signed-byte-p-one-bigger-when-unsigned-byte-p
  (implies (unsigned-byte-p (1- n) x)
           (signed-byte-p n x))
  :hints (("Goal" :in-theory (e/d (signed-byte-p unsigned-byte-p) ()))))

(defthm part-select-width-1-type
  (bitp (part-select x :low n :width 1))
  :rule-classes :type-prescription)

(defthm logapp-natp
  (implies (not (negp b))
           (natp (logapp w a b)))
  :rule-classes :type-prescription)




;; ;; We'll rewrite each part-select into a logtail -- the innermost because the
;; ;; width of x is low+width, the others because they're inside logapp width so
;; ;; the width on the partselect is redundant.

;; (encapsulate nil
;;   (local (defthm logbitp-past-width
;;            (implies (and (unsigned-byte-p n x)
;;                          (<= n (nfix m)))
;;                     (not (logbitp m x)))
;;            :hints(("Goal" :in-theory (enable* ihsext-inductions
;;                                               ihsext-recursive-redefs)))))

;;   (defthmd part-select-at-width-is-logtail
;;     (implies (unsigned-byte-p (+ (nfix low) (nfix width)) x)
;;              (equal (part-select x :width width :low low)
;;                     (logtail low x)))
;;     :hints ((logbitp-reasoning)))

;;   (local (defthm logbitp-past-width-signed
;;            (implies (and (signed-byte-p n x)
;;                          (<= n (nfix m)))
;;                     (equal (logbitp m x)
;;                            (logbitp (1- n) x)))
;;            :hints(("Goal" :in-theory (enable* ihsext-inductions
;;                                               ihsext-recursive-redefs)))))

;;   (defthmd logext-of-part-select-at-width-is-logtail
;;     (implies (and (signed-byte-p (+ (nfix low) (nfix width)) x)
;;                   (posp width))
;;              (equal (logext width (part-select x :width width :low low))
;;                     (logtail low x)))
;;     :hints ((logbitp-reasoning))))


;; ;; Then we need (logapp width (logtail n1 x) (logtail n2 x)) = (logtail n1 x) when n2 = n1+width
;; ;; and the variant for n1=0, (logapp width x (logtail width x)).

;; (local (defthmd logapp-of-logtails-consolidate-lemma
;;          (equal (logapp width (logtail n1 x) (logtail (+ (nfix n1) (nfix width)) x))
;;                 (logtail n1 x))
;;          :hints ((logbitp-reasoning))))

;; (defthm logapp-of-logtails-consolidate
;;   (implies (equal (nfix n2) (+ (nfix n1) (nfix width)))
;;            (equal (logapp width (logtail n1 x) (logtail n2 x))
;;                   (logtail n1 x)))
;;   :hints (("goal" :in-theory (enable* arith-equiv-forwarding)
;;            :use logapp-of-logtails-consolidate-lemma)))

;; (defthm logapp-of-logtail-consolidate
;;   (equal (logapp width x (logtail width x))
;;          (ifix x))
;;   :hints (("goal" :in-theory (enable* arith-equiv-forwarding)
;;            :use ((:instance logapp-of-logtails-consolidate-lemma
;;                   (n1 0))))))






;; ;; We use part-install and install-bit as updaters and logbit/logbitp and
;; ;; part-select as accessors.

;; ;; The part-install book includes the necessary theorems about
;; ;; logbitp of part-install
;; ;; part-select of part-install

;; ;; The install-bit book includes the necessary theorems about
;; ;; logbitp of install-bit

;; ;; So we basically just need theorems about:
;; ;; part-select of install-bit

;; ;; We probably just need non-overlapping ones, because we'd use logbitp to
;; ;; select any field that we'd use install-bit to update.
;; (defthm part-select-below-install-bit
;;   (implies (<= (+ (nfix width) (nfix low)) (nfix bit))
;;            (equal (part-select (install-bit bit val x) :low low :width width)
;;                   (part-select x :low low :width width)))
;;   :hints ((logbitp-reasoning)))

;; (defthm part-select-above-install-bit
;;   (implies (< (nfix bit) (nfix low))
;;            (equal (part-select (install-bit bit val x) :low low :width width)
;;                   (part-select x :low low :width width)))
;;   :hints ((logbitp-reasoning)))
