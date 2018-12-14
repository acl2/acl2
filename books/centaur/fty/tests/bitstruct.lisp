; FTY type support library
; Copyright (C) 2018 Centaur Technology
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
; Some contributions by Shilpi Goel <shilpi@centtech.com>

(in-package "FTY")
(include-book "../bitstruct")

(defbitstruct foo
  ;; Unsigned bitstruct with unsigned fields
  ((a bitp)
   (b booleanp)
   (c bitp)))

(defbitstruct foo-inline
  ;; Unsigned bitstruct with unsigned fields, with inlined accessors and updaters
  ((a bitp)
   (b booleanp)
   (c bitp))
  :inline t)

(defbitstruct foos
  ;; Signed bitstruct with unsigned fields
  ((a bitp)
   (b booleanp)
   (d bitp))
  :signedp t)

(defbitstruct bar
  ;; Unsigned bitstruct with an unsigned bitstruct field
  ((a bitp)
   (b booleanp)
   (c foo-p)
   (d bitp)))

(defbitstruct bars
  ;; Signed bitstruct with an unsigned bitstruct field
  ((a bitp)
   (b booleanp)
   (c foo-p)
   (d bitp))
  :signedp t)

(defbitstruct barss
  ;; Signed bitstruct with a signed bitstruct field
  ((a bitp)
   (b booleanp)
   (c foos-p)
   (d bitp))
  :signedp t)

(defbitstruct qux
  ;; Unsigned bitstruct with an unsigned and a signed bitstruct fields
  ((d bar-p)
   (a foos-p)))

(defbitstruct quxs
  ;; Signed bitstruct with an unsigned and a signed bitstruct fields
  ((d bar-p)
   (a foos-p))
  :signedp t)

(defbitstruct quux
  ;; Unsigned bitstruct with a signed and an unsigned bitstruct fields
  ((a foos-p)
   (d bar-p)))

(defbitstruct quuxs
  ;; Signed bitstruct with a signed and an unsigned bitstruct fields
  ((a foos-p)
   (d bar-p))
  :signedp t)

;; Misc. tests:

(defbitstruct signed3 3 :signedp t)
(defbitstruct unsigned5 5)

(defbitstruct baz
  ((a foo-p)
   (b signed3-p)
   (c unsigned5-p)
   (d bar-p)))

(defbitstruct s2 2 :signedp t)

(defbitstruct abababa
  :signedp t
  ((a s2)
   (b baz)
   (c bit)
   (d s2)
   (e boolean)
   (f s2)))

(defbitstruct rc 2)

(defbitstruct fp-flags
  ((ie bitp)
   (de bitp)
   (ze bitp)
   (oe bitp)
   (ue bitp)
   (pe bitp)))

(defbitstruct mxcsr
  ;; Note that mxcsr->ie is inlined, but fp-flags->ie is not.
  ((flags fp-flags
          :subfields (ie de ze oe ue pe))
   (daz bitp)
   (masks fp-flags
          :subfields (im dm zm om um pm))
   (rc  rc)
   (ftz bitp))
  :inline t)

;; Tests where fullp field may be non-nil:

(define ternary-p (x)
  (and (natp x)
       (<= x 2))
  ///
  (defthm unsigned-byte-2-when-ternary-p
    (implies (ternary-p x)
             (unsigned-byte-p 2 x)))

  (defthm ternary-p-compound-recognizer
    (implies (ternary-p x)
             (natp x))
    :rule-classes :compound-recognizer))

(define ternary-fix ((x ternary-p))
  :prepwork ((local (in-theory (enable ternary-p))))
  :returns (xx ternary-p
               :rule-classes (:rewrite (:type-prescription :typed-term xx)))
  (if (ternary-p x) x 0)
  ///
  (defthm ternary-fix-when-ternary-p
    (implies (ternary-p x)
             (equal (ternary-fix x) x)))

  (defthm unsigned-byte-p-of-ternary-fix
    (unsigned-byte-p 2 (ternary-fix x)))

  (fty::deffixtype ternary :pred ternary-p :fix ternary-fix :equiv ternary-equiv :define t :forward t))

(fixtype-to-bitstruct ternary :width 2)

(defbitstruct fafaf
  ((a ternary)
   (b baz)
   (c bit)
   (d ternary)
   (e boolean)
   (f ternary)))

(defbitstruct fafafa
  :signedp t
  ((a ternary)
   (b baz)
   (c bit)
   (d ternary)
   (e boolean)
   (f ternary)))

(defbitstruct bababa
  :signedp t
  ((a rc)
   (b baz)
   (c bit)
   (d rc)
   (e boolean)
   (f rc)))

(define sternary-p (x)
  (or (equal x 0)
      (equal x 1)
      (equal x -1))
  ///
  (defthm signed-byte-2-when-sternary-p
    (implies (sternary-p x)
             (signed-byte-p 2 x)))

  (defthm sternary-p-compound-recognizer
    (implies (sternary-p x)
             (and (integerp x)
                  (<= x 1)))
    :rule-classes :compound-recognizer))

(define sternary-fix ((x sternary-p))
  :prepwork ((local (in-theory (enable sternary-p))))
  :returns (xx sternary-p
               :rule-classes (:rewrite (:type-prescription :typed-term xx)))
  (if (sternary-p x) x 0)
  ///
  (defthm sternary-fix-when-sternary-p
    (implies (sternary-p x)
             (equal (sternary-fix x) x)))

  (defthm signed-byte-p-of-sternary-fix
    (signed-byte-p 2 (sternary-fix x)))

  (fty::deffixtype sternary :pred sternary-p :fix sternary-fix :equiv sternary-equiv :define t :forward t))

(fixtype-to-bitstruct sternary :width 2 :signedp t)

(defbitstruct afafaf
  ((a sternary)
   (b baz)
   (c bit)
   (d sternary)
   (e boolean)
   (f sternary)))

(defbitstruct afafafa
  :signedp t
  ((a sternary)
   (b baz)
   (c bit)
   (d sternary)
   (e boolean)
   (f sternary)))

;; [Shilpi] Added the following to check whether the mbe-related guard proofs
;; of accessor/updater functions succeed when there are subfields of width > 1:
(defbitstruct 3bitp 3)

(defbitstruct subfield-helper-unsigned
  ((three 3bitp)
   (one bitp)
   (two s2)
   (bool booleanp)))

(defbitstruct subfield-helper-signed
  :signedp t
  ((three 3bitp)
   (one bitp)
   (two s2)
   (bool booleanp)))

(defbitstruct subfield-test-unsigned-unsigned
  ((a bitp)
   (subfldtest subfield-helper-unsigned
               :subfields (three one two bool))))

(defbitstruct subfield-test-unsigned-signed
  :signedp t
  ((a bitp)
   (subfldtest subfield-helper-unsigned
               :subfields (three one two bool))))

(defbitstruct subfield-test-signed-unsigned
  ((a bitp)
   (subfldtest subfield-helper-signed
               :subfields (three one two bool))))

(defbitstruct subfield-test-signed-signed
  :signedp t
  ((a bitp)
   (subfldtest subfield-helper-signed
               :subfields (three one two bool))))

(defbitstruct nest1
  ((d bitp)
   (e subfield-test-signed-signed :subfields (a subfieldtest))))

(defbitstruct nest2
  ((f nest1 :subfields (d e))
   (g 3bitp)))

(defbitstruct nest3
  :signedp t
  ((h bitp)
   (i nest2 :subfields (f g))))