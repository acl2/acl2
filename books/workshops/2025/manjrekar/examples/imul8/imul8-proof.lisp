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
; Original author: Mayank Manjrekar <mayank.manjrekar2@arm.com>

(in-package "RTL")

(include-book "imul8")
(include-book "../../ctv-cp")
(include-book "projects/rac/lisp/alt-const-fns-gen" :dir :system)

;;; Correctness of the compress function:
(local
 (compress::def-ctv-thmd compress-lemma
   (implies (and (integerp pp0) (integerp pp1) (integerp pp2) (integerp pp3)
                 (integerp pp4) (integerp pp5) (integerp pp6) (integerp pp7))
            (equal (compress pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7)
                   (bits (+ pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7) 15 0)))
   :expand (compress)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The rest of the book contains proof of correctness of computeProd function

(local (arith-5-for-rtl))

(local
 (defthmd-nl genpp-loop-lemma
   (implies (and (natp i)
                 (natp j)
                 (bvecp a 8)
                 (bvecp b 8))
            (equal (ag i (genpp-loop-0 j a b pp))
                   (if (and (<= j i) (< i 8))
                       (ash (* (bitn a i) b) i)
                     (ag i pp))))
   :hints (("Goal" :in-theory (e/d (genpp-loop-0
                                    cat bvecp) ())))))

(local-defthm genpp-lemma
  (implies (and (natp i)
                (< i 8)
                (bvecp a 8)
                (bvecp b 8))
           (equal (ag i (genpp a b))
                  (ash (* (bitn a i) b) i)))
  :hints (("Goal" :in-theory (e/d (genpp genpp-loop-lemma) ()))))

(local-defthmd sumpp-lemma
  (implies (and (bvecp a 8)
                (bvecp b 8))
           (b* ((pp (genpp a b)))
             (equal (+ (ag 0 pp) (ag 1 pp) (ag 2 pp) (ag 3 pp) (ag 4 pp) (ag 5 pp) (ag 6 pp) (ag 7 pp))
                    (* a b))))
  :hints (("Goal" :in-theory (e/d (bits-plus-bits-shatter) (bits-tail))
                  :use ((:instance bits-tail
                         (x a) (i 7))))))

(defthmd-nl computeProd-correct
  (implies (and (bvecp a 8)
                (bvecp b 8))
           (equal (computeprod a b)
                  (* a b)))
  :hints (("Goal" :in-theory (e/d (computeprod
                                   compress-lemma
                                   bvecp)
                                  ())
                  :use (sumpp-lemma))))
