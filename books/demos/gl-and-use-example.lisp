; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann and Cuong Kim Chau (original date March, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; An example illustrating the use GL to prove unbounded theorems

; The final theorem in this file, main, is essentially one that arose during a
; proof effort.  The problem was to automate its proof using the GL package,
; even though it involves a variable, mem-val, that is not of finite type.  A
; proof strategy, very roughly, is to use GL to prove the theorem when mem-val
; is the "expected" type -- a 32-bit natural number -- and then derive the full
; theorem as a corollary.  We mechanize that rough strategy by proving that
; bounded lemma, main-1, using def-gl-thm, and then deriving from it the lemma
; main-2 below, which restricts to the case that mem-val is replaced by a
; typical 32-bit natural number, (mod mem-val *2^32*).  The main theorem is
; then essentially a consequence of main-2: a :use hint creates the goal
; (implies {main-2} {main}), where {NAME} denotes the formula associated with
; NAME.

; However, in order to reduce (implies {main-2} {main}) to (implies {main}
; {main}) and hence T, we prove three rewrite rules that together simplify
; {main-2} to {main}: main-3, main-4, and main-5.  Each of these replaces
; (mod mem-val *2^32*) by mem-val in one of the contexts where the term
; (mod mem-val *2^32*) occurs in {main-2} after applying its let-binding.

; To begin with, we execute the following
; portcullis command so that we can read the call of gl::g-int below:

; (include-book "centaur/gl/gl" :dir :system)

(in-package "ACL2")

; The following four events set up an environment that is similar to the one
; that was present in the original example:

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (disable ash-to-floor)))

(local (defthm default-ash-1
         (implies
          (syntaxp (not (proveably-integer 'x
                                           (cons (cons 'x x) 'nil)
                                           mfc state)))
          (equal (ash x n)
                 (if (integerp x) (ash x n) 0)))
         :hints (("Goal" :in-theory (enable ash)))))

(defconst *2^32* (expt 2 32))

; Here is the bounded version of the main theorem.

(local
 (def-gl-thm main-1
   :hyp (and (natp i02)
             (< i02 3)
             (natp mem-val)
             (< mem-val *2^32*))
   :concl (equal (logior (mod (ash mem-val (* -8 i02))
                              256)
                         (* 256
                            (mod (ash mem-val (+ -8 (* -8 i02)))
                                 256)))
                 (mod (ash mem-val (* -8 i02))
                      65536))
   :g-bindings
   `((mem-val ,(gl::g-int 0 2 33))
     (i02 ,(gl::g-int 1 2 3)))))

; Here is the version of the main theorem in which mem-val is replaced by
; (mod mem-val *2^32*).

(defthm main-2
  (let ((mem-val (mod mem-val *2^32*)))
    (implies (and (natp i02)
                  (< i02 3))
             (equal (logior (mod (ash mem-val (* -8 i02))
                                 256)
                            (* 256
                               (mod (ash mem-val (+ -8 (* -8 i02)))
                                    256)))
                    (mod (ash mem-val (* -8 i02))
                         65536))))
  :rule-classes nil)

; Now main-1 is no longer needed.
(local (in-theory (disable main-1)))

; Next come the three lemmas that eliminate occurrences of
; (mod mem-val *2^32*) in {main-2}.

(defthm main-3
  (implies (and (natp i02)
                (< i02 3))
           (equal (mod (ash (mod mem-val *2^32*)
                            (+ -8 (* -8 i02)))
                       256)
                  (mod (ash mem-val
                            (+ -8 (* -8 i02)))
                       256)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm main-4
  (implies (and (natp i02)
                (< i02 3)
                (integerp mem-val))
           (equal (mod (ash (mod mem-val *2^32*)
                            (* -8 i02))
                       256)
                  (mod (ash mem-val
                            (* -8 i02))
                       256)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm main-5
  (implies (and (natp i02)
                (< i02 3)
                (integerp mem-val))
           (equal (mod (ash (mod mem-val *2^32*)
                            (* -8 i02))
                       65536)
                  (mod (ash mem-val
                            (* -8 i02))
                       65536)))
  :hints (("Goal" :in-theory (enable ash))))

; Finally, the main result follows by using main-2, given the three rewrite
; rules just above.  We had originally considered forcing the hypotheses
; (integerp mem-val) in the preceding two rules, but it turned out not to be
; necessary, presumably because of case-splitting on (integerp mem-val)
; provided by DEFAULT-ASH-1 and/or other rewrite rules.

(defthm main
  (implies (and (natp i02)
                (< i02 3)

; Note that we do not need to assume (integerp mem-val); indeed, DEFAULT-ASH-1
; can introduce a split for each (ash mem-val ...) expression such that it is
; replaced by 0 in the case that (not (integerp mem-val)), in which case the
; resulting formula follows by evaluation.

                )
           (equal (logior (mod (ash mem-val (* -8 i02))
                               256)
                          (* 256
                             (mod (ash mem-val (+ -8 (* -8 i02)))
                                  256)))
                  (mod (ash mem-val (* -8 i02))
                       65536)))
  :hints (("Goal"
           :use
           (main-2))))
