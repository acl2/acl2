; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")

;; Formerly, GL had built-in support for coerce, intern-in-package-of-symbol,
;; and code-char.  These would essentially lift IFs within the arguments for
;; these functions, including any symbolic bits, and create a nest of IFs with
;; constants at the leaves giving the correct results for each of these
;; functions in each case.  It also had built-in support for complex rationals.

;; We have now stripped out this special support in favor of using term-level
;; reasoning to support these.

;; Essentially, we view everything other than Booleans, integers, and conses as
;; derived types.  In this file we provide rewrite rules that support
;; extracting their various fields and comparing them with EQUAL.
(include-book "def-gl-rewrite")
(include-book "general-objects")
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defsection characters
  ;; The canonical representation for a character is just (code-char code), and
  ;; we only have two accessors to worry about: char-code and equal.
  (def-gl-rewrite characterp-of-code-char
    (characterp (code-char x)))

  (def-gl-rewrite char-code-of-code-char
    (equal (char-code (code-char x))
           (if (unsigned-byte-p 8 x) x 0)))


  ;; We have this if we need it, but probably don't unless someone's using a character variable or something.
  ;; (def-gl-rewrite code-char-of-char-code
  ;;   (equal (code-char (char-code x))
  ;;          (if (characterp x) x (code-char 0))))

  (def-gl-rewrite equal-of-code-char-1
    (equal (equal (code-char x) y)
           (and (characterp y)
                (equal (char-code y)
                       (if (unsigned-byte-p 8 x) x 0))))
    :hints (("goal" :use ((:instance code-char-char-code-is-identity
                           (c y)))
             :in-theory (disable code-char-char-code-is-identity)))))


(defsection strings
  ;; The canonical representation for a string is (coerce lst 'string), and the
  ;; only accessor is (coerce x 'list).

  (def-gl-rewrite stringp-of-coerce-string
    (stringp (coerce x 'string)))

  (local (defthm character-listp-of-make-character-list
           (character-listp (make-character-list x))))

  (def-gl-rewrite coerce-list-of-coerce-string
    (equal (coerce (coerce x 'string) 'list)
           (make-character-list x))
    :hints (("goal" :use ((:instance completion-of-coerce (y 'string))))))

  (def-gl-rewrite equal-of-coerce-string
    (equal (equal (coerce x 'string) y)
           (and (stringp y)
                (equal (make-character-list x)
                       (coerce y 'list))))
    :hints (("goal" :use ((:instance completion-of-coerce (y 'string))
                          (:instance coerce-inverse-2 (x y)))
             :in-theory (disable coerce-inverse-2)))))


(defsection symbols
  ;; The canonical representation for a symbol is (intern-in-package-of-symbol str pkg).
  ;; Symbol-name and symbol-package-name are the accessors.

  (def-gl-rewrite symbolp-of-intern-in-package-of-symbol
    (symbolp (intern-in-package-of-symbol name pkg)))

  (def-gl-rewrite symbol-name-of-intern-in-package-of-symbol
    (equal (symbol-name (intern-in-package-of-symbol name pkg))
           (if (and (stringp name) (symbolp pkg))
               name
             "NIL")))

  (def-gl-rewrite symbol-package-name-of-intern-in-package-of-symbol
    (equal (symbol-package-name (intern-in-package-of-symbol name pkg))
           (if (and (stringp name) (symbolp pkg))
               (let ((find (member-symbol-name name (pkg-imports (symbol-package-name pkg)))))
                 (if find
                     (symbol-package-name (car find))
                   (symbol-package-name pkg)))
             "COMMON-LISP")))

  (local (defthm equal-of-symbols
           (implies (symbolp x)
                    (equal (equal x y)
                           (and (symbolp y)
                                (equal (symbol-name x) (symbol-name y))
                                (equal (symbol-package-name x) (symbol-package-name y)))))
           :hints(("Goal" :in-theory (disable intern-in-package-of-symbol-symbol-name)
                   :use ((:instance intern-in-package-of-symbol-symbol-name)
                         (:instance intern-in-package-of-symbol-symbol-name
                          (x y)))))
           :rule-classes nil))

  (local (defthm symbolp-of-member-symbol-name
           (implies (symbol-listp lst)
                    (symbolp (car (member-symbol-name x lst))))
           :hints(("Goal" :in-theory (enable member-symbol-name)))))

  (local (defthm symbol-name-of-member-symbol-name
           (implies (member-symbol-name x lst)
                    (equal (symbol-name (car (member-symbol-name x lst)))
                           x))
           :hints(("Goal" :in-theory (enable member-symbol-name)))))

  (def-gl-rewrite equal-of-intern-in-package-of-symbol
    (equal (equal (intern-in-package-of-symbol name pkg) sym)
           (if (and (symbolp pkg) (stringp name))
               (and (symbolp sym)
                    (equal name (symbol-name sym))
                    (equal (symbol-package-name sym)
                           (let ((find (member-symbol-name name (pkg-imports (symbol-package-name pkg)))))
                             (if find (symbol-package-name (car find)) (symbol-package-name pkg)))))
             (equal sym nil)))
    :hints (("goal" :use ((:instance symbol-package-name-of-intern-in-package-of-symbol)
                          (:instance equal-of-symbols
                           (x (intern-in-package-of-symbol name pkg))
                           (y sym)))
             ;; :in-theory (disable symbol-package-name-of-intern-in-package-of-symbol)
             ))))


(defsection complex
  ;; Complex numbers are fairly simple compared to rationals, at least.
  ;; Canonical representation is just (complex realpart imagpart).
  ;; We support +, -, *, integerp, rationalp, acl2-numberp, realpart, imagpart.

  (def-gl-rewrite realpart-of-complex
    (equal (realpart (complex real imag))
           (rfix real))
    :hints (("goal" :cases ((rationalp imag)))))

  (def-gl-rewrite imagpart-of-complex
    (equal (imagpart (complex real imag))
           (rfix imag))
    :hints (("goal" :cases ((rationalp real)))))

  (local (in-theory (enable realpart-of-complex imagpart-of-complex)))

  (def-gl-rewrite equal-of-complex
    (equal (equal (complex real imag) x)
           (and (acl2-numberp x)
                (equal (rfix real) (realpart x))
                (equal (rfix imag) (imagpart x)))))

  (local (in-theory (enable equal-of-complex)))

  (def-gl-rewrite +-of-complex-1
    (equal (+ (complex real imag) x)
           (complex (+ (rfix real) (realpart x))
                    (+ (rfix imag) (imagpart x)))))

  (def-gl-rewrite +-of-complex-2
    (equal (+ x (complex real imag))
           (complex (+ (realpart x) (rfix real))
                    (+ (imagpart x) (rfix imag)))))

  (def-gl-rewrite +-of-complex-3
    (equal (+ x (complex real imag) z)
           (+ (complex (+ (realpart x) (rfix real))
                       (+ (imagpart x) (rfix imag)))
              z)))

  (local (in-theory (disable equal-of-complex)))

  (def-gl-rewrite realpart-of-rational
    (implies (rationalp x)
             (equal (realpart x) x)))

  (def-gl-rewrite imagpart-of-rational
    (implies (rationalp x)
             (equal (imagpart x) 0)))

  (local (in-theory (enable realpart-of-rational
                            imagpart-of-rational)))

  (defthm realpart-of-i-*-rational
    (implies (rationalp r)
             (equal (realpart (* #c(0 1) r))
                    0))
    :hints (("goal" :use ((:instance complex-definition (x 0) (y r))))))

  (defthm imagpart-of-i-*-rational
    (implies (rationalp r)
             (equal (imagpart (* #c(0 1) r))
                    r))
    :hints (("goal" :use ((:instance complex-definition (x 0) (y r))))))


  (def-gl-rewrite minus-of-complex
    (equal (- (complex real imag))
           (complex (- (rfix real)) (- (rfix imag))))
    :hints(("Goal" :in-theory (enable complex-definition))))


  (local (defthm *-of-complexes
           (equal (* (complex real imag) (complex realx imagx))
                  (complex (- (* (rfix real) (rfix realx))
                              (* (rfix imag) (rfix imagx)))
                           (+ (* (rfix real) (rfix imagx))
                              (* (rfix imag) (rfix realx)))))
           :hints(("Goal" :in-theory (enable complex-definition)))))

  (def-gl-rewrite *-of-complex-1
    (equal (* (complex real imag) x)
           (complex (- (* (rfix real) (realpart x))
                       (* (rfix imag) (imagpart x)))
                    (+ (* (rfix real) (imagpart x))
                       (* (rfix imag) (realpart x)))))
    :hints(("Goal" :in-theory (enable complex-definition))))

  (def-gl-rewrite *-of-complex-2
    (equal (* x (complex real imag))
           (complex (- (* (rfix real) (realpart x))
                       (* (rfix imag) (imagpart x)))
                    (+ (* (rfix real) (imagpart x))
                       (* (rfix imag) (realpart x)))))
    :hints(("Goal" :in-theory (enable complex-definition))))

  (local (in-theory (enable *-of-complex-2)))

  (def-gl-rewrite *-of-complex-3
    (equal (* x (complex real imag) z)
           (* (complex (- (* (rfix real) (realpart x))
                          (* (rfix imag) (imagpart x)))
                       (+ (* (rfix real) (imagpart x))
                          (* (rfix imag) (realpart x))))
              z)))

  (def-gl-rewrite rationalp-of-complex
    (equal (rationalp (complex real imag))
           (equal (rfix imag) 0)))

  (def-gl-rewrite integerp-of-complex
    (equal (integerp (complex real imag))
           (and (integerp (rfix real))
                (equal (rfix imag) 0))))

  (def-gl-rewrite acl2-numberp-of-complex
    (acl2-numberp (complex real imag)))

  (def-gl-rewrite complex-when-imag-0
    (equal (complex real 0)
           (rfix real))))


(defsection rationals
  ;; Rationals are much harder than the others to support comprehensively, and
  ;; we won't really try.  We'll mostly try and support operations that reduce
  ;; to integers, and enough associativity/commutativity of multiplication to
  ;; consolidate divides and multiplies.  We'll try to normalize ratios of
  ;; integers to the form (* a (/ b)) or (* a recip) where recip is 1/n.

  (def-gl-rewrite acl2-numberp-of-/
    (acl2-numberp (/ x)))

  (local (defthm multiply-both-sides
           (implies (and (equal (* a b) (* a c))
                         (not (equal (fix a) 0)))
                    (equal (fix b) (fix c)))
           :rule-classes nil))


  ;; Normalize ratios of integers to the form (* a (/ b)).
  (def-gl-rewrite reciprocal-inverse
    (equal (/ (/ x))
           (fix x)))

  (local (defthm recip-identity
           (implies (not (equal (fix a) 0))
                    (equal (* a (/ a) b)
                           (fix b)))))
           ;; :hints (("goal" :use ((:instance associativity-of-*
           ;;                        (x a) (y (/ a) ))

  (def-gl-rewrite reciprocal-over-multiply
    (equal (/ (* x y))
           (* (/ x) (/ y))))

  ; reciprocal of complex:
  ;  1/(a+ib) = (a-ib)/(a^2-b^2)

  (local (defthm complex-equal-0
           (iff (equal (complex real imag) 0)
                (and (equal (rfix real) 0)
                     (equal (rfix imag) 0)))
           :hints(("Goal" :in-theory (enable equal-of-complex)))))

  (local (defthm *-of-complexes
           (equal (* (complex real imag) (complex realx imagx))
                  (complex (- (* (rfix real) (rfix realx))
                              (* (rfix imag) (rfix imagx)))
                           (+ (* (rfix real) (rfix imagx))
                              (* (rfix imag) (rfix realx)))))
           :hints(("Goal" :in-theory (enable complex-definition)))))

  (local (defthm lemma
           (implies (and (not (equal a 0))
                         (not (equal b 0))
                         (rationalp a)
                         (rationalp b))
                    (equal (+ (* a a (/ (+ (* a a) (* b b))))
                              (* b b (/ (+ (* a a) (* b b)))))
                           1))
           :hints (("goal" :use ((:instance distributivity
                                  (x (/ (+ (* a a) (* b b))))
                                  (y (* a a))
                                  (z (* b b))))
                    :in-theory (disable distributivity)))))
           ;; :hints (("goal" :use ((:instance inverse-of-*
           ;;                        (x (+ (* a a) (* b b)))))
           ;;          :in-theory (disable inverse-of-*
           ;;                              acl2::equal-*-/-2)))))
                  

  (def-gl-rewrite reciprocal-of-complex
    ;; note: the commented-out "when"s below would be helpful in the cases
    ;; where the tests can be determined to be true syntactically; otherwise
    ;; we'd prefer not to produce a case split in the symbolic result.  The
    ;; rule reciprocal-of-complex-when-real-zero below helps with the case
    ;; where real is 0; we restrict the application of this rule to cases where
    ;; that doesn't apply.
    (implies (syntaxp (not (equal real 0)))
             (equal (/ (complex real imag))
                    (b* ((imag (rfix imag))
                         (real (rfix real))
                         ;; ((when (eql imag 0)) (/ real))
                         ;; ((when (eql real 0)) (complex 0 (- (/ imag))))
                         (sq-norm (+ (* real real) (* imag imag))))
                      (complex (/ real sq-norm) (/ (- imag) sq-norm)))))
    :hints (("goal" :use ((:instance multiply-both-sides
                           (a (complex real imag))
                           (b (/ (complex real imag)))
                           (c (b* ((imag (rfix imag))
                                   (real (rfix real))
                                   (sq-norm (+ (* real real) (* imag imag))))
                                (complex (/ real sq-norm) (/ (- imag) sq-norm)))))))
            (and stable-under-simplificationp
                 '(:cases ((equal (rfix real) 0))))
            (and stable-under-simplificationp
                 '(:cases ((equal (rfix imag) 0)))))
    :otf-flg t)

  (def-gl-rewrite reciprocal-of-complex-when-real-zero
    (implies (equal (rfix real) 0)
             (equal (/ (complex real imag))
                    (complex 0 (- (/ (rfix imag))))))
    :hints (("goal" :use ((:instance reciprocal-of-complex))
             :cases ((equal (rfix imag) 0)))))



  (def-gl-rewrite rationalp-of-/
    (equal (rationalp (/ x))
           (rationalp (fix x)))
    :hints (("goal" :cases ((rationalp x)))))

  ;; (def-gl-rewrite reciprocal-of-rational-const
  ;;   (implies (and (syntaxp (and (rationalp x)
  ;;                               (not (integerp x))))
  ;;                 (rationalp x))
  ;;            (equal (/ x)
  ;;                   (* (denominator x) (/ (numerator x))))))

  ;; (def-gl-rewrite reciprocal-of-complex-const
  ;;   (implies (syntaxp (and (acl2-numberp x)
  ;;                          (not (rationalp x))))
  ;;            (equal (/ x)
  ;;                   (b* ((imag (imagpart x))
  ;;                        (real (realpart x))
  ;;                        (sq-norm (+ (* real real) (* imag imag))))
  ;;                     (complex (/ real sq-norm) (/ (- imag) sq-norm))))))

  (def-gl-rewrite integer-*-fraction
    (implies (and (syntaxp (and (rationalp b)
                                (not (integerp b))
                                (not (eql 1 (numerator b)))))
                  (integerp a)
                  (rationalp b))
             (equal (* a b)
                    (* (* a (numerator b)) (/ (denominator b))))))

  (def-gl-rewrite integer-*-consolidate
    (implies (syntaxp (and (general-integerp a)
                           (general-integerp b)))
             (equal (* a b c)
                    (* (* a b) c))))


  (def-gl-rewrite multiply-reciprocals
    (implies (syntaxp (and (general-integerp a)
                           (general-integerp b)))
             (equal (* (/ a) (/ b))
                    (/ (* a b)))))

  (def-gl-rewrite multiply-frac*recip
    (implies (and (syntaxp (and (rationalp a)
                                (not (integerp a))
                                (general-integerp b)))
                  (rationalp a))
             (equal (* a (/ b))
                    (* (numerator a) (/ (* (denominator a) b)))))
    :hints (("goal" :cases ((equal (fix b) 0)))))

  (def-gl-rewrite multiply-recip*frac
    (implies (and (syntaxp (and (rationalp a)
                                (not (integerp a))
                                (general-integerp b)))
                  (rationalp a))
             (equal (* (/ b) a)
                    (* (numerator a) (/ (* (denominator a) b))))))

  (def-gl-rewrite *-1-elim
    (equal (* 1 x) (fix x)))

  (def-gl-rewrite 1-*-elim
    (equal (* x 1) (fix x)))

  (def-gl-rewrite mult-move-reciprocal-later-1
    (implies (syntaxp (and (not (and (consp x)
                                     (eq (tag x) :g-apply)
                                     (eq (g-apply->fn x) 'unary-/)))
                           (not (and (rationalp x) (not (integerp x))))))
             (equal (* (/ y) x)
                    (* x (/ y)))))

  (def-gl-rewrite mult-move-reciprocal-later-2
    (implies (syntaxp (and (not (and (consp x)
                                     (eq (tag x) :g-apply)
                                     (eq (g-apply->fn x) 'unary-/)))
                           (not (and (rationalp x) (not (integerp x))))))
             (equal (* (/ y) x z)
                    (* x (/ y) z))))

  (def-gl-rewrite mult-move-fraction-later-1
    (implies (syntaxp (and (not (and (consp x)
                                     (eq (tag x) :g-apply)
                                     (eq (g-apply->fn x) 'unary-/)))
                           (not (and (rationalp x) (not (integerp x))))
                           (rationalp y)
                           (not (integerp y))))
             (equal (* y x)
                    (* x y))))

  (def-gl-rewrite mult-move-fraction-later-2
    (implies (syntaxp (and (not (and (consp x)
                                     (eq (tag x) :g-apply)
                                     (eq (g-apply->fn x) 'unary-/)))
                           (not (and (rationalp x) (not (integerp x))))
                           (rationalp y)
                           (not (integerp y))))
             (equal (* y x z)
                    (* x y z)))))









