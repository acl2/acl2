; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2014 Centaur Technology
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

; sexpr-freq.lisp - analyze frequency of sexprs of certain shapes
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "sexpr-eval")
(include-book "std/util/defines" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

(defxdoc 4v-frequency-analysis
  :parents (4v-sexprs)
  :short "Analyze some @(see 4v-sexprs) to see which shapes are most common."

  :long "<p>These tools carry out a simplistic analysis of @(see 4v-sexprs) to
see which \"shapes\" of S-expressions are most common.  This information might
be useful when investigating how to simplify S-expressions, as in @(see
sexpr-rewriting).</p>")

(local (xdoc::set-default-parents 4v-frequency-analysis))

(defines 4v-args-to-depth
  :parents (4v-sexpr-shape)
  :short "Gather a flat list of the sexpr's arguments, stopping at atoms and
some maximum depth."
  :flag-local nil

  (define 4v-args-to-depth ((x "Sexpr to destructure") (depth natp))
    :returns (args-at-depth true-listp :rule-classes :type-prescription)
    :flag :sexpr
    (b* (((when (or (zp depth)
                    (atom x)))
          (list x)))
      (4v-args-to-depth-list (cdr x) (- depth 1))))

  (define 4v-args-to-depth-list ((x "Sexpr list") (depth natp))
    :returns (args-at-depth true-listp :rule-classes :type-prescription)
    :flag :list
    (if (atom x)
        nil
      (append (4v-args-to-depth (car x) depth)
              (4v-args-to-depth-list (cdr x) depth)))))

(defines 4v-reinsert-args
  :parents (4v-sexpr-shape)
  :short "Re-insert the rewritten/elided arguments back into a sexpr."

  (define 4v-reinsert-args ((x     "Sexpr to reinsert args into")
                            (depth natp)
                            (args  true-listp "Arguments to insert."))
    :returns (mv (sexpr)
                 (rest-args true-listp :hyp (true-listp args)))
    :verify-guards nil
    (b* (((when (or (zp depth)
                    (atom x)))
          (mv (car args) (cdr args)))
         ((mv new-x-args other-args)
          (4v-reinsert-args-list (cdr x) (- depth 1) args))
         (new-x (hons (car x) new-x-args)))
      (mv new-x other-args)))

  (define 4v-reinsert-args-list (x (depth natp) (args true-listp))
    :returns (mv (sexpr-list)
                 (rest-args true-listp :hyp (true-listp args)))
    (b* (((when (atom x))
          (mv x args))
         ((mv x1 args) (4v-reinsert-args (car x) depth args))
         ((mv x2 args) (4v-reinsert-args-list (cdr x) depth args)))
      (mv (hons x1 x2) args)))
  ///
  (verify-guards 4v-reinsert-args))

(assert! (b* ((x '(and (xor a (and b c)) (iff c d)))
              (depth 3)
              (args (4v-args-to-depth x depth))
              ((mv new-x &) (4v-reinsert-args x depth args)))
           (equal x new-x)))

(define 4v-elide-args
  :parents (4v-sexpr-shape)
  :short "Elide the arguments gathered by @(see 4v-args-to-depth), replacing
common arguments with like symbols and standardizing the names."

  ((args  "Sexprs to elide.")
   (names "Fresh names we haven't used yet.  Typically a list of nice symbols
           like @('(a b c d ...)').  If we run out, a natural that we'll use to
           start generating bad names like @('x1, x2, ...')."
          (or (symbol-listp names)
              (natp names)))
   (seen "Fast list binding expressions we've seen to their replacement
          symbols.  We will free it when done."))
  :returns (elided (and (symbol-listp elided)
                        (equal (len elided) (len args))))
  (b* (((when (atom args))
        (fast-alist-free seen)
        nil)
       ((cons arg1 rest) args)
       (look (hons-get arg1 seen))
       ((when look)
        (cons (symbol-fix (cdr look)) (4v-elide-args rest names seen)))
       ((mv name1 names)
        (if (consp names)
            (mv (symbol-fix (car names)) (cdr names))
          (let ((names (nfix names)))
            (mv (intern$ (str::cat "X" (str::natstr names)) "ACL2")
                (+ 1 names)))))
       (seen (hons-acons arg1 name1 seen)))
    (cons name1 (4v-elide-args rest names seen))))


(define 4v-sexpr-shape
  :short "Summarize the shape of an S-expression down to some depth."
  ((x "Sexpr to analyze") &key (depth natp))
  :long "<p>The general idea behind @(see 4v-frequency-analysis) is to count up
how many times these shapes occur throughout an S-expression.</p>"
  (b* ((args   (4v-args-to-depth x depth))
       (elided (4v-elide-args args '(a b c d e f g h i j k l m n o p q r s
                                     ;; no t because that's confusing
                                       u v w x y z) nil))
       ((mv new-x &) (4v-reinsert-args x depth elided)))
    new-x)
  ///
  (defthmd 4v-sexpr-shape-examples
    (and (equal (4v-sexpr-shape '(and (and 0 1) (and 2 3)) :depth 1)
                '(and a b))
         (equal (4v-sexpr-shape '(and (and 0 1) (and 2 3)) :depth 2)
                '(and (and a b) (and c d)))
         (equal (4v-sexpr-shape '(and (and 0 1) (and 0 1)) :depth 2)
                '(and (and a b) (and a b)))
         (equal (4v-sexpr-shape '(and (and 0 1) (and 0 2)) :depth 2)
                '(and (and a b) (and a c))))))

(defines 4v-shape-freq1
  :short "Core engine for @(see 4v-frequency-analysis).  Walk through an
S-expression, summing how many times each shape occurs."

  (define 4v-shape-freq1 ((x          "The sexpr to analyze.")
                          (depth natp "Size of shapes to consider.")
                          (seen       "FAL for sexprs we've already counted.")
                          (shapetab   "FAL binding shapes to counts."))
    :returns (mv seen shapetab)
    (b* (((when (atom x))
          ;; Not going to count atoms.
          (mv seen shapetab))
         ((when (hons-get x seen))
          ;; Already counted this one.
          (mv seen shapetab))
         (seen     (hons-acons x t seen))
         (shape    (4v-sexpr-shape x :depth depth))
         (count    (nfix (cdr (hons-get shape shapetab))))
         (shapetab (hons-acons shape (+ 1 count) shapetab)))
      (4v-shape-freq1-list (cdr x) depth seen shapetab)))

  (define 4v-shape-freq1-list ((x          "List of sexprs to analyze.")
                               (depth natp "Size of shapes to consider.")
                               (seen       "FAL for sexprs we've already counted.")
                               (shapetab   "FAL binding shapes to counts."))
    :returns (mv seen shapetab)
    (b* (((when (atom x))
          (mv seen shapetab))
         ((mv seen shapetab) (4v-shape-freq1 (car x) depth seen shapetab))
         ((mv seen shapetab) (4v-shape-freq1-list (cdr x) depth seen shapetab)))
      (mv seen shapetab))))

(define 4v-shapefreq-clean
  :short "Clean up the shape frequencies collected by @(see 4v-shape-freq1) to
turn them into a nice, readable report."
  ((shapetab "Fast alist binding shape to duplicity, not shrunk."))
  :returns (report "Sorted, duplicate-free alist binding duplicity to shape.")
  (b* ((shape->freq (hons-shrink-alist shapetab nil))
       (- (fast-alist-free shape->freq))
       (freq->shape (pairlis$ (alist-vals shape->freq)
                              ;; the extra cons makes them look nicer
                              (pairlis$ (alist-keys shape->freq)
                                        nil)))
       (low-to-high (set::mergesort freq->shape))
       (high-to-low (rev low-to-high)))
    high-to-low))

(define 4v-shape-freq (sexpr &key (depth natp))
  :short "Shape frequency analysis for a single s-expression."
  :returns (report "Sorted, duplicate-free alist binding duplicity to shape.")
  (b* (((mv seen shapetab) (4v-shape-freq1 sexpr depth nil nil))
       (ans (4v-shapefreq-clean shapetab)))
    (fast-alist-free seen)
    (fast-alist-free shapetab)
    ans))

(define 4v-shape-freq-list (sexpr-list &key (depth natp))
  :short "Shape frequency analysis for a sexpr list."
  :returns (report "Sorted, duplicate-free alist binding duplicity to shape.")
  (b* (((mv seen shapetab) (4v-shape-freq1-list sexpr-list depth nil nil))
       (ans (4v-shapefreq-clean shapetab)))
    (fast-alist-free seen)
    (fast-alist-free shapetab)
    ans))

(define 4v-shape-freq-alist (sexpr-alist &key (depth natp))
  :short "Shape frequency analysis for a sexpr alist."
  :returns (report "Sorted, duplicate-free alist binding duplicity to shape.")
  (b* (((mv seen shapetab) (4v-shape-freq1-list (alist-vals sexpr-alist) depth nil nil))
       (ans (4v-shapefreq-clean shapetab)))
    (fast-alist-free seen)
    (fast-alist-free shapetab)
    ans))
