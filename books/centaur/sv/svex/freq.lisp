; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "SV")
(include-book "svex")
(include-book "std/util/defines" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(local (include-book "std/alists/alist-vals" :dir :system))

(defxdoc svex-frequency-analysis
  :parents (expressions)
  :short "Analyze some @(see sv) @(see expressions) to see which shapes are
most common."

  :long "<p>These tools carry out a very simple analysis of svex expressions to
see which \"shapes\" of S-expressions are most common.  This information might
be useful when investigating how to simplify S-expressions, as in @(see
rewriting).</p>")

(local (xdoc::set-default-parents svex-frequency-analysis))

(defines svex-args-to-depth
  :parents (svex-sexpr-shape)
  :short "Gather a flat list of the sexpr's arguments, stopping at atoms and
          some maximum depth."
  :flag-local nil

  (define svex-args-to-depth ((x svex-p)
                              (depth natp))
    :returns (args-at-depth svexlist-p :rule-classes :type-prescription)
    :measure (svex-count x)
    :flag :sexpr
    (b* ((x (svex-fix x)))
      (if (zp depth)
          (list x)
        (svex-case x
          :var (list x)
          :quote (list x)
          :call (svex-args-to-depth-list x.args (- depth 1))))))

  (define svex-args-to-depth-list ((x svexlist-p) (depth natp))
    :returns (args-at-depth svexlist-p :rule-classes :type-prescription)
    :measure (svexlist-count x)
    :flag :list
    (if (atom x)
        nil
      (append (svex-args-to-depth (car x) depth)
              (svex-args-to-depth-list (cdr x) depth)))))


(defines svex-reinsert-args
  :parents (svex-sexpr-shape)
  :short "Replace the arguments with corresponding variables."
  :flag-local nil

  (define svex-reinsert-args ((x     svex-p "Sexpr to reinsert args into")
                              (vars  svarlist-p "Replacement variables.")
                              (depth natp)
                              (constsp booleanp "Elide constants?"))
    ;; Need at least enough vars to make the replacement.
    :guard (<= (len (svex-args-to-depth x depth))
               (len vars))
    :returns (mv (new-x     svex-p)
                 (rest-vars svarlist-p))
    :verify-guards nil
    :measure (svex-count x)
    :flag :sexpr
    (b* ((x    (svex-fix x))
         (vars (svarlist-fix vars))
         ((when (svex-case x :var))
          (mv (make-svex-var :name (car vars)) (cdr vars)))
         ((when (svex-case x :quote))
          ;; Elide constants only if desired
          (mv (if constsp (make-svex-var :name (car vars)) x)
              (cdr vars)))
         ((when (zp depth))
          (mv (make-svex-var :name (car vars)) (cdr vars)))
         ((mv new-x-args other-vars)
          (svex-reinsert-args-list (svex-call->args x) vars (- depth 1) constsp))
         (new-x (change-svex-call x :args new-x-args)))
      (mv new-x other-vars)))

  (define svex-reinsert-args-list ((x     svexlist-p)
                                   (vars  svarlist-p)
                                   (depth natp)
                                   (constsp booleanp))
    :returns (mv (new-x     svexlist-p)
                 (rest-vars svarlist-p))
    ;; Need at least enough vars to make the replacement.
    :guard (<= (len (svex-args-to-depth-list x depth))
               (len vars))
    :measure (svexlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv nil (svarlist-fix vars)))
         ((mv x1 vars) (svex-reinsert-args (car x) vars depth constsp))
         ((mv x2 vars) (svex-reinsert-args-list (cdr x) vars depth constsp)))
      (mv (hons x1 x2) vars)))
  ///
  (local (defthm len-of-cdr
           (equal (len (cdr x))
                  (if (consp x)
                      (+ -1 (len x))
                    0))))

  (defthm-svex-reinsert-args-flag
    (defthm len-of-svex-reinsert-args
      (b* (((mv ?new-x rest-vars) (svex-reinsert-args x vars depth constsp)))
        (equal (len rest-vars)
               (nfix (- (len vars)
                        (len (svex-args-to-depth x depth))))))
      :flag :sexpr)
    (defthm len-of-svex-reinsert-args-list
      (b* (((mv ?new-x rest-vars) (svex-reinsert-args-list x vars depth constsp)))
        (equal (len rest-vars)
               (nfix (- (len vars)
                        (len (svex-args-to-depth-list x depth))))))
      :flag :list)
    :hints(("Goal"
            :do-not '(generalize fertilize eliminate-destructors)
            :expand ((svex-reinsert-args x vars depth constsp)
                     (svex-reinsert-args-list x vars depth constsp)
                     (svex-args-to-depth x depth)
                     (svex-args-to-depth-list x depth)))))

  (verify-guards svex-reinsert-args
    :hints(("Goal"
            :expand ((svex-args-to-depth x depth)
                     (svex-args-to-depth-list x depth))))))

(define svex-elide-args
  :parents (svex-sexpr-shape)
  :short "Elide the arguments gathered by @(see svex-args-to-depth), replacing
common arguments with like symbols and standardizing the names."

  ((args  "Sexprs to elide.")
   (names "Fresh names we haven't used yet.  Typically a list of nice symbols
           like @('(a b c d ...)').  If we run out, a natural that we'll use to
           start generating bad names like @('x1, x2, ...')."
          (or (symbol-listp names)
              (natp names)))
   (seen "Fast list binding expressions we've seen to their replacement
          symbols.  We will free it when done."
         (svarlist-p (alist-vals seen))))
  :returns (elided (and (svarlist-p elided)
                        (equal (len elided) (len args))))
  (b* (((when (atom args))
        (fast-alist-free seen)
        nil)
       ((cons arg1 rest) args)
       (look (hons-get arg1 seen))
       ((when look)
        (cons (svar-fix (cdr look))
              (svex-elide-args rest names seen)))
       ((mv name1 names)
        (if (consp names)
            (mv (car names) (cdr names))
          (let ((names (nfix names)))
            (mv (intern$ (str::cat "X" (str::natstr names)) "ACL2")
                (+ 1 names)))))
       (var1 (make-svar :name name1))
       (seen (hons-acons arg1 var1 seen)))
    (cons var1 (svex-elide-args rest names seen))))


(define svex-sexpr-shape ((x svex-p)
                          &key
                          (depth natp)
                          ((elide-constsp booleanp) 't))
  :short "Summarize the shape of an S-expression down to some depth."
  :long "<p>The general idea behind @(see svex-frequency-analysis) is to count up
how many times these shapes occur throughout an S-expression.</p>"
  (b* ((args   (svex-args-to-depth x depth))
       (elided (svex-elide-args args '(a b c d e f g h i j k l m n o p q r s
                                         ;; no t because that's confusing
                                       u v w x y z) nil))
       ((mv new-x &) (svex-reinsert-args x elided depth elide-constsp)))
    new-x)
  ///
  (defthmd svex-sexpr-shape-examples
    (and (equal (svex-sexpr-shape '(and (and 0 1) (and 2 3)) :depth 1)
                '(and a b))
         (equal (svex-sexpr-shape '(and (and x y) (and w 1)) :depth 2 :elide-constsp nil)
                '(and (and a b) (and c 1)))
         (equal (svex-sexpr-shape '(and (and 0 1) (and 2 3)) :depth 2)
                '(and (and a b) (and c d)))
         (equal (svex-sexpr-shape '(and (and 0 1) (and 0 1)) :depth 2)
                '(and (and a b) (and a b)))
         (equal (svex-sexpr-shape '(and (and 0 1) (and 0 2)) :depth 2)
                '(and (and a b) (and a c))))))

(defines svex-shape-freq1
  :short "Core engine for @(see svex-frequency-analysis).  Walk through an
S-expression, summing how many times each shape occurs."

  (define svex-shape-freq1 ((x       svex-p  "SVEX to analyze.")
                            (depth   natp    "Size of shapes to consider.")
                            (seen            "FAL for sexprs we've already counted.")
                            (shapetab        "FAL binding shapes to counts.")
                            (elide-constsp booleanp))
    :returns (mv seen shapetab)
    :measure (svex-count x)
    (b* (((when (or (svex-case x :quote)
                    (svex-case x :var)))
          ;; Not going to count atoms.
          (mv seen shapetab))
         ((when (hons-get x seen))
          ;; Already counted this one.
          (mv seen shapetab))
         (seen     (hons-acons x t seen))
         (shape    (svex-sexpr-shape x :depth depth :elide-constsp elide-constsp))
         (count    (nfix (cdr (hons-get shape shapetab))))
         (shapetab (hons-acons shape (+ 1 count) shapetab)))
      (svex-shape-freq1-list (svex-call->args x) depth seen shapetab elide-constsp)))

  (define svex-shape-freq1-list ((x        svexlist-p   "SVEX list to analyze.")
                                 (depth    natp         "Size of shapes to consider.")
                                 (seen                  "FAL for sexprs we've already counted.")
                                 (shapetab              "FAL binding shapes to counts.")
                                 (elide-constsp booleanp))
    :returns (mv seen shapetab)
    :measure (svexlist-count x)
    (b* (((when (atom x))
          (mv seen shapetab))
         ((mv seen shapetab) (svex-shape-freq1 (car x) depth seen shapetab elide-constsp))
         ((mv seen shapetab) (svex-shape-freq1-list (cdr x) depth seen shapetab elide-constsp)))
      (mv seen shapetab))))

(define svex-shapefreq-clean
  :short "Clean up the shape frequencies collected by @(see svex-shape-freq1) to
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

(define svex-shape-freq ((x svex-p) &key (depth natp) ((elide-constsp booleanp) 't))
  :short "Shape frequency analysis for a single s-expression."
  :returns (report "Sorted, duplicate-free alist binding duplicity to shape.")
  (b* (((mv seen shapetab) (svex-shape-freq1 x depth nil nil elide-constsp))
       (ans (svex-shapefreq-clean shapetab)))
    (fast-alist-free seen)
    (fast-alist-free shapetab)
    ans))

(define svex-shape-freq-list ((x svexlist-p) &key (depth natp) ((elide-constsp booleanp) 't))
  :short "Shape frequency analysis for a sexpr list."
  :returns (report "Sorted, duplicate-free alist binding duplicity to shape.")
  (b* (((mv seen shapetab) (svex-shape-freq1-list x depth nil nil elide-constsp))
       (ans (svex-shapefreq-clean shapetab)))
    (fast-alist-free seen)
    (fast-alist-free shapetab)
    ans))

(define svex-shape-freq-alist ((x svex-alist-p) &key (depth natp) ((elide-constsp booleanp) 't))
  :short "Shape frequency analysis for a sexpr alist."
  :returns (report "Sorted, duplicate-free alist binding duplicity to shape.")
  (b* (((mv seen shapetab) (svex-shape-freq1-list (alist-vals x) depth nil nil elide-constsp))
       (ans (svex-shapefreq-clean shapetab)))
    (fast-alist-free seen)
    (fast-alist-free shapetab)
    ans)
  :prepwork
  ((local (defthm l0
         (implies (svex-alist-p x)
                  (svexlist-p (alist-vals x)))
         :hints(("Goal" :induct (len x)))))))






(defalist svex-refcount-alist :key-type svex :val-type natp
  ///
  (defthm natp-lookup-in-svex-refcount-alist
    (implies (svex-refcount-alist-p x)
             (iff (natp (cdr (hons-assoc-equal k x)))
                  (cdr (hons-assoc-equal k x))))
    :hints(("Goal" :in-theory (enable svex-refcount-alist-p))))

  (defthm natp-lookup-in-svex-refcount-alist-fix
    (or (natp (cdr (hons-assoc-equal k (svex-refcount-alist-fix x))))
        (not (cdr (hons-assoc-equal k (svex-refcount-alist-fix x)))))
    :rule-classes :type-prescription))

#||
(defines svex-refcounts
  :verify-guards nil
  (define svex-refcounts ((x svex-p)
                          (refcounts svex-refcount-alist-p))
    :returns (refcounts-out svex-refcount-alist-p)
    :measure (svex-count x)
    (b* ((refcounts (svex-refcount-alist-fix refcounts))
         (x (svex-fix x))
         (count-lookup (cdr (hons-get x refcounts)))
         (count (or count-lookup 0))
         (refcounts (hons-acons x (+ 1 count) refcounts))
         ((when count-lookup) refcounts))
      (svex-case x
        :call (svexlist-refcounts x.args refcounts)
        :otherwise refcounts)))
  (define svexlist-refcounts ((x svexlist-p)
                              (refcounts svex-refcount-alist-p))
    :returns (refcounts-out svex-refcount-alist-p)
    :measure (svexlist-count x)
    (b* ((refcounts (svex-refcount-alist-fix refcounts)))
      (if (atom x)
          refcounts
        (svexlist-refcounts (cdr x) (svex-refcounts (car x) refcounts)))))
  ///
  (verify-guards svex-refcounts)
  (deffixequiv-mutual svex-refcounts))


(define svex-refcounts-keep-calls ((x svex-refcount-alist-p))
  :returns (new-x svex-refcount-alist-p)
  :measure (len (svex-refcount-alist-fix x))
  (b* ((x (svex-refcount-alist-fix x)))
    (if (atom x)
        nil
      (b* ((key (caar x)))
        (svex-case key
          :call (cons (car x) (svex-refcounts-keep-calls (cdr x)))
          :otherwise (svex-refcounts-keep-calls (cdr x)))))))

(define svex-refcounts-delete-calls ((x svex-refcount-alist-p))
  :returns (new-x svex-refcount-alist-p)
  :measure (len (svex-refcount-alist-fix x))
  (b* ((x (svex-refcount-alist-fix x)))
    (if (atom x)
        nil
      (b* ((key (caar x)))
        (svex-case key
          :call (svex-refcounts-delete-calls (cdr x))
          :otherwise (cons (car x) (svex-refcounts-delete-calls (cdr x))))))))

(define svex-refcounts-delete-fncalls ((fn fnsym-p)(x svex-refcount-alist-p))
  :returns (new-x svex-refcount-alist-p)
  :measure (len (svex-refcount-alist-fix x))
  (b* ((x (svex-refcount-alist-fix x)))
    (if (atom x)
        nil
      (b* ((key (caar x)))
        (svex-case key
          :call (if (eq (fnsym-fix fn) key.fn)
                    (svex-refcounts-delete-fncalls fn (cdr x))
                  (cons (car x) (svex-refcounts-delete-fncalls fn (cdr x))))
          :otherwise (cons (car x) (svex-refcounts-delete-fncalls fn (cdr x))))))))

(defalist counter-alist :val-type natp)

(defalist svex-key-alist :key-type svex)


(defines svex-fncounts
  :verify-guards nil
  (define svex-fncounts ((x svex-p)
                         (seen svex-key-alist-p)
                         (fncounts counter-alist-p))
    :returns (mv (seen svex-key-alist-p)
                 (fncounts-out counter-alist-p))
    :measure (svex-count x)
    (b* ((fncounts (counter-alist-fix fncounts))
         (seen (svex-key-alist-fix seen))
         (x (svex-fix x)))
      (svex-case x
        :call (if (hons-get x seen)
                  (mv seen fncounts)
                (b* ((count (nfix (cdr (hons-get x.fn fncounts)))))
                  (svexlist-fncounts x.args (hons-acons x t seen)
                                     (hons-acons x.fn (+ 1 count) fncounts))))
        :otherwise (mv seen fncounts))))
  (define svexlist-fncounts ((x svexlist-p)
                             (seen svex-key-alist-p)
                             (fncounts counter-alist-p))
    :returns (mv (seen svex-key-alist-p)
                 (fncounts-out counter-alist-p))
    :measure (svexlist-count x)
    (b* ((fncounts (counter-alist-fix fncounts))
         (seen (svex-key-alist-fix seen))
         ((When (atom x)) (mv seen fncounts))
         ((mv seen fncounts) (svex-fncounts (car x) seen fncounts)))
      (svexlist-fncounts (cdr x) seen fncounts)))
  ///
  (verify-guards svex-fncounts)
  (deffixequiv-mutual svex-fncounts))
||#
