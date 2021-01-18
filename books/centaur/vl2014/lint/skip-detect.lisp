; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "../mlib/ctxexprs")
(include-book "../mlib/print-context")
(include-book "../util/cwtime")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))



; BOZO it seems tricky to implement with the current way the code is written,
; but it would be nice if we could NOT mention skipped wires that occur on
; the LHS of an assignment, e.g.,
;
;    assign foo5 = foo0 | foo1 | foo2 | foo3 | foo4;
;
; Is pretty unlikely to be a skipped wire.  This causes some noise in a couple
; of modules.


(defthm take-leading-dec-digit-chars-under-iff
  ;; BOZO consider moving to string library
  (iff (str::take-leading-dec-digit-chars x)
       (str::dec-digit-char-p (car x)))
  :hints(("Goal" :in-theory (enable str::take-leading-dec-digit-chars))))



(defxdoc skip-detection
  :parents (lint)
  :short "We try to detect missing signals from expressions."

  :long "<p>Related wires often have similar names, e.g., in one module we
found wires with names like @('bcL2RB0NoRtry_P'), @('bcL2RB1NoRtry_P'), and so
on, up to @('bcL2RB7NoRtry_P').  Such signals might sometimes be combined later
on, e.g., we later found:</p>

@({
assign bcL2NoRtry_P = bcL2RB7NoRtry_P | bcL2RB6NoRtry_P
                    | bcL2RB5NoRtry_P | bcL2RB4NoRtry_P
                    | bcL2RB3NoRtry_P | bcL2RB2NoRtry_P
                    | bcL2RB1NoRtry_P | bcL2RB0NoRtry_P;
})

<p>Skip detection pertains to expressions like the above.  In short, it would
be pretty odd if @('bcL2RB4NoRtry_P') been omitted (\"skipped\") in the above
expression, or if say @('bcL2RB3NoRtry_P') occurred more than once.  We try to
detect such situations.</p>

<p>Note that some expressions might involve more than one group of these
kind of signals.  For instance, we found:</p>

@({
assign bcNxtWCBEntSrc_P =
   bcDataSrcLd_P ? ({3{bcWCB0DBSYQual_P}} & bcWCB0Ent_P)
                 | ({3{bcWCB1DBSYQual_P}} & bcWCB1Ent_P)
                 | ({3{bcWCB2DBSYQual_P}} & bcWCB2Ent_P)
                 | ({3{bcWCB3DBSYQual_P}} & bcWCB3Ent_P)
                 | ({3{bcWCB4DBSYQual_P}} & bcWCB4Ent_P)
                 | ({3{bcWCB5DBSYQual_P}} & bcWCB5Ent_P)
                 : bcWCBEntSrc_P;
})

<p>We try to also detect skipped signals in these kinds of expressions.</p>")

(local (xdoc::set-default-parents skip-detection))

(defaggregate sd-key
  :tag :sd-key
  :layout :fulltree
  :short "Keys are derived from wire names and are the basis of our skip
          detection."

  ((pat stringp :rule-classes :type-prescription
        "The same as the wire name except that some embedded number (perhaps
         spanning many digits) may have been replaced by a @('*') character.")

   (index maybe-natp :rule-classes :type-prescription
          "The parsed value of the number that has been replaced, or @('nil')
           if no replacement was made.")

   (orig stringp :rule-classes :type-prescription
         "The original wire name.  This is somewhat unnecessary since it can be
          recovered by just replacing @('*') in @('pat') with the characters
          for @('index'), but we thought it was convenient to keep around"))

  :long "<p>The idea of keys is to cause related signals to have the same
pattern.  For instance, @('bcWCB0Ent_P') and @('bcWCB1Ent_P') will both give
rise to the pattern @('bcWCB*Ent_P').</p>

<p>Because a particular wire name might include many numbers, we may generate a
list of keys for a single wire.  For instance, for @('bcL2RB1NoRtry_P') we will
generate one key with the pattern @('bcL*RB1NoRtry_P') and another with the
pattern @('bcL2RB*NoRtry_P').  We had previously considered using a list of
indices, but found it easier to just generate multiple keys, each with a single
index.</p>")

(deflist sd-keylist-p (x)
  (sd-key-p x)
  :guard t)

(defprojection sd-keylist->indicies (x)
  (sd-key->index x)
  :guard (sd-keylist-p x))


(defsection sd-keygen
  :short "@(call sd-keygen) derives a list of @(see sd-key-p)s from @('x'), a
wire name, and accumulates them into @('acc')."

  (defund sd-keygen-aux (n x xl acc)
    (declare (xargs :guard (and (natp n)
                                (natp xl)
                                (stringp x)
                                (= xl (length x))
                                (sd-keylist-p acc))
                    :measure (nfix (- (length (string-fix x)) (nfix n)))))
    (b* ((n  (lnfix n))
         (x  (mbe :logic (string-fix x) :exec x))
         (xl (mbe :logic (length x) :exec xl))
         ((when (>= n xl))
          ;; No more numbers, just generate the empty-indexed pattern.
          (let* ((x-honsed (hons-copy x))
                 (key      (make-sd-key :pat x-honsed :index nil :orig x-honsed)))
            (cons key acc)))
         (char (char x n))
         ((unless (str::dec-digit-char-p char))
          (sd-keygen-aux (+ 1 n) x xl acc))
         ;; Else, we found a number.
         ((mv val len) (str::parse-nat-from-string x 0 0 n xl))
         (prefix       (subseq x 0 n))
         (suffix       (subseq x (min xl (+ n len)) nil))
         (pat          (cat prefix "*" suffix))
         (key          (make-sd-key :pat (hons-copy pat)
                                    :index val
                                    :orig x)))
        (sd-keygen-aux (+ len n) x xl (cons key acc))))

  (local (in-theory (enable sd-keygen-aux)))

  (local (defthm sd-keylist-p-of-sd-keygen-aux
           (implies (sd-keylist-p acc)
                    (sd-keylist-p (sd-keygen-aux n x xl acc)))))

  (defund sd-keygen (x acc) ;; String --> Key List
    (declare (xargs :guard (and (stringp x)
                                (sd-keylist-p acc))))
    (sd-keygen-aux 0 x (length x) acc))

  (defthm sd-keylist-p-of-sd-keygen
    (implies (force (sd-keylist-p acc))
             (sd-keylist-p (sd-keygen x acc)))
    :hints(("Goal" :in-theory (enable sd-keygen))))

  (defund sd-keygen-list (x acc) ;; String list --> Key List
    (declare (xargs :guard (and (string-listp x)
                                (sd-keylist-p acc))))
    (if (atom x)
        acc
      (let ((acc (sd-keygen (car x) acc)))
        (sd-keygen-list (cdr x) acc))))

  (defthm sd-keylist-p-of-sd-keygen-list
    (implies (force (sd-keylist-p acc))
             (sd-keylist-p (sd-keygen-list x acc)))
    :hints(("Goal" :in-theory (enable sd-keygen-list)))))



(defsection sd-patalist-p
  :short "@(call sd-patalist-p) recognizes alists that bind strings to @(see
sd-keylist-p)s."

  (defund sd-patalist-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        t
      (and (consp (car x))
           (stringp (caar x))
           (sd-keylist-p (cdar x))
           (sd-patalist-p (cdr x)))))

  (local (in-theory (enable sd-patalist-p)))

  (defthm sd-patalist-p-when-not-consp
    (implies (not (consp x))
             (equal (sd-patalist-p x)
                    t)))

  (defthm sd-patalist-p-of-cons
    (equal (sd-patalist-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (sd-keylist-p (cdr a))
                (sd-patalist-p x))))

  (defthm sd-keylist-p-of-cdr-of-hons-assoc-equal-when-sd-patalist-p
    (implies (force (sd-patalist-p x))
             (sd-keylist-p (cdr (hons-assoc-equal a x)))))

  (defthm sd-patalist-p-of-hons-shrink-alist
    (implies (and (sd-patalist-p x)
                  (sd-patalist-p y))
             (sd-patalist-p (hons-shrink-alist x y)))
    :hints(("Goal" :in-theory (enable (:i hons-shrink-alist))))))



(defsection sd-patalist
  :short "@(call sd-patalist) separates a @(see sd-keylist-p) by their
patterns, producing a @(see sd-patalist-p)."

  :long "<p>We return a fast alist which has no shadowed pairs.</p>"

  (defund sd-patalist-aux (x acc)
    (declare (xargs :guard (and (sd-keylist-p x)
                                (sd-patalist-p acc))))
    (if (atom x)
        acc
      (let* ((key   (car x))
             (pat   (sd-key->pat key))
             (entry (cdr (hons-get pat acc)))
             (acc   (hons-acons pat (cons key entry) acc)))
        (sd-patalist-aux (cdr x) acc))))

  (local (in-theory (enable sd-patalist-aux)))

  (defthm alistp-of-sd-patalist-aux
    (implies (alistp acc)
             (alistp (sd-patalist-aux x acc))))

  (defthm sd-patalist-p-of-sd-patalist-aux
    (implies (and (force (sd-keylist-p x))
                  (force (sd-patalist-p acc)))
             (sd-patalist-p (sd-patalist-aux x acc))))

  (defund sd-patalist (x)
    (declare (xargs :guard (sd-keylist-p x)))
    (b* ((unclean (sd-patalist-aux x nil))
         (clean   (hons-shrink-alist unclean nil))
         (-       (flush-hons-get-hash-table-link unclean)))
        clean))

  (local (in-theory (enable sd-patalist)))

  (defthm sd-patalist-p-of-sd-patalist
    (implies (force (sd-keylist-p x))
             (sd-patalist-p (sd-patalist x))))

  (defthm alistp-of-sd-patalist
    (alistp (sd-patalist x))))


(defaggregate sd-problem
  :tag :sd-problem
  :layout :fulltree
  :short "An alleged problem noticed by skip detection."
  ((type symbolp :rule-classes :type-prescription
         "What kind of problem this is.  At the moment the type is always
          @(':skipped') and means that we think some wire is suspiciously
          skipped. But we imagine that we could add other kinds of analysis
          that look, e.g., for wires that are oddly duplicated, etc., and hence
          have other types.")

   (priority natp :rule-classes :type-prescription
             "A heuristic score that we give to problems to indicate how likely
              they are to be a real problem.  For instance, we assign extra
              priority to a sequence of wires like @('foo1'), @('foo2'),
              @('foo4'), @('foo5') because the skipped wire is in the middle.
              We also might assign extra priority if one of the other wires is
              duplicated.")

   (groupsize natp :rule-classes :type-prescription
              "Says how many wires had this same pattern.  We generally think
               that the larger the group size is, the more likely the problem
               is to be legitimate.")

   (key sd-key-p "The @(see sd-key-p) for the missing wire.")

   (ctx vl-context1-p "Says where this problem originates.")))

(deflist sd-problemlist-p (x)
  (sd-problem-p x)
  :elementp-of-nil nil)

(define sd-problem-score ((x sd-problem-p))
  :returns (score natp :rule-classes :type-prescription)
  (b* (((sd-problem x) x)
       (elem (vl-context1->elem x.ctx))
       (elem-score (cond ((eq (tag elem) :vl-assign) 1)
                         ((eq (tag elem) :vl-always) -1)
                         ((eq (tag elem) :vl-initial) -1)
                         (t 0)))
       (gs-score (cond ((< x.groupsize 4) -1)
                       ((< x.groupsize 5) 0)
                       ((< x.groupsize 8) 3)
                       ((< x.groupsize 10) 4)
                       (t 5)))
       (score (+ x.priority gs-score elem-score)))
      (nfix score)))

(define sd-problem->
  :short "Basic ordering on skip-detect problems."
  ((x sd-problem-p)
   (y sd-problem-p))
  (> (sd-problem-score x)
     (sd-problem-score y))
  ///
  (defthm sd-problem->-transitive
    (implies (and (sd-problem-> x y)
                  (sd-problem-> y z))
             (sd-problem-> x z))))

(acl2::defsort
 :comparablep sd-problem-p
 :compare< sd-problem->
 :prefix sd-problem)

(defthm sd-problem-list-p-removal
  (equal (sd-problem-list-p x)
         (sd-problemlist-p x))
  :hints(("Goal" :in-theory (enable sd-problem-list-p sd-problemlist-p))))

(defthm sd-problemlist-p-of-sd-problem-sort
  (implies (sd-problemlist-p x)
           (sd-problemlist-p (sd-problem-sort x)))
  :hints(("Goal"
          :in-theory (disable SD-PROBLEM-SORT-CREATES-COMPARABLE-LISTP)
          :use ((:instance SD-PROBLEM-SORT-CREATES-COMPARABLE-LISTP
                           (acl2::x x))))))



(define sd-natlist-linear-increments-p ((x nat-listp))
  "One reason we might bump the priority is if the wires are linearly
   progressing and we're missing one in the middle."
  (cond ((atom x)
         t)
        ((atom (cdr x))
         t)
        (t
         (and (equal (+ 1 (first x)) (second x))
              (sd-natlist-linear-increments-p (cdr x))))))

(define sd-keylist-linear-increments-p ((x sd-keylist-p))
  (let ((indicies (sd-keylist->indicies x)))
    (and (nat-listp indicies)
         (sd-natlist-linear-increments-p indicies))))





(define sd-keylist-find-skipped
  :short "Perform skip-detection for a single pattern within an expression."
  ((x sd-keylist-p)
   (y sd-keylist-p)
   (ctx vl-context1-p))
  :returns (prob? (equal (sd-problem-p prob?) (if prob? t nil))
                  :hyp :fguard)

  :long "<p>We expect that all of the keys in @('x') and @('y') have the same
pattern.  In practice, assuming the original wire names are free of @('*')
characters, this means that all keys throughout @('x') and @('y') should differ
only by their indices.  More specifically, our expectation here is that the
keys in @('x') have been generated from the wires in some particular
expression, while the keys in @('y') were generated by looking at the entire
module.</p>

<p>Our goal is to investigate whether this expression uses \"all but one\" of
the wires of this pattern.  That is, it would be suspicious for @('x') to
mention all of foo1, foo2, foo3, and foo5, but not foo4.  If there are a lot of
wires in @('x') and @('y'), then this is a very easy comparison.  The hard
cases are when there aren't very many wires in the first place.</p>

<p>If there is only one wire that matches this pattern, then there are only two
cases -- the expression mentions the wire or it doesn't -- and neither of these
cases are suspicious.</p>

<p>If there are only two wires that share this pattern, then we might use none,
one, or both of them, and none of these cases are suspicious.</p>

<p>If there are three wires that share this pattern, and we only use two of
them, then this is starting to get slightly suspicious.  We'll go ahead and
flag it.</p>

<p>Beyond that point, if we find that exactly one wire is missing, we flag it
with an @('alarm') level equal to the number of wires that match the pattern.
In other words, the alarm level is somehow like a confidence indicator that
says how suspicious this omission is -- it's not too suspicious to omit one out
of three wires, but it's really suspicious to omit one out of ten.</p>"

  :prepwork ((local (defthm consp-when-len-gt-0
                      (implies (< 0 (len x))
                               (consp x)))))

  :guard-hints (("goal" :in-theory (disable acl2::set-equiv-implies-equal-consp-1
                                            set::difference-under-set-equiv)
                 :do-not-induct t))

  (b* ((ys (mergesort y))
       (yl (len ys))
       ((unless (> yl 2))
        nil)
       (xs (mergesort x))
       (missing  (difference ys xs))
       (nmissing (len missing))
       ((unless (= nmissing 1))
        nil)
       ;; Extra priority will be assigned if the keys of Y are linear
       ;; increments and the one we are missing is in the middle!
       (linearp     (sd-keylist-linear-increments-p ys))
       (idx-min     (sd-key->index (car ys)))
       (idx-max     (sd-key->index (car (last ys))))
       (idx-missing (sd-key->index (car missing)))
       (middlep     (and linearp
                         (natp idx-min)
                         (natp idx-max)
                         (natp idx-missing)
                         (< idx-min idx-missing)
                         (< idx-missing idx-max)))

       ;; Another reason we might bump the priority is if the wires are all
       ;; mentioned with duplicity 1 except that one is duplicated.  This
       ;; might be something like foo1, foo2, foo2, foo4, foo5.  We know
       ;; there is exactly one wire missing, so if there is exactly one
       ;; duplicate, the len of X will be the len of YS.
       (dupep       (same-lengthp x ys))

       (priority    (cond ((and middlep dupep)
                           10)
                          (middlep
                           6)
                          (dupep
                           4)
                          (linearp
                           2)
                          (t
                           1))))
    (make-sd-problem :type :skipped
                     :priority priority
                     :groupsize yl
                     :key (car missing)
                     :ctx ctx)))

(define sd-patalist-compare
  :short "Perform skip-detection for a single expression."
  ((dom "In practice, this is the @(see strip-cars) of @('x').  That is, it is
         the list of all pattern names that were found in the expression, and
         which we need to investigate.")
   (x sd-patalist-p "The pattern produced for some particular expression.")
   (y sd-patalist-p "The global @(see sd-patalist-p) that we assume was
                     produced for the entire module.")
   (ctx vl-context1-p "Where this expression came from."))
  :returns (probs sd-problemlist-p :hyp :fguard)
  :long "<p>We recur over @('dom').  For each pattern named in the expression,
we use @(see sd-keylist-find-skipped) to try to find any skipped wires,
collecting any problems that have been reported.</p>"
  (if (atom dom)
      nil
    (let ((first (sd-keylist-find-skipped (cdr (hons-get (car dom) x))
                                          (cdr (hons-get (car dom) y))
                                          ctx))
          (rest  (sd-patalist-compare (cdr dom) x y ctx)))
      (if first
          (cons first rest)
        rest))))

(defsection sd-analyze-ctxexprs
  :short "Perform skip-detection for a list of expressions."

  :long "<p><b>Signature:</b> @(call sd-analyze-ctxexprs) returns a list of
@(see sd-problem-p)s.</p>

<ul>

<li>@('ctxexprs') is an @(see vl-exprctxalist-p) that associates expressions
with their contexts.  Generally we expect that this alist includes every
expression in a module.</li>

<li>@('global-pats') is the @(see sd-patalist-p) that was constructed for all
names in the module, which is needed by @(see sd-patalist-compare).</li>

</ul>

<p>We just call @(see sd-patalist-compare) for every expression in
@('ctxexprs') and combine the results.</p>"

  (defund sd-analyze-ctxexprs (ctxexprs global-pats)
    (declare (xargs :guard (and (vl-exprctxalist-p ctxexprs)
                                (sd-patalist-p global-pats))))
    (if (atom ctxexprs)
        nil
      (b* ((expr       (caar ctxexprs))
           (ctx        (vl-context1-fix (cdar ctxexprs)))
           (expr-names (vl-expr-names expr))
           (expr-keys  (sd-keygen-list expr-names nil))
           (expr-pats  (sd-patalist expr-keys))
           (dom        (strip-cars expr-pats))
           (report1    (sd-patalist-compare dom expr-pats global-pats ctx))
           (-          (flush-hons-get-hash-table-link expr-pats)))
          (append report1
                  (sd-analyze-ctxexprs (cdr ctxexprs) global-pats)))))

  (local (in-theory (enable sd-analyze-ctxexprs)))

  (defthm true-listp-of-sd-analyze-ctxexprs
    (true-listp (sd-analyze-ctxexprs ctxexprs global-pats))
    :rule-classes :type-prescription)

  (defthm sd-problemlist-p-of-sd-analyze-ctxexprs
    (implies (and (force (vl-exprctxalist-p ctxexprs))
                  (force (sd-patalist-p global-pats)))
             (sd-problemlist-p (sd-analyze-ctxexprs ctxexprs global-pats)))))




(defthm vl-exprlist-p-of-alist-keys-when-vl-exprctxalist-p
  (implies (vl-exprctxalist-p x)
           (vl-exprlist-p (alist-keys x)))
  :hints(("Goal" :induct (len x))))

(define sd-analyze-module-aux
  :short "Collect all the problems."
  ((x vl-module-p))
  :returns (probs sd-problemlist-p :hyp :fguard "Not sorted yet.")
  (b* (;;(modname (vl-module->name x))
       ;;(- (cw "Analyzing ~s0.~%" modname))
       (ctxexprs  (cwtime (vl-module-ctxexprs x)
                          :mintime 1/2
                          :name sd-harvest-ctxexprs))

       ;; BOZO is all-names sufficient?  Should we perhaps also collect all
       ;; declared wire names, in case they aren't ever used in an expression?

       (all-names (cwtime (vl-exprlist-names (alist-keys ctxexprs))
                          :mintime 1/2
                          :name sd-extract-names))
       (all-keys  (cwtime (mergesort (sd-keygen-list all-names nil))
                          :mintime 1/2
                          :name sd-make-global-keys))
       (global-pats (cwtime (sd-patalist all-keys)
                            :mintime 1/2
                            :name sd-make-global-pats))
       (report (cwtime (sd-analyze-ctxexprs ctxexprs global-pats)
                       :mintime 1/2
                       :name sd-analyze-ctxexprs)))
    (fast-alist-free global-pats)
    report))

(define sd-analyze-module
  :short "Perform skip-detection on a module."
  ((x vl-module-p))
  :returns (probs sd-problemlist-p :hyp :fguard "Sorted in priority order.")
  (sd-problem-sort (sd-analyze-module-aux x))
  ///
  (defthm true-listp-of-sd-analyze-module
    (true-listp (sd-analyze-module x))
    :rule-classes :type-prescription))


(define sd-analyze-modulelist-aux ((x vl-modulelist-p))
  :returns (probs sd-problemlist-p :hyp :fguard "Not sorted yet.")
  (if (atom x)
      nil
    (append (sd-analyze-module-aux (car x))
            (sd-analyze-modulelist-aux (cdr x)))))

(define sd-analyze-modulelist
  :short "Perform skip-detection on a module list."
  ((x vl-modulelist-p))
  :returns (probs sd-problemlist-p :hyp :fguard "Sorted in priority order.")
  (b* ((analyze (cwtime (sd-analyze-modulelist-aux x)
                        :name sd-analyze-modulelist-aux
                        :mintime 1))
       (sort    (cwtime (sd-problem-sort analyze)
                        :name sd-analyze-modulelist-sort
                        :mintime 1/2)))
    sort)
  ///
  (defthm true-listp-of-sd-analyze-modulelist
    (true-listp (sd-analyze-modulelist x))
    :rule-classes :type-prescription))


(define sd-analyze-design
  :short "Top level skip-detection for a design."
  ((x vl-design-p))
  :returns (probs sd-problemlist-p "Sorted in priority order.")
  (b* ((x (vl-design-fix x))
       (mods (vl-design->mods x)))
    (sd-analyze-modulelist mods)))


; Pretty-printing results

(define sd-pp-problem-header ((x sd-problem-p) &key (ps 'ps))
  (b* (((sd-problem x) x)
       ((sd-key x.key) x.key)
       (modname (vl-context1->mod x.ctx))
       (htmlp (vl-ps->htmlp)))
    (vl-ps-seq
     (if htmlp
         (vl-print-markup "<dt>")
       (vl-print "  "))
     (vl-print "Is ")
     (vl-print-ext-wirename modname x.key.orig)
     (vl-print " accidentally skipped? ")
     (vl-ps-span "sd_detail"
                 (vl-print "(score ")
                 (vl-print (sd-problem-score x))
                 (vl-print ", pat ")
                 (vl-print x.key.pat)
                 (vl-print ", priority ")
                 (vl-print x.priority)
                 (vl-print ", groupsize ")
                 (vl-print x.groupsize)
                 (vl-print ")"))
     (if htmlp
         (vl-println-markup "</dt>")
       (vl-println "")))))

(define sd-pp-problem-brief ((x sd-problem-p) &key (ps 'ps))
  (b* (((sd-problem x) x)
       (htmlp (vl-ps->htmlp)))
    (vl-ps-seq
     (sd-pp-problem-header x)
     (if htmlp
         (vl-print-markup "<dd class=\"sd_context\">")
       (vl-indent 2))
     (vl-println (vl-context-summary x.ctx))
     (if htmlp
         (vl-println-markup "</dd>")
       (vl-println "")))))

(define sd-pp-problemlist-brief ((x sd-problemlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (sd-pp-problem-brief (car x))
               (sd-pp-problemlist-brief (cdr x)))))

(defun vl-pp-context-modest (x)
  (declare (xargs :guard (vl-context1-p x)))
  (let ((full (with-local-ps (vl-pp-ctxelement-full (vl-context1->elem x)))))
    (if (< (length full) 230)
        full
      (cat (subseq full 0 230) "..." *nls*))))


(define sd-pp-problem-long ((x sd-problem-p) &key (ps 'ps))
  (b* (((sd-problem x) x)
       (modname (vl-context1->mod x.ctx))
       (loc (vl-ctxelement->loc (vl-context1->elem x.ctx))))
    (if (not (vl-ps->htmlp))
        ;; Plain text
        (vl-ps-seq
         (vl-print "In ")
         (vl-print-modname modname)
         (vl-print " (")
         (vl-print-loc loc)
         (vl-println ")")
         (sd-pp-problem-header x)
         (vl-indent 2)
         (vl-println "")
         (vl-print (vl-pp-context-modest x.ctx))
         (vl-println "")
         (vl-println ""))
      ;; HTML mode
      (vl-ps-seq
       (vl-println-markup "<dl class=\"sd_prob\">")
       (sd-pp-problem-header x)
       (vl-print-markup "<dt class=\"sd_loc\">")
       (vl-print "In ")
       (vl-print-modname modname)
       (vl-print " at ")
       (vl-print-loc loc)
       (vl-println-markup "</dt>")
       (vl-print-markup "<dd class=\"sd_context\">")
       (vl-print (vl-pp-context-modest x.ctx))
       (vl-println-markup "</dd>")
       (vl-println-markup "</dl>")
       ))))

(define sd-pp-problemlist-long ((x sd-problemlist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (sd-pp-problem-long (car x))
               (sd-pp-problemlist-long (cdr x)))))
