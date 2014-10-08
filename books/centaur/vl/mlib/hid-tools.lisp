; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "expr-tools")
(include-book "range-tools")
(include-book "../util/sum-nats")
(local (include-book "../util/arithmetic"))
(local (in-theory (enable tag-reasoning)))
(local (std::add-default-post-define-hook :fix))

(local (defthm equal-of-cons-rewrite
         (equal (equal x (cons a b))
                (and (consp x)
                     (equal (car x) a)
                     (equal (cdr x) b)))))


(defxdoc hid-tools
  :parents (mlib)
  :short "Functions for working with hierarchical identifiers."

  :long "<p>Here are some examples of hierarchical identifiers:</p>

@({
    foo.bar[3].baz          // Verilog-2005 or SystemVerilog-2012
    foo.bar[3][4].baz       // SystemVerilog-2012
})

<p>VL internally represents hierarchical identifiers as compound @(see
vl-expr-p) objects.  We expect to represent the above expressions as
follows:</p>

@({
            .                     .
           / \\                   / \\
       foo    .               foo   .
             / \\                   / \\
           []   baz               []  baz
          /  \\                   /  \\
       bar    3                 []   4
                               /  \\
                             bar   3
})

<p>Where each @('.') represents a @(':vl-hid-dot') operator, each @('[]')
represents a @(':vl-index') operator, and the names are represented as @(see
vl-hidpiece-p) atoms.</p>

<p>The generic @(see vl-expr-p) representation is really too weak, and by
itself it would permit nonsensical expressions like @('foo.5.bar.(1+2)'), which
should never be produced by our parser or by well-behaving internal VL code.
Instead, the function @(see vl-hidexpr-p) provides a stronger check to ensure
that an expression is a well-formed hierarchical identifier that meets our
usual expectations.</p>

<p>Note that @(see vl-hidexpr-p) does <b>not</b> restrict in any way the
expressions may occur in the index positions.  For instance, there is a valid
@('vl-hidexpr-p') that represents @('foo.bar[3+a*b].baz').  In practice,
complex indexing expressions might occasionally arise due to parameterized
modules.  Once everything settles down, you can check whether all of the
indexes in a hidexpr have been resolved to constants using @(see
vl-hidexpr-resolved-p).</p>

<p>The raw expression format can be cumbersome to work with.  Once you have
gotten down to resolved @(see vl-hidexpr-p)s, you can translate them into plain
list of names (strings) and indices (naturals) using @(see
vl-explode-hid).</p>")

(local (xdoc::set-default-parents hid-tools))

(define vl-hidname-p ((x vl-expr-p))
  :returns (bool)
  :short "Recognizes  simple name expression: either a hidpiece or an id."
  (and (vl-fast-atom-p x)
       (b* (((vl-atom x) x))
         (or (vl-fast-hidpiece-p x.guts)
             (vl-fast-id-p x.guts))))
  ///
  (defthm vl-hidname-p-when-vl-idexpr-p
    (implies (vl-idexpr-p x)
             (vl-hidname-p x))
    :hints(("Goal" :in-theory (enable vl-idexpr-p))))

  (defthm vl-hidname-p-when-vl-atom
    (implies (and (vl-atom-p x)
                  (or (vl-hidpiece-p (vl-atom->guts x))
                      (vl-id-p (vl-atom->guts x))))
             (vl-hidname-p x))))

(define vl-hidname->name ((x vl-expr-p))
  :prepwork ((local (in-theory (enable vl-hidname-p))))
  :guard (vl-hidname-p x)
  :returns (name stringp :rule-classes :type-prescription)
  (b* (((vl-atom x)))
    (if (vl-fast-hidpiece-p x.guts)
        (vl-hidpiece->name x.guts)
      (vl-id->name x.guts))))
       


(define vl-hidindex-p ((x vl-expr-p))
  :returns (bool)
  :short "Recognizes well-formed index expressions into hierarchical
identifiers, e.g., the @('bar[3][4][5]') part of @('foo.bar[3][4][5].baz')."

  :long "<p>We match left-associated trees of indices that ultimately end with
a @(see vl-hidpiece-p).  We don't restrict the actual index expressions, e.g.,
an expression such as @('bar[width-1]') is acceptable.</p>"
  :measure (vl-expr-count x)

  (if (vl-fast-atom-p x)
      (vl-hidname-p x)
    (b* (((vl-nonatom x) x))
      (and (eq x.op :vl-index)
           (vl-hidindex-p (first x.args)))))
  ///
  (defthm vl-hidname-p-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (vl-atom-p x))
             (vl-hidname-p x)))

  (defthmd vl-nonatom->op-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (force (not (vl-atom-p x))))
             (equal (vl-nonatom->op x) :vl-index))
    :rule-classes ((:rewrite) (:forward-chaining)))

  (defthm arity-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (force (not (vl-atom-p x))))
             (equal (vl-op-arity (vl-nonatom->op x)) 2)))

  (defthm len-of-vl-nonatom->args-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (force (not (vl-atom-p x))))
             (and ;; blah, so gross....
              (equal (len (vl-nonatom->args x)) 2)
              (consp (vl-nonatom->args x))
              (consp (cdr (vl-nonatom->args x))))))

  (deffixequiv vl-hidindex-p)

  (defthm vl-hidindex-p-of-make-vl-atom
    (equal (vl-hidindex-p (make-vl-atom :guts guts
                                        :finalwidth finalwidth
                                        :finaltype finaltype))
           (or (vl-hidpiece-p (vl-atomguts-fix guts))
               (vl-id-p (vl-atomguts-fix guts))))
    :hints(("Goal" :in-theory (enable vl-hidname-p))))

  (defthm vl-hidindex-p-of-make-vl-nonatom
    (implies (force (vl-hidindex-p (first args)))
             (vl-hidindex-p (make-vl-nonatom :op :vl-index
                                             :args args
                                             :atts atts
                                             :finalwidth finalwidth
                                             :finaltype finaltype)))
    :hints(("Goal"
            :in-theory (enable vl-arity-fix)
            :expand ((:free (atts args finalwidth finaltype)
                      (vl-hidindex-p
                       (make-vl-nonatom :op :vl-index
                                        :args args
                                        :atts atts
                                        :finalwidth finalwidth
                                        :finaltype finaltype)))))))

  (defthm not-vl-hidindex-p-by-op
    (implies (and (not (eq (vl-nonatom->op x) :vl-index))
                  (force (not (vl-atom-p x))))
             (not (vl-hidindex-p x)))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-hidindex-p-of-first-of-vl-nonatom->args-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidindex-p (first (vl-nonatom->args x))))))

(local (in-theory (enable vl-nonatom->op-when-vl-hidindex-p)))



(define vl-hidexpr-p ((x vl-expr-p))
  :returns (bool)
  :short "Recognizes well-formed hierarchical identifier expressions."
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (vl-hidname-p x))
       ((vl-nonatom x) x)
       ((when (eq x.op :vl-hid-dot))
        (and (vl-hidindex-p (first x.args))
             (vl-hidexpr-p (second x.args)))))
    (vl-hidindex-p x))
  ///
  (defthm vl-hidexpr-p-when-vl-hidindex-p
    (implies (vl-hidindex-p x)
             (vl-hidexpr-p x))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-hidpiece-p-of-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (vl-atom-p x))
             (vl-hidname-p x)))

  (defthm vl-nonatom->op-when-vl-hidexpr-p-forward
    (implies (and (vl-hidexpr-p x)
                  (not (vl-atom-p x)))
             (or (equal (vl-nonatom->op x) :vl-index)
                 (equal (vl-nonatom->op x) :vl-hid-dot)))
    :rule-classes :forward-chaining)

  (defthm not-vl-hidexpr-p-by-op
    (implies (and (not (eq (vl-nonatom->op x) :vl-hid-dot))
                  (not (eq (vl-nonatom->op x) :vl-index))
                  (force (not (vl-atom-p x))))
             (not (vl-hidexpr-p x))))

  (defthm vl-op-arity-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (equal (vl-op-arity (vl-nonatom->op x))
                    2))
    :hints(("Goal"
            :cases ((equal (vl-nonatom->op x) :vl-hid-dot)
                    (equal (vl-nonatom->op x) :vl-index)))))

  (defthm len-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x)))
                  (force (vl-expr-p x)))
             (and ;; blah, so gross....
              (equal (len (vl-nonatom->args x)) 2)
              (consp (vl-nonatom->args x))
              (consp (cdr (vl-nonatom->args x))))))

  (defthm vl-hidindex-p-of-first-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidindex-p (first (vl-nonatom->args x)))))

  (defthm vl-hidexpr-p-of-second-of-vl-nonatom->args-when-vl-hidexpr-p
    (implies (and (equal (vl-nonatom->op x) :vl-hid-dot)
                  (vl-hidexpr-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidexpr-p (second (vl-nonatom->args x)))))

  (local (defthm vl-id-p-of-vl-atomguts-fix
           (equal (vl-id-p (vl-atomguts-fix x))
                  (vl-id-p x))
           :hints(("Goal" :in-theory (e/d (vl-atomguts-fix
                                           vl-atomguts-p)
                                          (tag-when-vl-constint-p))
                   :use ((:instance tag-when-vl-constint-p
                          (x (vl-constint-fix x))))))))

  (local (defthm vl-hidpiece-p-of-vl-atomguts-fix
           (equal (vl-hidpiece-p (vl-atomguts-fix x))
                  (vl-hidpiece-p x))
           :hints(("Goal" :in-theory (e/d (vl-atomguts-fix
                                           vl-atomguts-p)
                                          (tag-when-vl-constint-p))
                   :use ((:instance tag-when-vl-constint-p
                          (x (vl-constint-fix x))))))))

  (defthm vl-hidexpr-p-of-vl-atom
    (equal (vl-hidexpr-p (make-vl-atom :guts guts
                                       :finalwidth finalwidth
                                       :finaltype finaltype))
           (or (vl-hidpiece-p guts)
               (vl-id-p guts)))
    :hints(("goal" :in-theory (enable vl-hidname-p))))

  (defthm vl-hidexpr-p-of-vl-nonatom-dot
    (implies (and (equal op :vl-hid-dot)
                  (force (vl-hidindex-p (first args)))
                  (force (vl-hidexpr-p (second args))))
             (vl-hidexpr-p (make-vl-nonatom :op op
                                            :args args
                                            :atts atts
                                            :finalwidth finalwidth
                                            :finaltype finaltype)))
    :hints(("Goal"
            :in-theory (enable vl-arity-fix)
            :expand ((:free (args atts finalwidth finaltype)
                      (vl-hidexpr-p
                       (make-vl-nonatom :op :vl-hid-dot
                                        :args args
                                        :atts atts
                                        :finalwidth finalwidth
                                        :finaltype finaltype)))))))

  (defthm vl-hidexpr-p-of-vl-nonatom-index
    (implies (and (equal op :vl-index)
                  (force (vl-hidindex-p (first args))))
             (vl-hidexpr-p (make-vl-nonatom :op op
                                            :args args
                                            :atts atts
                                            :finalwidth finalwidth
                                            :finaltype finaltype))))

  (defthm vl-hidindex-p-when-vl-hidexpr-p
    (implies (vl-hidexpr-p x)
             (equal (vl-hidindex-p x)
                    (or (vl-atom-p x)
                        (not (eq (vl-nonatom->op x) :vl-hid-dot)))))
    :hints(("Goal" :in-theory (enable vl-hidindex-p))))

  (defthm vl-hidexpr-p-when-id-atom
    (implies (and (equal (vl-expr-kind x) :atom)
                  (vl-id-p (vl-atom->guts x)))
             (vl-hidexpr-p x))))



(define vl-hidindex-resolved-p ((x vl-expr-p))
  :guard (vl-hidindex-p x)
  :returns (bool)
  :short "Determines if every index in a @(see vl-hidindex-p) is resolved."
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        t)
       ((vl-nonatom x) x))
    (and (mbt (eq x.op :vl-index))
         (vl-hidindex-resolved-p (first x.args))
         (vl-expr-resolved-p (second x.args))))
  ///
  (defthm vl-hidindex-resolved-p-when-atom
    (implies (vl-atom-p x)
             (vl-hidindex-resolved-p x)))

  (deffixequiv vl-hidindex-resolved-p)

  (defthm vl-hidindex-resolved-p-of-make-vl-nonatom
    (implies (and (force (vl-hidindex-resolved-p (first args)))
                  (force (vl-expr-resolved-p (second args))))
             (vl-hidindex-resolved-p (make-vl-nonatom :op :vl-index
                                                      :args args
                                                      :atts atts
                                                      :finalwidth finalwidth
                                                      :finaltype finaltype)))
    :hints(("Goal"
            :in-theory (e/d (vl-arity-fix) ((force)))
            :expand ((:free (atts args finalwidth finaltype)
                      (vl-hidindex-resolved-p (make-vl-nonatom :op :vl-index
                                                               :args args
                                                               :atts atts
                                                               :finalwidth finalwidth
                                                               :finaltype finaltype)))))))

  (defthmd vl-nonatom->op-when-hidindex-resolved-p
    (implies (and (vl-hidindex-resolved-p x)
                  (force (not (vl-atom-p x))))
             (equal (vl-nonatom->op x) :vl-index)))

  (defthm vl-hidindex-resolved-p-of-arg1-when-vl-hidindex-resolved-p
    (implies (and (vl-hidindex-resolved-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidindex-resolved-p (first (vl-nonatom->args x)))))

  (defthm vl-expr-resolved-p-of-arg2-when-vl-hidindex-resolved-p
    (implies (and (vl-hidindex-resolved-p x)
                  (force (not (vl-atom-p x))))
             (vl-expr-resolved-p (second (vl-nonatom->args x))))))



(define vl-hidexpr-resolved-p ((x vl-expr-p))
  :guard (vl-hidexpr-p x)
  :prepwork ((local (in-theory (enable vl-nonatom->op-when-hidindex-resolved-p))))
  :returns (bool)
  :short "Determines if every index throughout a @(see vl-hidexpr-p) is resolved."
  :guard-debug t
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x)) t)
       ((vl-nonatom x) x)
       ((when (eq x.op :vl-hid-dot))
        (and (vl-hidindex-resolved-p (first x.args))
             (vl-hidexpr-resolved-p (second x.args)))))
    (vl-hidindex-resolved-p x))
  ///
  (defthm vl-hidexpr-resolved-p-when-atom
    (implies (vl-atom-p x)
             (vl-hidexpr-resolved-p x)))

  (defthm vl-hidindex-resolved-p-of-arg1-when-vl-hidexpr-resolved-p
    (implies (and (equal (vl-nonatom->op x) :vl-hid-dot)
                  (vl-hidexpr-resolved-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidindex-resolved-p (first (vl-nonatom->args x)))))

  (defthm vl-hidexpr-resolved-p-of-arg2-when-vl-hidexpr-resolved-p
    (implies (and (equal (vl-nonatom->op x) :vl-hid-dot)
                  (vl-hidexpr-resolved-p x)
                  (force (not (vl-atom-p x))))
             (vl-hidexpr-resolved-p (second (vl-nonatom->args x)))))

  (defthm vl-hidexpr-resolved-p-of-make-vl-nonatom-for-index
    (implies (and (force (vl-hidindex-resolved-p (first args)))
                  (force (vl-expr-resolved-p (second args))))
             (vl-hidexpr-resolved-p (make-vl-nonatom :op :vl-index
                                                     :args args
                                                     :atts atts
                                                     :finalwidth finalwidth
                                                     :finaltype finaltype)))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-hidexpr-resolved-p-of-make-vl-nonatom-for-dot
    (implies (and (force (vl-hidindex-resolved-p (first args)))
                  (force (vl-hidexpr-resolved-p (second args))))
             (vl-hidexpr-resolved-p (make-vl-nonatom :op :vl-hid-dot
                                                     :args args
                                                     :atts atts
                                                     :finalwidth finalwidth
                                                     :finaltype finaltype)))
    :hints(("Goal"
            :expand (:free (atts args finalwidth finaltype)
                      (vl-hidexpr-resolved-p (make-vl-nonatom :op :vl-hid-dot
                                                              :args args
                                                              :atts atts
                                                              :finalwidth finalwidth
                                                              :finaltype finaltype)))
            :in-theory (e/d (vl-arity-fix) ((force))))))

  (defthm vl-hidindex-resolved-p-when-vl-hidexpr-resolved-p
    (implies (vl-hidexpr-resolved-p x)
             (equal (vl-hidindex-resolved-p x)
                    (or (vl-atom-p x)
                        (not (equal (vl-nonatom->op x) :vl-hid-dot)))))))


(define vl-hidindex->name ((x vl-expr-p))
  :guard (vl-hidindex-p x)
  :returns (name stringp :rule-classes :type-prescription)
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (vl-hidname->name x))
       ((vl-nonatom x) x))
    (vl-hidindex->name (first x.args))))

(define vl-hid-final-name ((x vl-expr-p))
  :guard (vl-hidexpr-p x)
  :returns (name stringp :rule-classes :type-prescription)
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x)) (vl-hidname->name x))
       ((vl-nonatom x) x)
       ((when (eq x.op :vl-hid-dot))
        (vl-hid-final-name (second x.args))))
    (vl-hidindex->name x)))

(define vl-flatten-hidindex ((x vl-expr-p))
  :guard (and (vl-hidindex-p x)
              (vl-hidindex-resolved-p x))
  :returns (flat-string stringp :rule-classes :type-prescription)
  :short "Converts a @(see vl-hidindex-p) into a string like
@('\"bar[3][4][5]\"')."
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (vl-hidname->name x))
       ((vl-nonatom x) x))
    (cat (vl-flatten-hidindex (first x.args))
         "["
         (str::natstr (vl-resolved->val (second x.args)))
         "]")))

(define vl-flatten-hidexpr ((x vl-expr-p))
  :guard (and (vl-hidexpr-p x)
              (vl-hidexpr-resolved-p x))
  :returns (flat-string stringp :rule-classes :type-prescription)
  :short "Converts a hierarchical identifier expression into a string like
@('foo.bar[3][4][5].baz')."
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x)) (vl-hidname->name x))
       ((vl-nonatom x) x)
       ((when (eq x.op :vl-hid-dot))
        (cat (vl-flatten-hidindex (first x.args))
             "."
             (vl-flatten-hidexpr (second x.args)))))
    (vl-flatten-hidindex x)))

(define vl-explode-hidindex
  :short "Explode a (resolved) @(see vl-hidindex-p) into a flat list of
          its components."
  ((x vl-expr-p "The hidindex to explode, e.g., @('foo[3][4][5]')"))
  :guard (and (vl-hidindex-p x)
              (vl-hidindex-resolved-p x))
  :returns (pieces true-listp :rule-classes :type-prescription
                   "A flat, mixed list of strings and numbers, e.g.,
                   @('(\"foo\" 3 4 5)').")
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (list (vl-hidname->name x)))
       ((vl-nonatom x) x)
       (from (vl-explode-hidindex (first x.args)))
       (idx  (vl-resolved->val (second x.args))))
    (append from (list idx))))

(define vl-explode-hid
  :short "Explode a (resolved) @(see vl-hidexpr-p) into a flat list of its
          components."
  ((x vl-expr-p "The hidexpr to explode, e.g., foo.bar[2][3].baz."))
  :guard (and (vl-hidexpr-p x)
              (vl-hidexpr-resolved-p x))
  :returns
  (pieces true-listp :rule-classes :type-prescription
          "A flat, mixed list of strings and numbers, e.g.,
           @('(\"foo\" \"bar\" 2 3 \"baz\")').")
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (list (vl-hidname->name x)))
       ((vl-nonatom x) x)
       ((when (eq x.op :vl-hid-dot))
        (append (vl-explode-hidindex (first x.args))
                (vl-explode-hid (second x.args)))))
    (vl-explode-hidindex x)))

(define vl-hid-range
  :short "Try to look up a range for a HID, which may have been installed by
@(see vl-expr-follow-hids)."
 ((x vl-expr-p  "This should generally be the top-level HID expression."))
 :guard (not (vl-atom-p x))
 :returns (mv (successp booleanp :rule-classes :type-prescription)
              (range vl-maybe-range-p
                     :hints(("Goal" :in-theory (disable (force))))))
  (b* ((atts (vl-nonatom->atts x))
       ((unless (assoc-equal "VL_HID_RESOLVED_RANGE_P" atts))
        (mv nil nil))
       (left  (cdr (assoc-equal "VL_HID_RESOLVED_RANGE_LEFT" atts)))
       (right (cdr (assoc-equal "VL_HID_RESOLVED_RANGE_RIGHT" atts)))
       ((when (and (not left) (not right)))
        ;; It's resolved, there's just no range.
        (mv t nil))
       ((unless (and left right))
        ;; Maybe this should be a programming error?
        (mv nil nil))
       ;; Dumb hackery for unconditional return theorem
       (left (mbe :logic (if (vl-expr-p left)
                             left
                           (vl-make-index 0))
                  :exec left))
       (right (mbe :logic (if (vl-expr-p right)
                              right
                            (vl-make-index 0))
                   :exec right))
       (range (make-vl-range :msb left :lsb right)))
    (mv t range))
  ///
  (defthm vl-hid-range-of-copy-atts
    (equal (vl-hid-range (vl-nonatom op (vl-nonatom->atts x) args fw ft))
           (vl-hid-range x))))

(define vl-hid-rangeatts
  :short "Extend the attributes for a HID with range information."
  ;; BOZO we should probably be using this in vl-expr-follow-hids.
  ((range vl-maybe-range-p)
   (atts vl-atts-p "the rest of the atts"))
  :guard (vl-maybe-range-resolved-p range)
  :returns (new-atts vl-atts-p)
  (b* ((atts (vl-atts-fix atts))
       (atts (if range
                 (list* (cons "VL_HID_RESOLVED_RANGE_LEFT" (vl-range->msb range))
                        (cons "VL_HID_RESOLVED_RANGE_RIGHT" (vl-range->lsb range))
                        atts)
               (list* (cons "VL_HID_RESOLVED_RANGE_LEFT" nil)
                      (cons "VL_HID_RESOLVED_RANGE_RIGHT" nil)
                      atts))))
    (cons (list "VL_HID_RESOLVED_RANGE_P") atts))
  ///
  (defthm vl-hid-range-of-vl-hid-rangeatts
    (implies range
             (equal (vl-hid-range (vl-nonatom op (vl-hid-rangeatts range atts) args fw ft))
                    (mv t (vl-range-fix range))))
    :hints(("Goal" :in-theory (e/d (vl-hid-range))))))

(define vl-hid-width
  :short "Try to return the width of a HID, using range attribute information
that may have been installed by @(see vl-expr-follow-hids)."
  ((x vl-expr-p))
  :guard (not (vl-atom-p x))
  :enabled t
  :guard-hints (("goal" :in-theory (enable vl-hid-range
                                           vl-maybe-range-resolved-p
                                           vl-maybe-range-size
                                           vl-range-resolved-p
                                           vl-range-size
                                           vl-width-from-difference
                                           )))
  :returns (width maybe-posp :rule-classes :type-prescription)
  (mbe :logic (b* (((mv ok range) (vl-hid-range x)))
                (and ok
                     (vl-maybe-range-resolved-p range)
                     (vl-maybe-range-size range)))
       :exec
       (b* ((atts (vl-nonatom->atts x))
            ((unless (assoc-equal "VL_HID_RESOLVED_RANGE_P" atts))
             nil)
            (left (cdr (assoc-equal "VL_HID_RESOLVED_RANGE_LEFT" atts)))
            (right (cdr (assoc-equal "VL_HID_RESOLVED_RANGE_RIGHT" atts)))
            ((unless (or (and (not left) (not right))
                         (and left (vl-expr-resolved-p left)
                              right (vl-expr-resolved-p right))))
             nil))
         (if left
             (vl-width-from-difference
              (- (vl-resolved->val left) (vl-resolved->val right)))
           1))))




(local (defthm vl-packeddimensionlist-fix-of-append
         (equal (vl-packeddimensionlist-fix (append a b))
                (append (vl-packeddimensionlist-fix a)
                        (vl-packeddimensionlist-fix b)))
         :hints(("Goal" :in-theory (enable append)))))





(define vl-usertype-resolve ((x vl-datatype-p)
                             (ss vl-scopestack-p)
                             (rec-limit natp))
  :guard (eq (vl-datatype-kind x) :vl-usertype)
  :short "Resolves a datatype of usertype kind to a concrete
datatype, i.e. anything but a user typename.  Not recursive."
  :long "<p>Always returns a datatype; however, in various failure cases, it
may still be a usertype.  Returns a scopestack suffix representing the scope in
which the typedef was found.</p>


@({
  typedef logic [3:0] mynibble;
  typedef mynibble [7:0] my32;
  typedef my32 [0:3] membank [63:0];
  // error: since membank now has unpacked dims, we can't give it more packed dims:
  // typedef membank [3:0] memchunk;
  // this works:
  typedef membank memchunk [3:0];
 })

<p>Suppose we are asked to resolve the memchunk type.  We first recur through
the typdefs to the definition of mynibble, which is a coretype of logic with a
packed dims entry of [3:0].</p>

<p>Then we pop up to where we are considering the definition of my32.  Here we
add [7:0] to the packed dimesions of the datatype.  This is ok since logic is an ok
type for packed dimensions and we don't have any unpacked dimensions yet.</p>

<p>When we get to membank we add [0:3] as another packed dimension, but now we
return [63:0] as an additional unpacked dimension not attached to the datatype.</p>

<p>If memchunk had a packed dimension in its definition as in the commented-out
version, we'd fail because now we have unpacked dimensions so we can't add more
packed ones.  However, it's fine to add more unpacked dimensions.</p>

<p>Also returns the scopestack representing the scope in which the final type
declaration was found.</p>"
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type vl-datatype-p)
               (scope vl-scopestack-p))
  :measure (nfix rec-limit)
  :verify-guards nil
  (b* ((ss (vl-scopestack-fix ss))
       (x (vl-datatype-fix x))
       ((vl-usertype x))
       ((when (zp rec-limit))
        (mv (make-vl-warning :type :vl-resolve-usertypes-fail
                             :msg "Rec-limit ran out: recursively defined ~
                                       datatype? ~a0"
                             :args (list x.kind))
            x ss))
       ((unless (vl-idexpr-p x.kind))
        (mv (make-vl-warning :type :vl-resolve-usertypes-fail
                             :msg "We don't yet support usertypes that are ~
                                   not simple identifiers: ~a0"
                             :args (list x.kind))
            x ss))
       (name (vl-idexpr->name x.kind))
       ((mv item new-ss)
        (vl-scopestack-find-item/ss name ss))
       ((unless item)
        (mv (make-vl-warning :type :vl-resolve-usertypes-fail
                             :msg "No typedef found for ~a0"
                             :args (list x.kind))
            x ss))
       ((unless (eq (tag item) :vl-typedef))
        (mv (make-vl-warning :type :vl-resolve-usertypes-fail
                             :msg "Didn't find a typedef ~a0, instead ~
                                       found ~a1"
                             :args (list x.kind item))
            x ss))
       ((vl-typedef item))
       ((mv warning subtype final-ss)
        (if (eq (vl-datatype-kind item.type) :vl-usertype)
            (vl-usertype-resolve item.type new-ss (1- rec-limit))
          (mv nil item.type new-ss)))
       ((when warning)
        (mv warning x ss))
       (sub-udims (vl-datatype->udims subtype))
       ((when (and (consp x.pdims) (consp x.udims)))
        ;; Bad case: we have unpacked dimensions from the inner call but
        ;; we're trying to add packed ones.  Warn and return x.
        (mv (make-vl-warning :type :vl-usertype-packed-dims
                             :msg "Usertype ~s0 was declared with packed ~
                                       dimensions, but its definition already ~
                                       has unpacked dimensions."
                             :args (list x))
            x ss))
       (subtype (mbe :logic (vl-datatype-update-dims
                             (append-without-guard x.pdims (vl-datatype->pdims subtype))
                             (append-without-guard x.udims sub-udims)
                             subtype)
                     :exec
                     (if (or x.udims x.pdims)
                         (vl-datatype-update-dims
                          (append-without-guard x.pdims (vl-datatype->pdims subtype))
                          (append-without-guard x.udims sub-udims)
                          subtype)
                       subtype))))
    (mv nil subtype final-ss))
  ///

  (verify-guards vl-usertype-resolve))


(defines vl-datatype-usertype-elim
  :verify-guards nil
  (define vl-datatype-usertype-elim ((x vl-datatype-p)
                                         (ss vl-scopestack-p)
                                         (reclimit natp))
    :measure (two-nats-measure reclimit (vl-datatype-count x))
    :returns (mv (warning (iff (vl-warning-p warning) warning))
                 (type vl-datatype-p))
    (b* ((x (vl-datatype-fix x)))
      (vl-datatype-case x
        :vl-coretype (mv nil x)
        :vl-enum (mv nil x) ;; bozo 
        :vl-usertype
        (b* (((mv warning newx newss) (vl-usertype-resolve x ss 100))
             ((when warning) (mv warning newx))
             ((when (zp reclimit))
              (mv (make-vl-warning :type :vl-datatype-usertype-elim-fail
                                   :msg "Recursion limit ran out: ~a0"
                                   :args (list x.kind))
                  newx)))
          (vl-datatype-usertype-elim newx newss (1- reclimit)))
        :vl-struct
        (b* (((mv warning members) (vl-structmembers-usertype-elim x.members ss reclimit))
             (newx (change-vl-struct x :members members)))
          (mv warning newx))
        :vl-union
        (b* (((mv warning members) (vl-structmembers-usertype-elim x.members ss reclimit))
             (newx (change-vl-union x :members members)))
          (mv warning newx)))))
  (define vl-structmembers-usertype-elim ((x vl-structmemberlist-p)
                                              (ss vl-scopestack-p)
                                              (reclimit natp))
    :measure (two-nats-measure reclimit (vl-structmemberlist-count x))
    :returns (mv (warning (iff (vl-warning-p warning) warning))
                 (newx vl-structmemberlist-p))
    (b* (((when (atom x)) (mv nil nil))
         ((mv warning type1) (vl-datatype-usertype-elim
                              (vl-structmember->type (car x)) ss reclimit))
         (first (change-vl-structmember (car x) :type type1))
         ((when warning) (mv warning (cons first (vl-structmemberlist-fix (cdr x)))))
         ((mv warning membs2) (vl-structmembers-usertype-elim (cdr x) ss reclimit)))
      (mv warning (cons first membs2))))
  ///
  (verify-guards vl-datatype-usertype-elim))
          
    
  

(define vl-datatype->structmembers ((x vl-datatype-p))
  :short "Finds the struct members of x when it is a struct or union."
  :returns (mv ok (members vl-structmemberlist-p))
  (vl-datatype-case x
    :vl-struct (mv t x.members)
    :vl-union  (mv t x.members)
    :otherwise (mv nil nil)))
  
(define vl-find-structmember ((name stringp) (membs vl-structmemberlist-p))
  :returns (memb (iff (vl-structmember-p memb) memb))
  (if (atom membs)
      nil
    (if (equal (string-fix name) (vl-structmember->name (car membs)))
        (vl-structmember-fix (car membs))
      (vl-find-structmember name (cdr membs)))))


(define vl-hidexpr-first-index ((x vl-expr-p))
  :guard (vl-hidexpr-p x)
  :returns (first (and (vl-expr-p first)
                       (implies (vl-hidexpr-p x)
                                (vl-hidindex-p first)))
                  :hints(("Goal" :expand ((vl-hidexpr-p x)))))
  (if (and (not (vl-fast-atom-p x))
           (eq (vl-nonatom->op x) :vl-hid-dot))
      (first (vl-nonatom->args x))
    (vl-expr-fix x)))

(define vl-hidexpr-dot-p ((x vl-expr-p))
  :guard (vl-hidexpr-p x)
  :returns (dotp)
  (and (not (vl-fast-atom-p x))
       (eq (vl-nonatom->op x) :vl-hid-dot)))

(define vl-hidexpr-rest ((x vl-expr-p))
  :guard (and (vl-hidexpr-p x)
              (vl-hidexpr-dot-p x))
  :prepwork ((local (in-theory (enable vl-hidexpr-dot-p))))
  :returns (rest (and (vl-expr-p rest)
                      (implies (and (vl-hidexpr-p x)
                                    (vl-hidexpr-dot-p x))
                               (vl-hidexpr-p rest))))
  (vl-expr-fix (second (vl-nonatom->args x)))
  ///
  (defthm vl-expr-count-of-vl-hidexpr-rest
    (implies (vl-hidexpr-dot-p x)
             (< (vl-expr-count (vl-hidexpr-rest x))
                (vl-expr-count x)))
    :rule-classes :linear))

(define vl-hidindex-count-indices ((x vl-expr-p))
  :guard (vl-hidindex-p x)
  :measure (vl-expr-count x)
  :returns (idxcount natp :rule-classes :type-prescription)
  (if (vl-fast-atom-p x)
      0
    (+ 1 (vl-hidindex-count-indices (first (vl-nonatom->args x))))))

(define vl-hidindex-datatype-resolve-dims ((x vl-expr-p)
                                           (type vl-datatype-p))
  :short "Given a hidindex expression, e.g. foo[5][3], and the datatype and
unpacked dimensions corresponding to foo, return the datatype and unpacked
dimensions corresponding to the whole expression."
  :long "<p>Note: we don't check whether indices are in bounds or anything,
just whether the number of indices is less than or equal the number of
total (unpacked plus packed) dimensions.</p>

<p>We produce a non-fatal warning because we're not sure in what contexts this
will be used.</p>

<p>Example: Suppose our datatype is from a typedef</p>
@({ typedef bit [3:0] [4:2] foo [0:6] [0:8]; }

<p>that is, it has one unpacked dimension @('[0:6]') and two packed dimensions.
Suppose our expression is @('bar[5][7][2]'), where bar is of type foo.  Then we
should return @('bit[4:2]') as our resolved datatype, with no packed
dimensions, because the first two indices correspond to the unpacked dimension
and the second to the first packed dimension.  On the other hand if we had
@('bar[5]'), we should return @('bit[3:0][4:2]') as the type and @('[0:8]') as
the remaining unpacked dimensions.</p>"
  :guard (vl-hidindex-p x)
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type1 (iff (vl-datatype-p type1) (not warning))))
  (b* ((idxcount (vl-hidindex-count-indices x))
       (type (vl-datatype-fix type))
       (x (vl-expr-fix x))
       (unpacked-dims (vl-datatype->udims type))
       (packed-dims (vl-datatype->pdims type))
       (nunpacked (len unpacked-dims))
       ((when (<= idxcount nunpacked))
        (mv nil (vl-datatype-update-udims
                 (nthcdr idxcount (redundant-list-fix unpacked-dims)) type)))
       (remaining-idxcount (- idxcount nunpacked))
       ((unless (<= remaining-idxcount (len packed-dims)))
        (mv (make-vl-warning :type :vl-too-many-indices
                             :msg "Too many indices on expression ~a0 ~
                                   relative to dimensions of type ~a1 (with ~
                                   ~x2 additional unpacked dimensions)."
                             :args (list x type (len unpacked-dims)))
            nil))
       (type (vl-datatype-update-dims
              (nthcdr remaining-idxcount (redundant-list-fix packed-dims))
              nil ;; udims
              type)))
    (mv nil type)))


;; Have a HID, and know (for the base name) the type (unresolved) and unpacked
;; dims.

;; Resolve the type.
;; If the hid is an ID, return the type and dims.

;; Resolve the indices of the base part against the unpacked/packed dims.  If we
;; end up still having dims remaining, fail.

;; If the type is not a struct or union type, fail.

;; Find the next name in the HID among the structmembers.  If not found, fail.

;; Recur with the rest of the HID and the type/unpacked dims of the member.


(define vl-hidexpr-traverse-datatype ((x vl-expr-p)
                                      (type vl-datatype-p))
  :parents (hid-tools)
  :short "Given a dotted expression that indexes into a datatype, find the type of the expression."
  :long " <p>A helpful invariant to remember when thinking about this function:
The type and unpacked dimensions of a given call of this function belong to the
base (leftmost) variable in the HID.</p>

<p>Also note: the datatype should be fully usertype-resolved, as by
vl-datatype-usertype-elim.</p>

<p>BOZO Rewrite this documentation under the new assumption that the datatypes
are pre-resolved.</p>

<p>Example: Suppose we have the following type declarations</p>
@({
 typedef struct packed { logic [3:0] foo; } [4:0] foostruct;
 typedef union { foostruct [5:0] bar; logic [2:0] baz; } bunion [0:6];
 typedef struct { bunion fa [0:8], logic [1:0] ba; } bstruct;
 bstruct myvar [8:0];
 )}

<p>For this example, we'll write a type with both packed an unpacked dimensions
with an underscore between the packed and unpacked dims.</p>

<p>A bunion is a type consisting of an unpacked array of 7 elements
each of which may either be a packed array of 6 foostructs (a packed structure
containing one 4-bit logic field) or a 3-bit logic; a bstruct is a struct
containing an unpacked array of 9 bunions and an additional 2-bit logic field;
and myvar is an unpacked array of 9 bstructs.</p>

<p>Suppose our expression is @('myvar[1].fa[8][4].bar[3][4].foo').</p>

<ul>

<li>First, before calling this function we look up the type of myvar.  We get a
vardecl, which has a type @('bstruct _ [8:0]'). Then we're ready to run.</li>

<li>Outermost call: We resolve the type bstruct to its struct definition.  We
cancel our index with the single array dimension, leaving just the struct.  We
find the element fa inside the struct, and
recur on the remainder of our expression, @('fa[8][4].bar[3][4].foo'), with the
structmember's type, @('bunion _ [0:8]').</li>

<li> We resolve the bunion type to the union, and append the unpacked
dimensions of the type and the element to get @('[0:8][0:6]').  We then check
the indices from the expression against this type and unpacked dimensions,
which results in just the bare union type (the definition of bunion, but
without its unpacked dimension @('[0:6]')).  We find the element bar inside the
union and recur: @('bar[3][4].foo'), type @('foostruct[5:0]').</li>

<li> We resolve the type foostruct to its struct type, and append the packed
dimensions to get @('[5:0][4:0]').  We then check the indices from the
expression, which results in cancelling out the dimension to obtain just the
bare struct.  We find the element foo of the struct and recur on that.</li>

<li>Finally, we have just the atom @('foo') as our expression, so we return the
type @('logic[3:0]').</li> </ul>"
  :guard (vl-hidexpr-p x)
  :measure (vl-expr-count x)
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (restype (iff (vl-datatype-p restype) (not warning))))
  ;; Resolve the type and dims.
  (b* ((type (vl-datatype-fix type))
       ((unless (vl-hidexpr-dot-p x))
        ;; We have at just an ID.  Return the resolved type.
        (mv nil type))

       ;; Cancel the indices of the first element of the HID with the unpacked
       ;; and packed dims of the type.
       (idx1 (vl-hidexpr-first-index x))
       ((mv warning baretype)
        (vl-hidindex-datatype-resolve-dims idx1 type))
       ((when warning) (mv warning nil))
       ((when (or (consp (vl-datatype->udims baretype))
                  (consp (vl-datatype->pdims baretype))))
        (mv (make-vl-warning :type :vl-hid-datatype-fail
                             :msg "Not enough indices in dotted selector ~a0: ~
                                   extra ~s1 dimensions."
                             :args (list
                                    (vl-expr-fix x)
                                    (if (consp (vl-datatype->udims baretype))
                                        "unpacked" "packed")))
            nil))
       
       ;; Next we're going to dot-index into the datatype, so get its
       ;; structmembers, making sure it's a struct.
       ((mv ok members) (vl-datatype->structmembers baretype))
       ((unless ok)
        (mv (make-vl-warning :type :vl-hid-datatype-fail
                             :msg "Dot-indexing into a datatype that isn't a ~
                                   struct or union: ~a0"
                             :args (list (vl-datatype-fix baretype)))
            nil))

       ;; Look up the member corresponding to the next name in the hid.
       (next-hid (vl-hidexpr-rest x))
       (nextname (vl-hidindex->name (vl-hidexpr-first-index next-hid)))
       (member (vl-find-structmember nextname members))
       ((unless member)
        (mv (make-vl-warning :type :vl-structindex-fail
                             :msg "Dot-indexing failed: struct/union member ~
                                   ~s0 not found in type ~a1"
                             :args (list nextname (vl-datatype-fix baretype)))
            nil))
       (membtype (vl-structmember->type member)))
    (vl-hidexpr-traverse-datatype next-hid membtype)))


(define vl-hidexpr-find-type ((x vl-expr-p)
                              (ss vl-scopestack-p))
  :parents (hid-tools)
  :short "Looks up a HID in a scopestack and looks for a declaration, returning the type and dimensionlist if found."
  :guard (vl-hidexpr-p x)
  :measure (vl-expr-count x)
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type (iff (vl-datatype-p type) (not warning))))
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (vl-module-p x)
                               (vl-scope-p x)))))
  (b* ((idx1 (vl-hidexpr-first-index x))
       (name1 (vl-hidindex->name idx1))
       ((mv item new-ss)
        (vl-scopestack-find-item/ss name1 ss))
       ((unless item)
        (mv (make-vl-warning :type :vl-hidexpr-type-fail
                             :msg "Couldn't find an item named ~s0"
                             :args (list name1))
            nil))
       ((when (eq (tag item) :vl-modinst))
        ;; Find the module, push it onto the new scopestack, recur
        (b* (((unless (vl-hidexpr-dot-p x))
              (mv (make-vl-warning :type :vl-hidexpr-type-fail
                                   :msg "Can't find a type for ~s0 because it ~
                                         is a modinst name"
                                   :args (list name1))
                  nil))
             ((unless (vl-fast-atom-p idx1))
              (mv (make-vl-warning :type :vl-hidexpr-type-fail
                                   :msg "Indexing into instance arrays not ~
                                         yet supported: ~a0"
                                   :args (list (vl-expr-fix x)))
                  nil))
             ((vl-modinst item))
             ((mv mod new-ss)
              (vl-scopestack-find-definition/ss item.modname new-ss))
             ((unless (and mod (eq (tag mod) :vl-module)))
              (mv (make-vl-warning :type :vl-hidexpr-type-fail
                                   :msg "Module ~s0 not found for module ~
                                         instance ~s1"
                                   :args (list item.modname item.instname))
                  nil))
             (new-ss (vl-scopestack-push mod new-ss)))
          (vl-hidexpr-find-type (vl-hidexpr-rest x) new-ss)))

       ((when (eq (tag item) :vl-vardecl))
        ;; check its datatype
        (b* (((vl-vardecl item))
             ((mv warning res-type)
              (vl-datatype-usertype-elim item.type new-ss 1000))
             ((when warning) (mv warning nil)))
          (vl-hidexpr-traverse-datatype x res-type))))

    (mv (make-vl-warning :type :vl-hidexpr-type-fail
                         :msg "Looking up ~s0: item type not supported: ~s1~%"
                         :args (list name1 (tag item)))
        nil)))



(define vl-packeddimensionlist-total-size ((x vl-packeddimensionlist-p))
  :short "Given a packeddimensionlist like [5:0][3:1][0:8], multiplies the
dimensions together to get the total number of bits, or returns nil on
failure."
  :returns (size maybe-posp :rule-classes :type-prescription)
  (b* (((when (atom x)) 1)
       (rest (vl-packeddimensionlist-total-size (cdr x)))
       ((unless rest) nil)
       (first (vl-packeddimension-fix (car x)))
       ((when (eq first :vl-unsized-dimension)) nil)
       ((unless (vl-range-resolved-p first)) nil))
    (* (vl-range-size first) rest)))









(define vl-datatype-range
  :short "Get the range, if any, for a data type."
  :long "<p>The datatype should be fully resolved, and the unpacked dimensions
passed separately, as in the output from @(see
vl-datatype-usertype-elim).</p>

<p>What exactly do we mean by the range of a datatype?  Most data types can
have multiple array dimensions.  What we mean is the range of indices that are
valid to apply directly to the data structure: that is, the range of the
\"first\" array dimension.  This means: the leftmost unpacked dimension if
there are unpacked dimensions; otherwise the leftmost packed dimension,
otherwise nil.  When types are composed, e.g. by declaring a type to be another
type with some additional dimensions, the additional dimensions go to the left.
Examples:</p>

@({
 typedef logic [3:0] nibble;
 typedef nibble [7:0] quadword [1:0];
 typedef quadword cacheline [15:0];
 })
<p>These are equivalent to:</p>
@({
 typedef logic [3:0] nibble;
 typedef logic [7:0] [3:0] quadword [1:0];
 typedef logic [7:0] [3:0] cacheline [15:0] [1:0];
 })

<p>A tricky part here is that a variable declaration's datatype doesn't
necessarily include all of the unpacked array dimensions.  In the declaration
of my_kbyte, the type of my_kbyte is dword but it has additional dimensions
stored in the variable declaration itself.  So we take as an extra argument the
unpacked dimensions of the datatype.  If there are any unpacked dimensions,
then the first unpacked dimension is transformed into the range; otherwise,
it's the first packed dimension (or the declared range of a net type)."
  ((x vl-datatype-p))
  :returns
  (mv (warning (iff (vl-warning-p warning) warning))
      (range  vl-maybe-range-p
              "On success: the range of this datatype."))
  (b* (((fun (fail msg args)) 
        (mv (make-vl-warning :type :vl-datatype-range-fail
                             :msg msg
                             :args args)
            nil))
       ((fun (success range)) (mv nil range))
       (x (vl-datatype-fix x))
       (udims (vl-datatype->udims x))
       ((when (consp udims))
        (b* ((dim (vl-packeddimension-fix (car udims)))
             ((when (eq dim :vl-unsized-dimension))
              (fail "Most significant dimension is unsized: ~a0" (list x))))
          (success dim)))
       (pdims (vl-datatype->pdims x))
       ((when (consp pdims))
        (b* (((when (eq (car pdims) :vl-unsized-dimension))
              (fail "Most significant dimension is unsized: ~a0" (list x))))
          (success (car pdims)))))
    ;; No array dimensions, and not a nettype.  Do we succeed with NIL or fail?
    ;; What we want depends on whether we only call this due to some indexing
    ;; operation, or whether we call this in an exploratory fashion.  At the
    ;; moment, we return NIL and the caller should produce an error if this is
    ;; bad.
    (success nil)))

(define vl-datatype-range-conservative
  :short "Get the range, if any, for a data type."
  :long "<p>The datatype should be fully resolved, and the unpacked dimensions
passed separately, as in the output from @(see
vl-datatype-resolve-usertypes).</p>

<p>This is like @(see vl-datatype-range), but it only works on
single-dimensional vectors of basic 1-bit types.  Why?  A lot of existing code
is built around an assumption that the range of a variable determines its
width.  In that code, if we use vl-datatype-range, then we'll be silently doing
the wrong thing in a lot of cases.</p>."
  ((x vl-datatype-p))
  :returns
  (mv (warning (iff (vl-warning-p warning) warning))
      (range  vl-maybe-range-p
              "On success: the range of this datatype."))
  (b* (((fun (fail msg args)) 
        (mv (make-vl-warning :type :vl-datatype-range-fail
                             :msg msg
                             :args args)
            nil))
       ((fun (success range)) (mv nil range))
       (x (vl-datatype-fix x))
       (udims (vl-datatype->udims x))
       ((when (consp udims))
        (fail "Unpacked dims present." nil))
       ((when (and (eq (vl-datatype-kind x) :vl-coretype)
                   (member (vl-coretype->name x)
                           '(:vl-logic :vl-reg :vl-bit))))
        (b* ((dims (vl-coretype->pdims x))
             ((when (atom dims)) (success nil))
             ((when (and (atom (cdr dims))
                         (not (eq (car dims) :vl-unsized-dimension))))
              (success (car dims))))
          (fail "Multiple packed dims present" nil))))
    (fail "Complex type." nil)))

(define vl-ss-find-hidexpr-range ((x vl-expr-p)
                                 (ss vl-scopestack-p))
  :guard (vl-hidexpr-p x)
  :prepwork ((local (in-theory (enable vl-hidexpr-p))))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (range    vl-maybe-range-p))
  (b* (((mv warning type) (vl-hidexpr-find-type x ss))
       ((when warning) (mv warning nil)))
    (vl-datatype-range-conservative type)))

(define vl-ss-find-hidexpr-range!! ((x vl-expr-p)
                                    (ss vl-scopestack-p))
  :short "The exclamation marks are there to get your attention."
  :long "<p>This finds the range of the datatype of the given hid, using @(see
vl-datatype-range).  In code that is not aware of multidimensional
arrays/vectors, you should use @(see vl-ss-find-hidexpr-range) (without the
exclamation marks) instead; it finds the datatype range using @(see
vl-datatype-range-conservative) which will correctly produce warnings when the
datatype is multidimensional.</p>"
  :guard (vl-hidexpr-p x)
  :prepwork ((local (in-theory (enable vl-hidexpr-p))))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (range    vl-maybe-range-p))
  (b* (((mv warning type) (vl-hidexpr-find-type x ss))
       ((when warning) (mv warning nil)))
    (vl-datatype-range type)))



(defines vl-packed-datatype-size
  :verify-guards nil
  :prepwork ((local (defthm posp-sum-nats-of-pos-listp
                      (implies (and (pos-listp x) (consp x))
                               (posp (sum-nats x)))
                      :hints(("Goal" :in-theory (enable sum-nats)))))
             (local (defthm posp-max-nats-of-pos-listp
                      (implies (and (pos-listp x) (consp x))
                               (posp (max-nats x)))
                      :hints(("Goal" :in-theory (enable max-nats))))))
  (define vl-packed-datatype-size
    :short "Get the size for any packed data type."
    :long "<p>The type should be fully resolved (i.e. no usertypes) and be
packed or we'll fail.</p>"
    ((x vl-datatype-p))
    :returns
    (mv (warning (iff (vl-warning-p warning) warning))
        (size    (implies (not warning) (posp size)) :rule-classes :type-prescription))
    :measure (vl-datatype-count x)
    (b* (((fun (fail reason args)) 
          (mv (make-vl-warning :type :vl-datatype-size-fail
                               :msg reason
                               :args args)
              nil))
         ((fun (success width)) (mv nil width))
         (x (vl-datatype-fix x))
         ((when (consp (vl-datatype->udims x)))
          (fail "Has unpacked dimensions: ~a0" (list x))))

      (vl-datatype-case x

        (:vl-coretype
         (case x.name
           ;; See SystemVerilog-2012 Section 6.11, Integer Data Types.

           ;; integer atom types -- these don't have any dimensions, they're just fixed sizes
           (:vl-byte     (success 8))
           (:vl-shortint (success 16))
           (:vl-int      (success 32))
           (:vl-longint  (success 64))
           (:vl-integer  (success 32))
           (:vl-time     (success 64))

           ;; integer vector types -- these have arbitrary packed dimensions.
           ((:vl-bit :vl-logic :vl-reg)
            (b* ((totalsize (vl-packeddimensionlist-total-size x.pdims)))
              (if totalsize
                  (success totalsize)
                (fail "Dimensions of vector type ~a0 not resolvd"
                      (list x)))))

           (otherwise
            ;; Something like a real, shortreal, void, realtime, chandle, etc.
            ;; We don't try to size these, but we still claim success: these just
            ;; don't have ranges.
            (fail "bad coretype ~a0" (list x)))))

        (:vl-struct
         (b* (((unless x.packedp) (fail "unpacked struct ~a0" (list x)))
              ;; bozo is there a correct thing to do for a struct with no members?
              ((unless (consp x.members)) (fail "empty struct: ~a0" (list x)))
              ((mv warning widths) (vl-packed-structmemberlist-sizes x.members))
              ((when warning) (mv warning nil)))
           (success (sum-nats widths))))

        (:vl-union
         (b* (((unless x.packedp) (fail "unpacked union ~a0" (list x)))
              ;; bozo is there a correct thing to do for a union with no members?
              ((unless (consp x.members)) (fail "empty union ~a0" (list x)))
              ((mv warning widths) (vl-packed-structmemberlist-sizes x.members))
              ((when warning) (mv warning nil)))
           (success (max-nats widths))))

        (:vl-enum ;; need to compute size from the base type?
         (fail "bozo: implement enum range" nil))

        (:vl-usertype
         (fail "unresolved usertype: ~a0" (list x.kind))))))

  (define vl-packed-structmemberlist-sizes ((x vl-structmemberlist-p))
    :returns (mv (warning (iff (vl-warning-p warning) warning))
                 (sizes   (and (pos-listp sizes)
                               (implies (not warning)
                                        (equal (consp sizes) (consp x))))))
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x)) (mv nil nil))
         ((vl-structmember first) (vl-structmember-fix (car x)))
         ((mv warning size) (vl-packed-datatype-size first.type))
         ((when warning) (mv warning nil))
         ((mv warning rest) (vl-packed-structmemberlist-sizes (cdr x)))
         ((when warning) (mv warning nil)))
      (mv nil (cons size rest))))
  ///
  (defthm-vl-packed-datatype-size-flag
    (defthm len-of-vl-packed-structmemberlist-sizes
      (b* (((mv warning sizes) (vl-packed-structmemberlist-sizes x)))
        (implies (not warning)
                 (equal (len sizes) (len x))))
      :flag vl-packed-structmemberlist-sizes)
    :skip-others t)

  (local (defthm nat-listp-when-pos-listp
           (implies (pos-listp x)
                    (nat-listp x))
           :hints(("Goal" :in-theory (enable nat-listp)))))

  (verify-guards vl-packed-datatype-size)

  (deffixequiv-mutual vl-packed-datatype-size))


(define vl-datatype-set-unsigned ((x vl-datatype-p))
  :returns (new-x vl-datatype-p)
  (vl-datatype-case x
    :vl-coretype (mbe :logic (change-vl-coretype x :signedp nil)
                      :exec (if x.signedp (change-vl-coretype x :signedp nil) x))
    :vl-struct   (mbe :logic (change-vl-struct   x :signedp nil)
                      :exec (if x.signedp (change-vl-struct   x :signedp nil) x))
    :vl-union    (mbe :logic (change-vl-union    x :signedp nil)
                      :exec (if x.signedp (change-vl-union    x :signedp nil) x))
    :otherwise   (vl-datatype-fix x)))
  



(define vl-index-find-type ((x vl-expr-p)
                            (ss vl-scopestack-p))
  :returns (mv (warning (iff (vl-warning-p warning) warning))
               (type (implies (not warning) (vl-datatype-p type))))
  :prepwork ((local (in-theory (disable vl-nonatom->op-when-hidindex-resolved-p
                                        default-car
                                        vl-hidexpr-p-when-id-atom
                                        vl-nonatom->op-when-vl-hidindex-p))))
  :verify-guards nil
  :measure (vl-expr-count x)
  (b* ((x (vl-expr-fix x))
       ((when (or (vl-fast-atom-p x)
                  (not (member (vl-nonatom->op x)
                               '(:vl-index :vl-array-index :vl-bitselect)))))
        (b* (((unless (vl-hidexpr-p x))
              (mv (make-vl-warning :type :vl-bad-index-expr
                                   :msg "An index operator was applied to a bad subexpression, ~a0."
                                   :args (list x))
                  nil))
             ((mv warning type) (vl-hidexpr-find-type x ss))
             ((when warning) (mv warning nil)))
          (mv nil type)))
       ((vl-nonatom x))
       ((mv warning sub-type) (vl-index-find-type (first x.args) ss))
       ((when warning) (mv warning nil))
       (udims (vl-datatype->udims sub-type))
       ((when (consp udims))
        ;; We could check here that the index is in bounds, but maybe that
        ;; should more appropriately be done elsewhere.
        (mv nil (vl-datatype-update-udims (cdr udims) sub-type)))
       (pdims (vl-datatype->pdims sub-type))
       ((unless (consp pdims))
        (mv (make-vl-warning :type :vl-bad-indexing-operator
                             :msg "Can't apply an index operator to ~a0 because it ~
                         has no dimensions; its type is ~a1."
                             :args (list (first x.args) sub-type))
            nil)))
    ;; An index operator applied to packed dimensions makes the datatype unsigned.
    (mv nil (vl-datatype-update-pdims (cdr pdims) (vl-datatype-set-unsigned sub-type))))
  ///
  (verify-guards vl-index-find-type
    :hints(("Goal" :in-theory (e/d (acl2::member-of-cons)
                                   (vl-index-find-type))))))

