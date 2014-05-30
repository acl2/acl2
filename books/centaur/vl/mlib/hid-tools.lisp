; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "expr-tools")
(include-book "range-tools")
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

(define vl-hidindex-p ((x vl-expr-p))
  :returns (bool)
  :short "Recognizes well-formed index expressions into hierarchical
identifiers, e.g., the @('bar[3][4][5]') part of @('foo.bar[3][4][5].baz')."

  :long "<p>We match left-associated trees of indices that ultimately end with
a @(see vl-hidpiece-p).  We don't restrict the actual index expressions, e.g.,
an expression such as @('bar[width-1]') is acceptable.</p>"
  :measure (vl-expr-count x)

  (if (vl-fast-atom-p x)
      (vl-fast-hidpiece-p (vl-atom->guts x))
    (b* (((vl-nonatom x) x))
      (and (eq x.op :vl-index)
           (vl-hidindex-p (first x.args)))))
  ///
  (defthm vl-hidpiece-p-of-vl-atom->guts-when-vl-hidindex-p
    (implies (and (vl-hidindex-p x)
                  (force (vl-atom-p x)))
             (vl-hidpiece-p (vl-atom->guts x))))

  (defthm vl-nonatom->op-when-vl-hidindex-p
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
           (vl-hidpiece-p (vl-atomguts-fix guts))))

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



(define vl-hidexpr-p ((x vl-expr-p))
  :returns (bool)
  :short "Recognizes well-formed hierarchical identifier expressions."
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (vl-hidindex-p x))
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

  (defthm vl-hidpiece-p-of-vl-atom->guts-when-vl-hidexpr-p
    (implies (and (vl-hidexpr-p x)
                  (force (vl-atom-p x)))
             (vl-hidpiece-p (vl-atom->guts x))))

  (defthm vl-nonatom->op-when-vl-hidexpr-p-forward
    (implies (and (vl-hidexpr-p x)
                  (not (vl-atom-p x))
                  (force (vl-expr-p x)))
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

  (defthm vl-hidexpr-p-of-vl-atom
    (implies (and (force (vl-atomguts-p guts))
                  (force (maybe-posp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (equal (vl-hidexpr-p (make-vl-atom :guts guts
                                                :finalwidth finalwidth
                                                :finaltype finaltype))
                    (vl-hidpiece-p guts)))
    :hints(("goal" :in-theory (enable vl-hidexpr-p))))

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
                        (not (eq (vl-nonatom->op x) :vl-hid-dot)))))))



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

  (defthm vl-nonatom->op-when-hidindex-resolved-p
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
  :returns (bool)
  :short "Determines if every index throughout a @(see vl-hidexpr-p) is resolved."
  :guard-debug t
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (vl-hidindex-resolved-p x))
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


(define vl-hidindex-final-name ((x vl-expr-p))
  :guard (vl-hidindex-p x)
  :returns (name stringp :rule-classes :type-prescription)
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (string-fix (vl-hidpiece->name (vl-atom->guts x))))
       ((vl-nonatom x) x))
    (vl-hidindex-final-name (first x.args))))

(define vl-hid-final-name ((x vl-expr-p))
  :guard (vl-hidexpr-p x)
  :returns (name stringp :rule-classes :type-prescription)
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (vl-hidindex-final-name x))
       ((vl-nonatom x) x)
       ((when (eq x.op :vl-hid-dot))
        (vl-hid-final-name (second x.args))))
    (vl-hidindex-final-name x)))

(define vl-flatten-hidindex ((x vl-expr-p))
  :guard (and (vl-hidindex-p x)
              (vl-hidindex-resolved-p x))
  :returns (flat-string stringp :rule-classes :type-prescription)
  :short "Converts a @(see vl-hidindex-p) into a string like
@('\"bar[3][4][5]\"')."
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (string-fix (vl-hidpiece->name (vl-atom->guts x))))
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
  (b* (((when (vl-fast-atom-p x))
        (string-fix (vl-hidpiece->name (vl-atom->guts x))))
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
        (list (vl-hidpiece->name (vl-atom->guts x))))
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
        (vl-explode-hidindex x))
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

