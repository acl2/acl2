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
(include-book "../expr")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (non-parallel-book))

(defxdoc expr-tools
  :parents (mlib)
  :short "Basic functions for working with expressions.")

(local (xdoc::set-default-parents expr-tools))

(defthm vl-maybe-expr-fix-when-exists
  (implies x
           (equal (vl-maybe-expr-fix x)
                  (vl-expr-fix x)))
  :hints(("Goal" :in-theory (enable vl-maybe-expr-fix))))

(defthm vl-expr-fix-under-vl-maybe-expr-equiv-when-exists
  (implies x
           (vl-maybe-expr-equiv (vl-expr-fix x)
                                x))
  :hints(("Goal" :in-theory (enable vl-maybe-expr-fix))))

(defthm vl-atts-fix-when-atom
  (implies (atom x)
           (equal (vl-atts-fix x)
                  nil))
  :hints(("Goal" :in-theory (enable vl-atts-fix))))

(defthm vl-atts-fix-of-cons
  (equal (vl-atts-fix (cons a x))
         (if (atom a)
             (vl-atts-fix x)
           (cons (cons (str-fix (car a))
                       (vl-maybe-expr-fix (cdr a)))
                 (vl-atts-fix x))))
  :hints(("Goal" :in-theory (enable vl-atts-fix))))

(defines vl-expr-count
  :short "A measure for recurring over expressions."
  :long "<p>This measure has a few nice properties.  It respects all of the
equivalences for expressions and avoids having a function for @(see
vl-maybe-expr-p).</p>

<p>Note that we don't count the attributes of an atom.  Normally there's not
any reason to descend into their attributes, so this doesn't really matter.  We
might some day extend this function to also count atom attributes.</p>"

  :verify-guards nil
  :flag vl-expr-flag ;; BOZO no way to override this on deftypes
  :flag-local nil
  :prepwork
  ((local (defrule vl-exprlist-count-raw-of-vl-nonatom->args-rw
            (implies (eq (vl-expr-kind x) :nonatom)
                     (< (vl-exprlist-count-raw (vl-nonatom->args x))
                        (vl-expr-count-raw x)))
            :rule-classes :rewrite))

   (local (defrule vl-exprlist-count-raw-of-cdr-weak
            (<= (vl-exprlist-count-raw (cdr x))
                (vl-exprlist-count-raw x))
            :rule-classes ((:rewrite) (:linear))))

   (local (defrule vl-exprlist-count-raw-of-cdr-rw
            (implies (consp x)
                     (< (vl-exprlist-count-raw (cdr x))
                        (vl-exprlist-count-raw x)))
            :rule-classes :rewrite))

   (local (defrule vl-expr-count-raw-less-than-atts
            ;; BOZO really gross
            (implies x
                     (< (vl-expr-count-raw x)
                        (vl-atts-count-raw (cons (cons name x) alist))))
            :in-theory (enable vl-atts-count-raw vl-maybe-expr-expr->expr)
            :expand ((vl-maybe-expr-count-raw x))))

   (local (defthm vl-maybe-expr-count-raw-of-vl-expr-fix
            (implies x
                     (equal (vl-maybe-expr-count-raw (vl-expr-fix x))
                            (vl-maybe-expr-count-raw x)))
            :hints(("Goal" :in-theory (enable vl-maybe-expr-count-raw))))))

  (define vl-expr-count ((x vl-expr-p))
    :measure (two-nats-measure (vl-expr-count-raw x) 0)
    :flag :expr
    (vl-expr-case x
      :atom
      1
      :nonatom
      (+ 1
         (vl-atts-count x.atts)
         (vl-exprlist-count x.args))))

  (define vl-atts-count ((x vl-atts-p))
    :measure (two-nats-measure (vl-atts-count-raw x) (len x))
    :flag :atts
    (cond ((atom x)
           1)
          ((atom (car x))
           (vl-atts-count (cdr x)))
          ((cdar x)
           (+ 1
              (vl-expr-count (cdar x))
              (vl-atts-count (cdr x))))
          (t
           (+ 1
              (vl-atts-count (cdr x))))))

  (define vl-exprlist-count ((x vl-exprlist-p))
    :measure (two-nats-measure (vl-exprlist-count-raw x) 0)
    :flag :list
    (if (atom x)
        1
      (+ 1
         (vl-expr-count (car x))
         (vl-exprlist-count (cdr x)))))

  ///

  (local (in-theory (enable vl-expr-count
                            vl-atts-count
                            vl-exprlist-count)))

  (defrule vl-exprlist-count-of-cons
    (equal (vl-exprlist-count (cons a x))
           (+ 1
              (vl-expr-count a)
              (vl-exprlist-count x))))

  (defrule vl-expr-count-of-car-weak
    (<= (vl-expr-count (car x))
        (vl-exprlist-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-expr-count-of-car-strong
    (implies (consp x)
             (< (vl-expr-count (car x))
                (vl-exprlist-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-expr-kind-when-vl-expr-count-is-1-fwd
    ;; Goofy rule that helps with, e.g., vl-pp-expr
    (implies (equal (vl-expr-count x) 1)
             (equal (vl-expr-kind x) :atom))
    :rule-classes ((:forward-chaining))
    :hints(("Goal"
            :expand (vl-expr-count x)
            :in-theory (enable vl-expr-count))))

  (defrule vl-exprlist-count-of-cdr-weak
    (<= (vl-exprlist-count (cdr x))
        (vl-exprlist-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-exprlist-count-of-cdr-strong
    (implies (consp x)
             (< (vl-exprlist-count (cdr x))
                (vl-exprlist-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-atts-count-when-atom
    (implies (atom x)
             (equal (vl-atts-count x)
                    1)))

  (defrule vl-atts-count-of-cons
    (equal (vl-atts-count (cons a x))
           (if (atom a)
               (vl-atts-count x)
             (+ 1
                (if (cdr a) (vl-expr-count (cdr a)) 0)
                (vl-atts-count x)))))

  (defrule vl-atts-count-of-cdr-weak
    (<= (vl-atts-count (cdr x))
        (vl-atts-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-atts-count-of-cdr-strong
    (implies (and (consp x)
                  (consp (car x)))
             (< (vl-atts-count (cdr x))
                (vl-atts-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-expr-count-of-cdar-when-vl-atts-p
    (implies (and (vl-atts-p x) x)
             (< (vl-expr-count (cdar x))
                (vl-atts-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-exprlist-count-of-vl-nonatom->args-strong
    (implies (equal (vl-expr-kind x) :nonatom)
             (< (vl-exprlist-count (vl-nonatom->args x))
                (vl-expr-count x)))
    :rule-classes ((:rewrite) (:linear))
    :expand (vl-expr-count x))

  (defrule vl-exprlist-count-of-vl-nonatom->atts-strong
    (implies (equal (vl-expr-kind x) :nonatom)
             (< (vl-atts-count (vl-nonatom->atts x))
                (vl-expr-count x)))
    :rule-classes ((:rewrite) (:linear))
    :expand (vl-expr-count x))

  (deffixequiv-mutual vl-expr-count
    :hints(("Goal"
            :expand (vl-atts-count x)
            :in-theory (enable vl-expr-count
                               vl-atts-count
                               vl-exprlist-count
                               vl-atts-fix
                               vl-exprlist-fix)))))


(encapsulate
  ()

  ;; A tricky recursion over expressions, to make sure our measure is good
  ;; enough to handle lots of cases.  Doesn't compute anything useful.

  (local (defines vl-expr-recursion-test
           (define f-expr ((x vl-expr-p))
             :measure (two-nats-measure (vl-expr-count x) 2)
             (vl-expr-case x
               :atom 1
               :nonatom
               (+ (case x.op
                    ;; Explicit arg recursions for known arity operators
                    (:vl-unary-plus   (+ 1 (f-expr (first x.args))))
                    (:vl-binary-plus  (+ (f-expr (first x.args))
                                         (f-expr (second x.args))))
                    (:vl-qmark        (+ (f-expr (first x.args))
                                         (f-expr (second x.args))
                                         (f-expr (third x.args))))
                    (otherwise 0))
                  ;; Recursion on all args
                  (f-exprlist x.args)
                  ;; Recursion on all atts
                  (f-atts x.atts))))

           (define f-atts-aux ((x vl-atts-p))
             :measure (two-nats-measure (vl-atts-count x) (len x))
             (b* (((when (atom x))
                   0)
                  ;; NOTE: when recurring through attributes you always obey the non-alist
                  ;; convention to match the equivalence relation.  See :doc std/alists if
                  ;; you don't understand this convention.
                  ((when (atom (car x)))
                   (f-atts-aux (cdr x)))
                  ((cons ?name expr) (car x)))
               (+ 1
                  (if expr (f-expr expr) 1)
                  (f-atts-aux (cdr x)))))

           (define f-atts ((x vl-atts-p))
             :measure (two-nats-measure (vl-atts-count x) (+ 1 (len x)))
             (f-atts-aux x))

           (define f-exprlist-aux ((x vl-exprlist-p))
             :measure (two-nats-measure (vl-exprlist-count x) 0)
             (if (atom x)
                 1
               (+ (f-expr (car x))
                  (f-exprlist-aux (cdr x)))))

           (define f-exprlist ((x vl-exprlist-p))
             :measure (two-nats-measure (vl-exprlist-count x) 1)
             (f-exprlist-aux x))
           ///
           (local (in-theory (enable vl-atts-fix)))
           (local (fty::set-deffixequiv-mutual-default-hints nil))
           (deffixequiv-mutual vl-expr-recursion-test))))


(defines vl-expr-count-noatts
  :short "A measure for recurring over expressions but ignoring attributes."

  (define vl-expr-count-noatts ((x vl-expr-p))
    :measure (vl-expr-count x)
    :flag :expr
    (vl-expr-case x
      :atom 1
      :nonatom
      (+ 1 (vl-exprlist-count-noatts x.args))))

  (define vl-exprlist-count-noatts ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    :flag :list
    (if (atom x)
        1
      (+ 1
         (vl-expr-count-noatts (car x))
         (vl-exprlist-count-noatts (cdr x)))))
  ///
  (defrule vl-exprlist-count-noatts-of-cons
    (equal (vl-exprlist-count-noatts (cons a x))
           (+ 1
              (vl-expr-count-noatts a)
              (vl-exprlist-count-noatts x))))

  (defrule vl-expr-count-noatts-of-car-weak
    (<= (vl-expr-count-noatts (car x))
        (vl-exprlist-count-noatts x))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-expr-count-noatts-of-car-strong
    (implies (consp x)
             (< (vl-expr-count-noatts (car x))
                (vl-exprlist-count-noatts x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-expr-kind-when-vl-expr-count-noatts-is-1-fwd
    ;; Goofy rule that helps with, e.g., vl-pp-expr
    (implies (equal (vl-expr-count-noatts x) 1)
             (equal (vl-expr-kind x) :atom))
    :rule-classes ((:forward-chaining))
    :hints(("Goal"
            :expand (vl-expr-count-noatts x)
            :in-theory (enable vl-expr-count-noatts))))

  (defrule vl-exprlist-count-noatts-of-cdr-weak
    (<= (vl-exprlist-count-noatts (cdr x))
        (vl-exprlist-count-noatts x))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-exprlist-count-noatts-of-cdr-strong
    (implies (consp x)
             (< (vl-exprlist-count-noatts (cdr x))
                (vl-exprlist-count-noatts x)))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-exprlist-count-noatts-of-vl-nonatom->args-strong
    (implies (equal (vl-expr-kind x) :nonatom)
             (< (vl-exprlist-count-noatts (vl-nonatom->args x))
                (vl-expr-count-noatts x)))
    :rule-classes ((:rewrite) (:linear))
    :expand (vl-expr-count-noatts x))

  (deffixequiv-mutual vl-expr-count-noatts))


(defsection vl-one-bit-constants
  :short "Already-sized, one-bit constants."

  :long "<p>Care should be taken when using these constants because they are
already annotated with their final widths and types, and @(see
expression-sizing) is a very complex topic.</p>"

  (defconst |*sized-1'b0*|
    (hons-copy (make-vl-atom :guts (make-vl-constint :value 0
                                                     :origwidth 1
                                                     :origtype :vl-unsigned)
                             :finalwidth 1
                             :finaltype :vl-unsigned)))


  (defconst |*sized-1'b1*|
    (hons-copy (make-vl-atom :guts (make-vl-constint :value 1
                                                     :origwidth 1
                                                     :origtype :vl-unsigned)
                             :finalwidth 1
                             :finaltype :vl-unsigned)))

  (defconst |*sized-1'bx*|
    (hons-copy (make-vl-atom :guts (make-vl-weirdint :bits (list :vl-xval)
                                                     :origwidth 1
                                                     :origtype :vl-unsigned)
                             :finalwidth 1
                             :finaltype :vl-unsigned)))

  (defconst |*sized-1'bz*|
    (hons-copy (make-vl-atom :guts (make-vl-weirdint :bits (list :vl-zval)
                                                     :origwidth 1
                                                     :origtype :vl-unsigned)
                             :finalwidth 1
                             :finaltype :vl-unsigned))))



(define vl-expr-resolved-p ((x vl-expr-p))
  :short "Recognizes plain constant integer expressions."

  :long "<p>We say an expression is <b>resolved</b> when it is just an atomic,
integer value that is free of X/Z bits.  We often expect to be able to resolve
the expressions that occur in ranges like @('wire [3:0] foo;') and in
selects.</p>"
  :inline t

  (and (vl-fast-atom-p x)
       (vl-fast-constint-p (vl-atom->guts x))))

(define vl-resolved->val ((x vl-expr-p))
  :guard (vl-expr-resolved-p x)
  :returns (val natp :rule-classes :type-prescription)
  :short "Get the value from a resolved expression."
  :long "<p>Guaranteed to return a natural number.</p>"
  (vl-constint->value (vl-atom->guts x))
  :guard-hints (("Goal" :in-theory (enable vl-expr-resolved-p))))

(deflist vl-exprlist-resolved-p (x)
  (vl-expr-resolved-p x)
  :guard (vl-exprlist-p x))

(defprojection vl-exprlist-resolved->vals ((x vl-exprlist-p))
  :guard (vl-exprlist-resolved-p x)
  :returns (vals nat-listp)
  (vl-resolved->val x))


(define vl-idexpr-p ((x vl-expr-p))
  :short "Recognize plain identifier expressions."
  :long "<p>This recognizes simple non-hierarchical identifier expressions
like @('foo').</p>"
  :inline t
  (and (vl-fast-atom-p x)
       (vl-fast-id-p (vl-atom->guts x))))

(deflist vl-idexprlist-p (x)
  (vl-idexpr-p x)
  :guard (vl-exprlist-p x))


(define vl-idexpr->name ((x vl-expr-p))
  :returns (name stringp :rule-classes :type-prescription)
  :guard (vl-idexpr-p x)
  :short "Get the name from a @(see vl-idexpr-p)."
  :long "<p>Guaranteed to return a string.</p>"
  :inline t
  (vl-id->name (vl-atom->guts x))
  :guard-hints(("Goal" :in-theory (enable vl-idexpr-p))))

(defprojection vl-idexprlist->names ((x vl-exprlist-p))
  :returns (names string-listp)
  :guard (vl-idexprlist-p x)
  (vl-idexpr->name x))


(define vl-idexpr ((name stringp)
                   (finalwidth maybe-natp)
                   (finaltype vl-maybe-exprtype-p))
  :returns (expr vl-expr-p)
  :short "Construct an @(see vl-idexpr-p)."
  :long "<p>@(call vl-idexpr) constructs a simple identifier expression with the
given name, width, and type.</p>

<p>I didn't always hons these, but now it seems like a good idea since the same
identifier may be needed in several contexts, and since we often want to
construct fast alists binding identifiers to things, etc.</p>"
  :inline t
  (hons-copy
   (make-vl-atom :guts (make-vl-id :name name)
                 :finalwidth finalwidth
                 :finaltype finaltype))
  ///
  (local (in-theory (enable vl-idexpr-p vl-idexpr->name)))

  (defthm vl-idexpr-p-of-vl-idexpr
    (vl-idexpr-p (vl-idexpr name finalwidth finaltype)))

  (defthm vl-idexpr->name-of-vl-idexpr
    (equal (vl-idexpr->name (vl-idexpr name finalwidth finaltype))
           (str-fix name)))

  (defthm vl-expr->finalwidth-of-vl-idexpr
    (equal (vl-expr->finalwidth (vl-idexpr name finalwidth finaltype))
           (maybe-natp-fix finalwidth)))

  (defthm vl-expr->finaltype-of-vl-idexpr
    (equal (vl-expr->finaltype (vl-idexpr name finalwidth finaltype))
           (vl-maybe-exprtype-fix finaltype)))

  (defthm vl-expr-kind-of-vl-idexpr
    (equal (vl-expr-kind (vl-idexpr name finalwidth finaltype))
           :atom)))


(defprojection vl-make-idexpr-list ((x          string-listp)
                                    (finalwidth maybe-natp)
                                    (finaltype  vl-maybe-exprtype-p))
  :returns (exprs (and (vl-exprlist-p exprs)
                       (vl-idexprlist-p exprs)))
  (vl-idexpr x finalwidth finaltype)
  :long "<p>Each expression is given the specified @('finalwidth') and
@('finaltype').</p>"
  ///
  (defthm vl-idexprlist->names-of-vl-make-idexpr-list
    (implies (force (string-listp x))
             (equal (vl-idexprlist->names (vl-make-idexpr-list x finalwidth finaltype))
                    x))))


(defines vl-expr-widthsfixed-p
  :short "Determines if all of the @('finalwidth') fields throughout an
expression are natural numbers."

  (define vl-expr-widthsfixed-p ((x vl-expr-p))
    :measure (vl-expr-count x)
    (and (natp (vl-expr->finalwidth x))
         (or (vl-fast-atom-p x)
             (vl-exprlist-widthsfixed-p (vl-nonatom->args x)))))

  (define vl-exprlist-widthsfixed-p ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    (if (consp x)
        (and (vl-expr-widthsfixed-p (car x))
             (vl-exprlist-widthsfixed-p (cdr x)))
      t))
  ///
  (xdoc::without-xdoc
    (deflist vl-exprlist-widthsfixed-p (x)
      (vl-expr-widthsfixed-p x)
      :already-definedp t))

  ;; BOZO doesn't work? (deffixequiv-mutual vl-expr-widthsfixed-p)

  (local (in-theory (enable vl-expr-widthsfixed-p)))

  (local (in-theory (disable (force))))

  (defthm vl-expr-widthsfixed-p-of-car-of-vl-nonatom->args
    ;; BOZO bizarre.
    (implies (and (vl-expr-widthsfixed-p x)
                  (force (not (eq (vl-expr-kind x) :atom)))
                  (force (consp (vl-nonatom->args x))))
             (vl-expr-widthsfixed-p (car (vl-nonatom->args x)))))

  (defthm vl-expr-widthsfixed-p-of-cadr-of-vl-nonatom->args
    ;; BOZO bizarre.
    (implies (and (vl-expr-widthsfixed-p x)
                  (force (not (eq (vl-expr-kind x) :atom)))
                  (force (consp (cdr (vl-nonatom->args x)))))
             (vl-expr-widthsfixed-p (cadr (vl-nonatom->args x))))))




(defines vl-expr-names-nrev
  :parents (vl-expr-names)
  :flag-local nil
  (define vl-expr-names-nrev ((x vl-expr-p) nrev)
    :measure (vl-expr-count x)
    :flag :expr
    (if (vl-fast-atom-p x)
        (let ((guts (vl-atom->guts x)))
          (if (vl-fast-id-p guts)
              (nrev-push (vl-id->name guts) nrev)
            (nrev-fix nrev)))
      (vl-exprlist-names-nrev (vl-nonatom->args x) nrev)))

  (define vl-exprlist-names-nrev ((x vl-exprlist-p) nrev)
    :measure (vl-exprlist-count x)
    :flag :list
    (if (atom x)
        (nrev-fix nrev)
      (let ((nrev (vl-expr-names-nrev (car x) nrev)))
        (vl-exprlist-names-nrev (cdr x) nrev)))))


(defines vl-expr-names
  :short "Gather the names of all @(see vl-id-p) atoms throughout an
expression."

  :long "<p>We compute the names of all simple identifiers used throughout an
expression.</p>

<p>These identifiers might refer to wires, registers, ports, parameters, or
anything else in the module.  This function can often be used in conjunction
with the @(see allexprs) family of functions, e.g., to see all the wires that
are ever mentioned in some module item.</p>

<p>Note that we look for @(see vl-id-p) atoms only.  A consequence is that we
do not return any hierarchical identifiers, function names, or system function
names, since these are not treated as @(see vl-id-p) atoms, but are instead
@(see vl-hidpiece-p), @(see vl-sysfunname-p), or @(see vl-funname-p) atoms.</p>

<p>Note that as we gather names, we do <b>NOT</b> descend into any embedded
@('(* foo = bar *)')-style attributes.</p>

<p>@('vl-expr-names') is necessarily mutually-recursive with
@('vl-exprlist-names').  For efficiency we use a tail-recursive,
accumulator-style functions to do the collection.  Under the hood, we also use
@('nreverse') optimization.</p>"

  :verify-guards nil
  (define vl-expr-names ((x vl-expr-p))
    :returns (names string-listp)
    :measure (vl-expr-count x)
    :flag :expr
    (mbe :logic (if (vl-fast-atom-p x)
                    (let ((guts (vl-atom->guts x)))
                      (if (vl-id-p guts)
                          (list (vl-id->name guts))
                        nil))
                  (vl-exprlist-names (vl-nonatom->args x)))
         :exec (with-local-nrev
                 (vl-expr-names-nrev x nrev))))

  (define vl-exprlist-names ((x vl-exprlist-p))
    :returns (names string-listp)
    :measure (vl-exprlist-count x)
    :flag :list
    (mbe :logic (if (consp x)
                    (append (vl-expr-names (car x))
                            (vl-exprlist-names (cdr x)))
                  nil)
         :exec (with-local-nrev
                 (vl-exprlist-names-nrev x nrev))))
  ///
  (defthm true-listp-of-vl-expr-names
    (true-listp (vl-expr-names x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-names
    (true-listp (vl-exprlist-names x))
    :rule-classes :type-prescription)

  (defthm-vl-expr-names-nrev-flag
    (defthm vl-expr-names-nrev-removal
      (equal (vl-expr-names-nrev x nrev)
             (append nrev (vl-expr-names x)))
      :flag :expr)
    (defthm vl-exprlist-names-nrev-removal
      (equal (vl-exprlist-names-nrev x nrev)
             (append nrev (vl-exprlist-names x)))
      :flag :list)
    :hints(("Goal"
            :in-theory (enable acl2::rcons)
            :expand ((vl-expr-names-nrev x nrev)
                     (vl-exprlist-names-nrev x nrev)
                     (vl-expr-names x)
                     (vl-exprlist-names x)))))

  (verify-guards vl-expr-names)

  (defthm vl-exprlist-names-when-atom
    (implies (atom x)
             (equal (vl-exprlist-names x)
                    nil))
    :hints(("Goal" :expand (vl-exprlist-names x))))

  (defthm vl-exprlist-names-of-cons
    (equal (vl-exprlist-names (cons a x))
           (append (vl-expr-names a)
                   (vl-exprlist-names x)))
    :hints(("Goal" :expand ((vl-exprlist-names (cons a x))))))

  (defthm vl-exprlist-names-of-append
    (equal (vl-exprlist-names (append x y))
           (append (vl-exprlist-names x)
                   (vl-exprlist-names y)))
    :hints(("Goal" :induct (len x))))

  (local (defthm c0
           (implies (member-equal a x)
                    (subsetp-equal (vl-expr-names a)
                                   (vl-exprlist-names x)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm c1
           (implies (subsetp-equal x y)
                    (subsetp-equal (vl-exprlist-names x)
                                   (vl-exprlist-names y)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm c2
           (implies (and (subsetp-equal x y)
                         (member-equal a x))
                    (subsetp-equal (vl-expr-names a)
                                   (vl-exprlist-names y)))))

  (defcong set-equiv set-equiv (vl-exprlist-names x) 1
    :event-name vl-exprlist-names-preserves-set-equiv
    :hints(("Goal" :in-theory (enable set-equiv))))

  (deffixequiv-mutual vl-expr-names))



(defines vl-expr-varnames-nrev
  :parents (vl-expr-varnames)
  :flag-local nil
  (define vl-expr-varnames-nrev ((x vl-expr-p) nrev)
    :measure (vl-expr-count x)
    :flag :expr
    (if (vl-fast-atom-p x)
        (let ((guts (vl-atom->guts x)))
          (if (vl-fast-id-p guts)
              (nrev-push (vl-id->name guts) nrev)
            (nrev-fix nrev)))
      (b* (((vl-nonatom x))
           ((when (member x.op '(:vl-hid-dot
                                 :vl-scope)))
            (nrev-fix nrev))
           ((when (member x.op '(:vl-binary-cast
                                 :vl-pattern-type
                                 :vl-keyvalue)))
            ;; only look at the second argument
            (vl-expr-varnames-nrev (second x.args) nrev)))

        (vl-exprlist-varnames-nrev (vl-nonatom->args x) nrev))))

  (define vl-exprlist-varnames-nrev ((x vl-exprlist-p) nrev)
    :measure (vl-exprlist-count x)
    :flag :list
    (if (atom x)
        (nrev-fix nrev)
      (let ((nrev (vl-expr-varnames-nrev (car x) nrev)))
        (vl-exprlist-varnames-nrev (cdr x) nrev)))))

(defines vl-expr-varnames
  :verify-guards nil
  (define vl-expr-varnames ((x vl-expr-p))
    :returns (names string-listp)
    :measure (vl-expr-count x)
    :flag :expr
    :short "Extract all the variable names from a VL expression."
    (mbe :logic (if (vl-fast-atom-p x)
                    (let ((guts (vl-atom->guts x)))
                      (if (vl-id-p guts)
                          (list (vl-id->name guts))
                        nil))
                  (b* (((vl-nonatom x))
                       ((when (member x.op '(:vl-hid-dot
                                             :vl-scope)))
                        nil)
                       ((when (member x.op '(:vl-binary-cast
                                             :vl-pattern-type
                                             :vl-keyvalue)))
                        ;; only look at the second argument
                        (vl-expr-varnames (second x.args))))

                    (vl-exprlist-varnames (vl-nonatom->args x))))
         :exec (with-local-nrev
                 (vl-expr-varnames-nrev x nrev))))

  (define vl-exprlist-varnames ((x vl-exprlist-p))
    :returns (names string-listp)
    :measure (vl-exprlist-count x)
    :flag :list
    (mbe :logic (if (consp x)
                    (append (vl-expr-varnames (car x))
                            (vl-exprlist-varnames (cdr x)))
                  nil)
         :exec (with-local-nrev
                 (vl-exprlist-varnames-nrev x nrev))))
  ///
  (defthm true-listp-of-vl-expr-varnames
    (true-listp (vl-expr-varnames x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-varnames
    (true-listp (vl-exprlist-varnames x))
    :rule-classes :type-prescription)

  (defthm-vl-expr-varnames-nrev-flag
    (defthm vl-expr-varnames-nrev-removal
      (equal (vl-expr-varnames-nrev x nrev)
             (append nrev (vl-expr-varnames x)))
      :flag :expr)
    (defthm vl-exprlist-varnames-nrev-removal
      (equal (vl-exprlist-varnames-nrev x nrev)
             (append nrev (vl-exprlist-varnames x)))
      :flag :list)
    :hints(("Goal"
            :in-theory (enable acl2::rcons)
            :expand ((vl-expr-varnames-nrev x nrev)
                     (vl-exprlist-varnames-nrev x nrev)
                     (vl-expr-varnames x)
                     (vl-exprlist-varnames x)))))

  (verify-guards vl-expr-varnames)

  (defthm vl-exprlist-varnames-when-atom
    (implies (atom x)
             (equal (vl-exprlist-varnames x)
                    nil))
    :hints(("Goal" :expand (vl-exprlist-varnames x))))

  (defthm vl-exprlist-varnames-of-cons
    (equal (vl-exprlist-varnames (cons a x))
           (append (vl-expr-varnames a)
                   (vl-exprlist-varnames x)))
    :hints(("Goal" :expand ((vl-exprlist-varnames (cons a x))))))

  (defthm vl-exprlist-varnames-of-append
    (equal (vl-exprlist-varnames (append x y))
           (append (vl-exprlist-varnames x)
                   (vl-exprlist-varnames y)))
    :hints(("Goal" :induct (len x))))

  (local (defthm c0
           (implies (member-equal a x)
                    (subsetp-equal (vl-expr-varnames a)
                                   (vl-exprlist-varnames x)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm c1
           (implies (subsetp-equal x y)
                    (subsetp-equal (vl-exprlist-varnames x)
                                   (vl-exprlist-varnames y)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm c2
           (implies (and (subsetp-equal x y)
                         (member-equal a x))
                    (subsetp-equal (vl-expr-varnames a)
                                   (vl-exprlist-varnames y)))))

  (defcong set-equiv set-equiv (vl-exprlist-varnames x) 1
    :event-name vl-exprlist-varnames-preserves-set-equiv
    :hints(("Goal" :in-theory (enable set-equiv))))

  (deffixequiv-mutual vl-expr-varnames))



(defines vl-expr-ops-nrev
  :parents (vl-expr-ops)
  :flag-local nil
  (define vl-expr-ops-nrev ((x vl-expr-p) nrev)
    :measure (vl-expr-count x)
    :flag :expr
    (b* (((when (vl-fast-atom-p x))
          (nrev-fix nrev))
         (nrev (nrev-push (vl-nonatom->op x) nrev)))
      (vl-exprlist-ops-nrev (vl-nonatom->args x) nrev)))

  (define vl-exprlist-ops-nrev ((x vl-exprlist-p) nrev)
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (nrev-fix nrev))
         (nrev (vl-expr-ops-nrev (car x) nrev)))
      (vl-exprlist-ops-nrev (cdr x) nrev))))

(defines vl-expr-ops
  :short "Gather all of the operators used throughout an expression."
  :long "<p>We simply gather all of the operators, with repetition.  The
resulting list may contain any @(see vl-op-p), including even odd such as
@(':vl-syscall') or @(':vl-hid-dot'), which you might not ordinarily think of
as an operator.</p>"

  (define vl-expr-ops ((x vl-expr-p))
    :returns (ops vl-oplist-p)
    :measure (vl-expr-count x)
    :verify-guards nil
    :flag :expr
    (mbe :logic (if (vl-fast-atom-p x)
                    nil
                  (cons (vl-nonatom->op x)
                        (vl-exprlist-ops (vl-nonatom->args x))))
         :exec (with-local-nrev
                 (vl-expr-ops-nrev x nrev))))

   (define vl-exprlist-ops ((x vl-exprlist-p))
     :returns (ops vl-oplist-p)
     :measure (vl-exprlist-count x)
     :flag :list
     (mbe :logic (if (consp x)
                     (append (vl-expr-ops (car x))
                             (vl-exprlist-ops (cdr x)))
                   nil)
         :exec (with-local-nrev
                 (vl-exprlist-ops-nrev x nrev))))
   ///
   (defthm true-listp-of-vl-expr-ops
     (true-listp (vl-expr-ops x))
     :rule-classes :type-prescription)

   (defthm true-listp-of-vl-exprlist-ops
     (true-listp (vl-exprlist-ops x))
     :rule-classes :type-prescription)

   (defthm-vl-expr-ops-nrev-flag
     (defthm vl-expr-ops-nrev-removal
       (equal (vl-expr-ops-nrev x nrev)
              (append nrev (vl-expr-ops x)))
       :flag :expr)
     (defthm vl-exprlist-ops-nrev-removal
       (equal (vl-exprlist-ops-nrev x nrev)
              (append nrev (vl-exprlist-ops x)))
       :flag :list)
     :hints(("Goal"
             :expand ((vl-expr-ops-nrev x nrev)
                      (vl-exprlist-ops-nrev x nrev)
                      (vl-expr-ops x)
                      (vl-exprlist-ops x)))))

   (verify-guards vl-expr-ops)

   (deffixequiv-mutual vl-expr-ops))


(defines vl-expr-has-ops-aux

   (define vl-expr-has-ops-aux ((ops vl-oplist-p)
                                (x   vl-expr-p))
     :guard (true-listp ops)
     :measure (vl-expr-count x)
     (cond ((vl-fast-atom-p x)
            nil)
           ((member (vl-nonatom->op x) ops)
            t)
           (t
            (vl-exprlist-has-ops-aux ops (vl-nonatom->args x)))))

   (define vl-exprlist-has-ops-aux ((ops vl-oplist-p)
                                    (x   vl-exprlist-p))
     :guard (true-listp ops)
     :measure (vl-exprlist-count x)
     (if (atom x)
         nil
       (or (vl-expr-has-ops-aux ops (car x))
           (vl-exprlist-has-ops-aux ops (cdr x)))))

   ///

   (defthm-vl-expr-flag
     (defthm vl-expr-has-ops-aux-removal
       (equal (vl-expr-has-ops-aux ops x)
              (intersectp-equal ops (vl-expr-ops x)))
       :flag :expr)
     (defthm vl-exprlist-has-ops-aux-removal
       (equal (vl-exprlist-has-ops-aux ops x)
              (intersectp-equal ops (vl-exprlist-ops x)))
       :flag :list)
     :skip-others t
     :hints(("Goal"
             :in-theory (enable vl-expr-ops
                                vl-exprlist-ops
                                vl-expr-has-ops-aux
                                vl-exprlist-has-ops-aux)))))

(define vl-expr-has-ops ((ops vl-oplist-p)
                         (x   vl-expr-p))
  :enabled t
  :hooks nil ;; BOZO? intersectp-equal doesn't respect oplist equiv
  (mbe :logic (intersectp-equal ops (vl-expr-ops x))
       :exec (vl-expr-has-ops-aux (list-fix ops) x)))

(define vl-exprlist-has-ops ((ops vl-oplist-p)
                             (x   vl-exprlist-p))
  :enabled t
  :hooks nil ;; BOZO? intersectp-equal doesn't respect oplist equiv
  (mbe :logic (intersectp-equal ops (vl-exprlist-ops x))
       :exec (vl-exprlist-has-ops-aux (list-fix ops) x)))


(define vl-zbitlist-p ((x vl-bitlist-p))
  (if (consp x)
      (and (equal (vl-bit-fix (car x)) :vl-zval)
           (vl-zbitlist-p (cdr x)))
    t))

(define vl-zatom-p ((x vl-expr-p))
  (and (vl-fast-atom-p x)
       (let ((guts (vl-atom->guts x)))
         (and (vl-weirdint-p guts)
              (vl-zbitlist-p (vl-weirdint->bits guts))))))

(define vl-obviously-true-expr-p ((x vl-expr-p))
  (and (vl-fast-atom-p x)
       (vl-fast-constint-p (vl-atom->guts x))
       (eql (vl-constint->value (vl-atom->guts x)) 1)))

(define vl-obviously-false-expr-p ((x vl-expr-p))
  (and (vl-fast-atom-p x)
       (vl-fast-constint-p (vl-atom->guts x))
       (eql (vl-constint->value (vl-atom->guts x)) 0)))


(define vl-make-index (n)
  :short "Safely create a constant integer atom whose value is n."
  :long "<p>@('n') is expected to be a natural number, but our guard is only
@('t').  We cause a hard error if we are given a non-natural number index, or
one which is too large.  BOZO consider a stronger guard.</p>"
  :returns (index vl-expr-p)

  (let* ((value  (if (natp n)
                     n
                   (prog2$ (raise "Proposed index is not a natural: ~x0." n)
                           0)))
         (width (+ 1 (integer-length value))))
    (if (<= width 31)
        ;; Prefer to make indices that look like plain decimal numbers, I
        ;; didn't used to hons these, but now it seems like a good idea since
        ;; the same indicies may be needed frequently.
        (hons-copy
         (make-vl-atom
          :guts (make-vl-constint :origwidth 32
                                  :origtype :vl-signed
                                  :wasunsized t
                                  :value value)
          :finalwidth 32
          :finaltype :vl-signed))
      (hons-copy
       (make-vl-atom
        :guts (make-vl-constint :origwidth width
                                :origtype :vl-signed
                                :value value)
        :finalwidth width
        :finaltype :vl-signed))))
  ///
  (local (in-theory (enable vl-make-index)))

  (defthm vl-expr-kind-of-vl-make-index
    (eq (vl-expr-kind (vl-make-index n)) :atom))

  (defthm vl-expr-resolved-p-of-vl-make-index
    (vl-expr-resolved-p (vl-make-index n))
    :hints(("Goal" :in-theory (enable vl-expr-resolved-p))))

  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))

  (local (defthm simple-loghead-identity
           (implies (and (case-split (< n (expt 2 k)))
                         (natp n)
                         (natp k))
                    (equal (acl2::loghead k n)
                           n))))

  (defthm vl-resolved->val-of-vl-make-index
    (equal (vl-resolved->val (vl-make-index n))
           (nfix n))
    :hints(("Goal" :in-theory (enable vl-resolved->val))))

  (defthm posp-of-vl-expr->finalwidth-of-vl-make-index
    (posp (vl-expr->finalwidth (vl-make-index n)))
    :rule-classes :type-prescription)

  (deffixequiv vl-make-index :args ((n natp))))



(defines vl-expr-atoms-nrev
  :parents (vl-expr-atoms)
  :flag-local nil
  (define vl-expr-atoms-nrev ((x vl-expr-p) nrev)
    :measure (vl-expr-count x)
    :flag :expr
    (if (vl-fast-atom-p x)
        (nrev-push (vl-expr-fix x) nrev)
      (vl-exprlist-atoms-nrev (vl-nonatom->args x) nrev)))

  (define vl-exprlist-atoms-nrev ((x vl-exprlist-p) nrev)
    :measure (vl-exprlist-count x)
    :flag :list
    (if (atom x)
        (nrev-fix nrev)
      (let ((nrev (vl-expr-atoms-nrev (car x) nrev)))
        (vl-exprlist-atoms-nrev (cdr x) nrev)))))


(defines vl-expr-atoms
  :short "Gather all of the atoms throughout an expression."
  :long "<p>We simply gather all of the @(see vl-atom-p)s in the expression,
with repetition.  The resulting list may contain any @(see vl-atom-p),
including even odd things like hid pieces and function names, which you might
not usually think of as atoms.</p>"

  (define vl-expr-atoms ((x vl-expr-p))
    :returns (atoms (and (vl-exprlist-p atoms)
                         (vl-atomlist-p atoms)))
    :measure (vl-expr-count x)
    :verify-guards nil
    :flag :expr
    (mbe :logic (if (vl-atom-p x)
                    (list (vl-expr-fix x))
                  (vl-exprlist-atoms (vl-nonatom->args x)))
         :exec (with-local-nrev (vl-expr-atoms-nrev x nrev))))

  (define vl-exprlist-atoms ((x vl-exprlist-p))
    :returns (atoms (and (vl-exprlist-p atoms)
                         (vl-atomlist-p atoms)))
    :measure (vl-exprlist-count x)
    :flag :list
    (mbe :logic (if (consp x)
                    (append (vl-expr-atoms (car x))
                            (vl-exprlist-atoms (cdr x)))
                  nil)
         :exec (with-local-nrev (vl-exprlist-atoms-nrev x nrev))))
  ///
  (defthm true-listp-of-vl-expr-atoms
    (true-listp (vl-expr-atoms x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-atoms
    (true-listp (vl-exprlist-atoms x))
    :rule-classes :type-prescription)

  (defthm-vl-expr-atoms-nrev-flag
    (defthm vl-expr-atoms-nrev-removal
      (equal (vl-expr-atoms-nrev x nrev)
             (append nrev (vl-expr-atoms x)))
      :flag :expr)
    (defthm vl-exprlist-atoms-nrev-removal
      (equal (vl-exprlist-atoms-nrev x nrev)
             (append nrev (vl-exprlist-atoms x)))
      :flag :list)
    :hints(("Goal"
            :in-theory (enable acl2::rcons)
            :expand ((vl-expr-atoms-nrev x nrev)
                     (vl-exprlist-atoms-nrev x nrev)))))

  (verify-guards vl-expr-atoms)

  (deffixequiv-mutual vl-expr-atoms))


(define vl-atomlist-collect-funnames ((x vl-exprlist-p))
  :guard (vl-atomlist-p x)
  :returns (ans string-listp)
  :parents (vl-expr-funnames vl-atomlist-p)
  :short "Collect all the function names that occur in an @(see vl-atomlist-p)
and return them as a string list."

  (b* (((when (atom x))
        nil)
       (guts (vl-atom->guts (car x)))
       ((when (vl-fast-funname-p guts))
        (cons (string-fix (vl-funname->name guts))
              (vl-atomlist-collect-funnames (cdr x)))))
    (vl-atomlist-collect-funnames (cdr x))))

(define vl-expr-funnames ((x vl-expr-p))
  :returns (ans string-listp)
  :short "Collect the names of all functions that occur in a @(see vl-expr-p)
and return them as a string list."
  (vl-atomlist-collect-funnames (vl-expr-atoms x)))

(define vl-exprlist-funnames ((x vl-exprlist-p))
  :returns (ans string-listp)
  :short "Collect the names of all functions that occur in a @(see
vl-exprlist-p) and return them as a string list."
  (vl-atomlist-collect-funnames (vl-exprlist-atoms x)))

(define vl-expr-has-funcalls ((x vl-expr-p))
  (mbe :logic (if (member :vl-funcall (vl-expr-ops x))
                  t
                nil)
       :exec (vl-expr-has-ops (list :vl-funcall) x)))

(define vl-exprlist-has-funcalls ((x vl-exprlist-p))
  (mbe :logic (if (member :vl-funcall (vl-exprlist-ops x))
                  t
                nil)
       :exec (vl-exprlist-has-ops (list :vl-funcall) x)))



(defines vl-expr-selects
  :short "Collects up all the selection expressions (bit-selects, part-selects,
array indexing, and unresolved indexing) and returns them as a flat list of
expressions."
  :long "<p>Note: we assume there are no nested selects.</p>"

  (define vl-expr-selects ((x vl-expr-p))
    :returns (selects vl-exprlist-p)
    :measure (vl-expr-count x)
    :flag :expr
    (b* (((when (vl-fast-atom-p x))
          nil)
         ((vl-nonatom x) x)
         ((when (or (eq x.op :vl-bitselect)
                    (eq x.op :vl-partselect-colon)
                    (eq x.op :vl-partselect-pluscolon)
                    (eq x.op :vl-partselect-minuscolon)
                    (eq x.op :vl-index)
                    (eq x.op :vl-select-colon)
                    (eq x.op :vl-select-pluscolon)
                    (eq x.op :vl-select-minuscolon)))
          (list (vl-expr-fix x))))
      (vl-exprlist-selects x.args)))

  (define vl-exprlist-selects ((x vl-exprlist-p))
    :returns (selects vl-exprlist-p)
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (append (vl-expr-selects (car x))
              (vl-exprlist-selects (cdr x)))))
  ///
  (deffixequiv-mutual vl-expr-selects))


(define vl-bitlist-from-nat ((x     natp)
                             (width natp))
  :returns (bits vl-bitlist-p)
  :short "Turn a natural number into a vl-bitlist-p of the given width."
  (b* (((when (zp width)) nil)
       (width (1- width))
       (bit (if (logbitp width (lnfix x))
                :vl-1val
              :vl-0val)))
    (cons bit (vl-bitlist-from-nat x width)))
  :prepwork ((local (in-theory (disable logbitp))))
  ///
  (defthm len-of-vl-bitlist-from-nat
    (equal (len (vl-bitlist-from-nat x width))
           (nfix width))))


(defsection vl-exprtype-max
  :parents (vl-expr-typedecide)
  :short "@(call vl-exprtype-max) is given @(see vl-exprtype-p)s as arguments;
it returns @(':vl-unsigned') if any argument is unsigned, or @(':vl-signed')
when all arguments are signed."

  (local (in-theory (enable vl-exprtype-p)))

  (defund vl-exprtype-max-fn (x y)
    (declare (xargs :guard (and (vl-exprtype-p x)
                                (vl-exprtype-p y))))
    ;; Goofy MBE stuff is just to make sure this function breaks if we ever add
    ;; support for reals or other types.
    (let ((x-fix (mbe :logic (case (vl-exprtype-fix x)
                               (:vl-signed   :vl-signed)
                               (otherwise    :vl-unsigned))
                      :exec x))
          (y-fix (mbe :logic (case (vl-exprtype-fix y)
                               (:vl-signed   :vl-signed)
                               (otherwise    :vl-unsigned))
                      :exec y)))
      (if (or (eq x-fix :vl-unsigned)
              (eq y-fix :vl-unsigned))
          :vl-unsigned
        :vl-signed)))

  (defmacro vl-exprtype-max (x y &rest rst)
    (xxxjoin 'vl-exprtype-max-fn (cons x (cons y rst))))

  (add-binop vl-exprtype-max vl-exprtype-max-fn)

  (local (in-theory (enable vl-exprtype-max-fn)))

  (defthm vl-exprtype-p-of-vl-exprtype-max
    (vl-exprtype-p (vl-exprtype-max x y)))

  (defthm type-of-vl-exprtype-max
    (and (symbolp (vl-exprtype-max x y))
         (not (equal t (vl-exprtype-max x y)))
         (not (equal nil (vl-exprtype-max x y))))
    :rule-classes :type-prescription)

  (defthm vl-exprtype-max-of-vl-exprtype-max
    (equal (vl-exprtype-max (vl-exprtype-max x y) z)
           (vl-exprtype-max x (vl-exprtype-max y z))))

  (deffixequiv vl-exprtype-max-fn :args ((x vl-exprtype-p) (y vl-exprtype-p))))


(define vl-expr->atts ((x vl-expr-p))
  :returns (atts vl-atts-p)
  :inline t
  :enabled t
  (vl-expr-case x
    :atom x.atts
    :nonatom x.atts))

(define vl-expr-add-atts ((new-atts vl-atts-p)
                          (x        vl-expr-p))
  :returns (new-x vl-expr-p)
  (vl-expr-case x
    :atom (change-vl-atom x :atts (append-without-guard new-atts x.atts))
    :nonatom (change-vl-nonatom x :atts (append-without-guard new-atts x.atts))))
