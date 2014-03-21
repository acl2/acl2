; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (non-parallel-book))

(defxdoc expr-tools
  :parents (mlib)
  :short "Basic functions for working with expressions.")


(defsection vl-one-bit-constants
  :parents (expr-tools)
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
  :parents (expr-tools)
  :short "Recognizes plain constant integer expressions."

  :long "<p>We say an expression is <b>resolved</b> when it is just an atomic,
integer value that is free of X/Z bits.  We often expect to be able to resolve
the expressions that occur in ranges like @('wire [3:0] foo;') and in
selects.</p>"
  :inline t

  (and (vl-fast-atom-p x)
       (vl-fast-constint-p (vl-atom->guts x))))


(define vl-resolved->val ((x (and (vl-expr-p x)
                                  (vl-expr-resolved-p x))))
  :parents (expr-tools)
  :short "Get the value from a resolved expression."
  :long "<p>Guaranteed to return a natural number.</p>"

  (lnfix (vl-constint->value (vl-atom->guts x)))

  :guard-hints (("Goal" :in-theory (enable vl-expr-resolved-p)))

  ///
  (defthm natp-of-vl-resolved->val
    (natp (vl-resolved->val x))
    :rule-classes :type-prescription))

(deflist vl-exprlist-resolved-p (x)
  (vl-expr-resolved-p x)
  :guard (vl-exprlist-p x)
  :elementp-of-nil nil
  :parents (expr-tools))

(defprojection vl-exprlist-resolved->vals (x)
  (vl-resolved->val x)
  :guard (and (vl-exprlist-p x)
              (vl-exprlist-resolved-p x))
  :nil-preservingp nil
  :parents (expr-tools)
  :rest
  ((defthm nat-listp-of-vl-exprlist-resolved->vals
     (nat-listp (vl-exprlist-resolved->vals x)))))



(define vl-idexpr-p ((x vl-expr-p))
  :parents (expr-tools)
  :short "Recognize plain identifier expressions."
  :long "<p>This recognizes simple non-hierarchical identifier expressions
like @('foo').</p>"
  :inline t
  (and (vl-fast-atom-p x)
       (vl-fast-id-p (vl-atom->guts x))))

(deflist vl-idexprlist-p (x)
  (vl-idexpr-p x)
  :guard (vl-exprlist-p x)
  :elementp-of-nil nil
  :parents (expr-tools))


(define vl-idexpr->name ((x (and (vl-expr-p x)
                                 (vl-idexpr-p x))))
  :parents (expr-tools)
  :short "Get the name from a @(see vl-idexpr-p)."
  :long "<p>Guaranteed to return a string.</p>"
  :inline t

  (mbe :logic (string-fix (vl-id->name (vl-atom->guts x)))
       :exec (vl-id->name (vl-atom->guts x)))

  :guard-hints(("Goal" :in-theory (enable vl-idexpr-p)))

  ///

  (defthm stringp-of-vl-idexpr->name
    (stringp (vl-idexpr->name x))
    :rule-classes :type-prescription))


(defprojection vl-idexprlist->names (x)
  (vl-idexpr->name x)
  :guard (and (vl-exprlist-p x)
              (vl-idexprlist-p x))
  :parents (expr-tools)
  :rest
  ((defthm string-listp-of-vl-idexprlist->names
     (string-listp (vl-idexprlist->names x)))))



(define vl-idexpr ((name stringp)
                   (finalwidth maybe-natp)
                   (finaltype vl-maybe-exprtype-p))
  :parents (expr-tools)
  :short "Construct an @(see vl-idexpr-p)."
  :long "<p>@(call vl-idexpr) constructs a simple identifier expression with the
given name, width, and type.</p>

<p>I didn't always hons these, but now it seems like a good idea since the same
identifier may be needed in several contexts, and since we often want to
construct fast alists binding identifiers to things, etc.</p>"
  :inline t

  (make-honsed-vl-atom :guts (make-honsed-vl-id :name name)
                       :finalwidth finalwidth
                       :finaltype finaltype)

  ///
  (local (in-theory (enable vl-idexpr-p vl-idexpr->name)))

  (defthm vl-idexpr-p-of-vl-idexpr
    (implies (and (force (stringp name))
                  (force (maybe-natp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (vl-idexpr-p (vl-idexpr name finalwidth finaltype))))

  (defthm vl-idexpr->name-of-vl-idexpr
    (implies (force (stringp name))
             (equal (vl-idexpr->name (vl-idexpr name finalwidth finaltype))
                    name)))

  (defthm vl-expr->finalwidth-of-vl-idexpr
    (equal (vl-expr->finalwidth (vl-idexpr name finalwidth finaltype))
           finalwidth))

  (defthm vl-expr->finaltype-of-vl-idexpr
    (equal (vl-expr->finaltype (vl-idexpr name finalwidth finaltype))
           finaltype))

  (defthm vl-atom-p-of-vl-idexpr
    (implies (and (force (stringp name))
                  (force (maybe-natp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (vl-atom-p (vl-idexpr name finalwidth finaltype)))))



(defprojection vl-make-idexpr-list (x finalwidth finaltype)
  (vl-idexpr x finalwidth finaltype)
  :guard (and (string-listp x)
              (maybe-natp finalwidth)
              (vl-maybe-exprtype-p finaltype))
  :result-type vl-exprlist-p
  :parents (expr-tools)
  :long "<p>Each expression is given the specified @('finalwidth') and
@('finaltype').</p>"
  :rest
  ((defthm vl-idexprlist-p-of-vl-make-idexpr-list
     (implies (and (force (string-listp x))
                   (force (maybe-natp finalwidth))
                   (force (vl-maybe-exprtype-p finaltype)))
              (vl-idexprlist-p (vl-make-idexpr-list x finalwidth finaltype))))

   (defthm vl-idexprlist->names-of-vl-make-idexpr-list
     (implies (force (string-listp x))
              (equal (vl-idexprlist->names (vl-make-idexpr-list x finalwidth finaltype))
                     x)))))



(defsection vl-expr-widthsfixed-p
  :parents (expr-tools)
  :short "@(call vl-expr-widthsfixed-p) determines if all of the
@('finalwidth') fields throughout an expression are natural numbers."

  (mutual-recursion

   (defund vl-expr-widthsfixed-p (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (and (natp (vl-expr->finalwidth x))
          (or (vl-fast-atom-p x)
              (vl-exprlist-widthsfixed-p (vl-nonatom->args x)))))

   (defund vl-exprlist-widthsfixed-p (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (consp x)
         (and (vl-expr-widthsfixed-p (car x))
              (vl-exprlist-widthsfixed-p (cdr x)))
       t)))

  (deflist vl-exprlist-widthsfixed-p (x)
    (vl-expr-widthsfixed-p x)
    :already-definedp t
    :parents (expr-tools))

  (local (in-theory (enable vl-expr-widthsfixed-p)))

  (defthm vl-expr-widthsfixed-p-of-car-of-vl-nonatom->args
    ;; BOZO bizarre.
    (implies (and (vl-expr-widthsfixed-p x)
                  (force (not (vl-atom-p x)))
                  (force (consp (vl-nonatom->args x))))
             (vl-expr-widthsfixed-p (car (vl-nonatom->args x)))))

  (defthm vl-expr-widthsfixed-p-of-cadr-of-vl-nonatom->args
    ;; BOZO bizarre.
    (implies (and (vl-expr-widthsfixed-p x)
                  (force (not (vl-atom-p x)))
                  (force (consp (cdr (vl-nonatom->args x)))))
             (vl-expr-widthsfixed-p (cadr (vl-nonatom->args x))))))



(defsection vl-expr-names
  :parents (expr-tools)
  :short "Gather the names of all @(see vl-id-p) atoms throughout an
expression."

  :long "<p><b>Signature:</b> @(call vl-expr-names) returns a string list.</p>

<p>We compute the names of all simple identifiers used throughout an
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

  (defxdoc vl-exprlist-names
    :parents (expr-tools)
    :short "Gather the names of all @(see vl-id-p) atoms throughout an
expression list."

    :long "<p>See @(see vl-expr-names)</p>")

  (mutual-recursion

   (defund vl-expr-names-exec (x acc)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (vl-expr-count x)))
     (if (vl-fast-atom-p x)
         (let ((guts (vl-atom->guts x)))
           (if (vl-fast-id-p guts)
               (cons (vl-id->name guts) acc)
             acc))
       (vl-exprlist-names-exec (vl-nonatom->args x) acc)))

   (defund vl-exprlist-names-exec (x acc)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (vl-exprlist-count x)))
     (if (consp x)
         (vl-exprlist-names-exec (cdr x)
                                 (vl-expr-names-exec (car x) acc))
       acc)))

  (mutual-recursion

   (defund vl-expr-names (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (vl-expr-count x)
                     :verify-guards nil))
     (mbe :logic (if (vl-atom-p x)
                     (let ((guts (vl-atom->guts x)))
                       (if (vl-id-p guts)
                           (list (vl-id->name guts))
                         nil))
                   (vl-exprlist-names (vl-nonatom->args x)))
          :exec (reverse (vl-expr-names-exec x nil))))

   (defund vl-exprlist-names (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (vl-exprlist-count x)))
     (mbe :logic (if (consp x)
                     (append (vl-expr-names (car x))
                             (vl-exprlist-names (cdr x)))
                   nil)
          :exec (reverse (vl-exprlist-names-exec x nil)))))

  (defthm true-listp-of-vl-expr-names
    (true-listp (vl-expr-names x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-names
    (true-listp (vl-exprlist-names x))
    :rule-classes :type-prescription)

  (FLAG::make-flag vl-fast-flag-expr-names
                   vl-expr-names-exec
                   :flag-mapping ((vl-expr-names-exec . expr)
                                  (vl-exprlist-names-exec . list)))

  (defthm-vl-fast-flag-expr-names lemma
    (expr (equal (vl-expr-names-exec x acc)
                 (revappend (vl-expr-names x) acc))
          :name vl-expr-names-exec-removal)
    (list (equal (vl-exprlist-names-exec x acc)
                 (revappend (vl-exprlist-names x) acc))
          :name vl-exprlist-names-exec-removal)
    :hints(("Goal"
            :induct (vl-fast-flag-expr-names flag x acc)
            :expand ((vl-expr-names-exec x acc)
                     (vl-exprlist-names-exec x acc)
                     (vl-expr-names x)
                     (vl-exprlist-names x)))))

  (verify-guards vl-expr-names
                 :hints(("Goal" :in-theory (enable vl-expr-names
                                                   vl-expr-names-exec
                                                   vl-exprlist-names
                                                   vl-exprlist-names-exec))))

  (defttag vl-optimize)
  (never-memoize vl-expr-names-exec)
  (never-memoize vl-exprlist-names-exec)
  (progn! (set-raw-mode t)
          (defun vl-expr-names (x)
            (nreverse (vl-expr-names-exec x nil)))
          (defun vl-exprlist-names (x)
            (nreverse (vl-exprlist-names-exec x nil))))
  (defttag nil)

  (local (defthm lemma
           (case flag
             (expr (implies (vl-expr-p x)
                            (string-listp (vl-expr-names x))))
             (atts t)
             (t (implies (vl-exprlist-p x)
                         (string-listp (vl-exprlist-names x)))))
           :rule-classes nil
           :hints(("Goal"
                   :induct (vl-expr-induct flag x)
                   :expand ((vl-expr-names x)
                            (vl-exprlist-names x))))))

  (defthm string-listp-of-vl-expr-names
    (implies (force (vl-expr-p x))
             (string-listp (vl-expr-names x)))
    :hints(("Goal" :use ((:instance lemma (flag 'expr))))))

  (defthm string-listp-of-vl-exprlist-names
    (implies (force (vl-exprlist-p x))
             (string-listp (vl-exprlist-names x)))
    :hints(("Goal" :use ((:instance lemma (flag 'list))))))

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
    :hints(("Goal" :in-theory (enable set-equiv)))))




(defsection vl-expr-ops
  :parents (expr-tools)
  :short "Gather all of the operators used throughout an expression."
  :long "<p><b>Signature:</b> @(call vl-expr-ops) returns a @(see
vl-oplist-p).</p>

<p>We simply gather all of the operators, with repetition.  The resulting list
may contain any @(see vl-op-p), including even odd such as @(':vl-syscall') or
@(':vl-hid-dot'), which you might not ordinarily think of as an operator.</p>"

  (defxdoc vl-exprlist-ops
    :parents (expr-tools)
    :short "Gather all operators used throughout an expression list."
    :long "<p>See @(see vl-expr-ops).</p>")

  (mutual-recursion

   (defund vl-fast-expr-ops (x acc)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atom-p x)
         acc
       (vl-fast-exprlist-ops (vl-nonatom->args x) (cons (vl-nonatom->op x) acc))))

   (defund vl-fast-exprlist-ops (x acc)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (consp x)
         (vl-fast-exprlist-ops (cdr x)
                               (vl-fast-expr-ops (car x) acc))
       acc)))

  (mutual-recursion

   (defund vl-expr-ops (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)
                     :verify-guards nil))
     (mbe :logic (if (vl-atom-p x)
                     nil
                   (cons (vl-nonatom->op x) (vl-exprlist-ops (vl-nonatom->args x))))
          :exec (reverse (vl-fast-expr-ops x nil))))

   (defund vl-exprlist-ops (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (mbe :logic (if (consp x)
                     (append (vl-expr-ops (car x))
                             (vl-exprlist-ops (cdr x)))
                   nil)
          :exec (reverse (vl-fast-exprlist-ops x nil)))))

  (defttag vl-optimize)
  (never-memoize vl-fast-expr-ops)
  (never-memoize vl-fast-exprlist-ops)
  (progn! (set-raw-mode t)
          (defun vl-expr-ops (x)
            (nreverse (vl-fast-expr-ops x nil)))
          (defun vl-exprlist-ops (x)
            (nreverse (vl-fast-exprlist-ops x nil))))
  (defttag nil)

  (defthm true-listp-of-vl-expr-ops
    (true-listp (vl-expr-ops x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-ops
    (true-listp (vl-exprlist-ops x))
    :rule-classes :type-prescription)

  (encapsulate
    ()
    (local (FLAG::make-flag vl-fast-flag-expr-ops
                            vl-fast-expr-ops
                            :flag-mapping ((vl-fast-expr-ops . expr)
                                           (vl-fast-exprlist-ops . list))))

    (local (defthm-vl-fast-flag-expr-ops vl-fast-expr-ops-correct
             (expr (equal (vl-fast-expr-ops x acc)
                          (revappend (vl-expr-ops x) acc)))
             (list (equal (vl-fast-exprlist-ops x acc)
                          (revappend (vl-exprlist-ops x) acc)))
             :hints(("Goal"
                     :induct (vl-fast-flag-expr-ops flag x acc)
                     :expand ((vl-fast-expr-ops x acc)
                              (vl-fast-exprlist-ops x acc)
                              (vl-expr-ops x)
                              (vl-exprlist-ops x))))))

    (verify-guards vl-expr-ops
      :hints(("Goal" :in-theory (enable vl-expr-ops
                                        vl-fast-expr-ops
                                        vl-exprlist-ops
                                        vl-fast-exprlist-ops)))))

  (encapsulate
    ()
    (local (defthm lemma
             (case flag
               (expr (implies (vl-expr-p x)
                              (vl-oplist-p (vl-expr-ops x))))
               (atts t)
               (t (implies (vl-exprlist-p x)
                           (vl-oplist-p (vl-exprlist-ops x)))))
             :rule-classes nil
             :hints(("Goal"
                     :induct (vl-expr-induct flag x)
                     :expand ((vl-expr-ops x)
                              (vl-exprlist-ops x))))))

    (defthm vl-oplist-p-of-vl-expr-ops
      (implies (force (vl-expr-p x))
               (vl-oplist-p (vl-expr-ops x)))
      :hints(("Goal" :use ((:instance lemma (flag 'expr))))))

    (defthm vl-oplist-p-of-vl-exprlist-names
      (implies (force (vl-exprlist-p x))
               (vl-oplist-p (vl-exprlist-ops x)))
      :hints(("Goal" :use ((:instance lemma (flag 'list))))))))



(defsection vl-expr-has-ops

  (mutual-recursion

   (defund vl-expr-has-ops-aux (ops x)
     (declare (xargs :guard (and (vl-oplist-p ops)
                                 (true-listp ops)
                                 (vl-expr-p x))
                     :measure (two-nats-measure (acl2-count x) 1)))
     (cond ((vl-fast-atom-p x)
            nil)
           ((member (vl-nonatom->op x) ops)
            t)
           (t
            (vl-exprlist-has-ops-aux ops (vl-nonatom->args x)))))

   (defund vl-exprlist-has-ops-aux (ops x)
     (declare (xargs :guard (and (vl-oplist-p ops)
                                 (true-listp ops)
                                 (vl-exprlist-p x))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (or (vl-expr-has-ops-aux ops (car x))
           (vl-exprlist-has-ops-aux ops (cdr x))))))

  (local
   (defthm lemma
     (case flag
       (expr (implies (vl-expr-p x)
                      (equal (vl-expr-has-ops-aux ops x)
                             (intersectp-equal ops (vl-expr-ops x)))))
       (atts t)
       (t    (implies (vl-exprlist-p x)
                      (equal (vl-exprlist-has-ops-aux ops x)
                             (intersectp-equal ops (vl-exprlist-ops x))))))
     :rule-classes nil
     :hints(("Goal"
             :induct (vl-expr-induct flag x)
             :in-theory (enable vl-expr-ops
                                vl-exprlist-ops
                                vl-expr-has-ops-aux
                                vl-exprlist-has-ops-aux)))))

  (local (defthm vl-expr-has-ops-aux-removal
           (implies (force (vl-expr-p x))
                    (equal (vl-expr-has-ops-aux ops x)
                           (intersectp-equal ops (vl-expr-ops x))))
           :hints(("Goal" :use ((:instance lemma (flag 'expr)))))))

  (local (defthm vl-exprlist-has-ops-aux-removal
           (implies (force (vl-exprlist-p x))
                    (equal (vl-exprlist-has-ops-aux ops x)
                           (intersectp-equal ops (vl-exprlist-ops x))))
           :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

  (defun vl-expr-has-ops (ops x)
    (declare (xargs :guard (and (vl-oplist-p ops)
                                (vl-expr-p x))))
    (mbe :logic (intersectp-equal ops (vl-expr-ops x))
         :exec (vl-expr-has-ops-aux (redundant-list-fix ops) x)))

  (defun vl-exprlist-has-ops (ops x)
    (declare (xargs :guard (and (vl-oplist-p ops)
                                (vl-exprlist-p x))))
    (mbe :logic (intersectp-equal ops (vl-exprlist-ops x))
         :exec (vl-exprlist-has-ops-aux (redundant-list-fix ops) x))))



(define vl-zbitlist-p ((x vl-bitlist-p))
  (if (consp x)
      (and (equal (car x) :vl-zval)
           (vl-zbitlist-p (cdr x)))
    t))

(define vl-zatom-p (x)
  (and (vl-atom-p x)
       (let ((guts (vl-atom->guts x)))
         (and (vl-weirdint-p guts)
              (vl-zbitlist-p (vl-weirdint->bits guts))))))

(define vl-obviously-true-expr-p ((x vl-expr-p))
  (and (vl-fast-atom-p x)
       (vl-fast-constint-p (vl-atom->guts x))
       (equal (vl-constint->value (vl-atom->guts x)) 1)))

(define vl-obviously-false-expr-p ((x vl-expr-p))
  (and (vl-fast-atom-p x)
       (vl-fast-constint-p (vl-atom->guts x))
       (equal (vl-constint->value (vl-atom->guts x)) 0)))



(define vl-make-index (n)
  :parents (expr-tools)
  :short "Safely create a constant integer atom whose value is n."
  :long "<p>@('n') is expected to be a natural number, but our guard is only
@('t').  We cause a hard error if we are given a non-natural number index, or
one which is too large.  BOZO consider a stronger guard.</p>"

  (let* ((value  (if (natp n)
                     n
                   (prog2$ (er hard? 'vl-make-index
                               "Proposed index is not a natural: ~x0." n)
                           0)))
         (width (+ 1 (integer-length value))))
    (if (<= width 31)
        ;; Prefer to make indices that look like plain decimal numbers, I
        ;; didn't used to hons these, but now it seems like a good idea since
        ;; the same indicies may be needed frequently.
        (make-honsed-vl-atom
           :guts (make-honsed-vl-constint :origwidth 32
                                          :origtype :vl-signed
                                          :wasunsized t
                                          :value value)
           :finalwidth 32
           :finaltype :vl-signed)
        (make-honsed-vl-atom
         :guts (make-honsed-vl-constint :origwidth width
                                        :origtype :vl-signed
                                        :value value)
         :finalwidth width
         :finaltype :vl-signed)))

  ///

  (defthm vl-atom-p-of-vl-make-index
    (vl-atom-p (vl-make-index n)))

  (defthm vl-expr-resolved-p-of-vl-make-index
    (vl-expr-resolved-p (vl-make-index n))
    :hints(("Goal" :in-theory (enable vl-expr-resolved-p))))

  (defthm vl-resolved->val-of-vl-make-index
    (equal (vl-resolved->val (vl-make-index n))
           (nfix n))
    :hints(("Goal" :in-theory (enable vl-resolved->val))))

  (defthm posp-of-vl-expr->finalwidth-of-vl-make-index
    (posp (vl-expr->finalwidth (vl-make-index n)))
    :rule-classes :type-prescription))





(define vl-sysfunexpr-p ((x vl-expr-p))
  (and (vl-fast-atom-p x)
       (vl-fast-sysfunname-p (vl-atom->guts x))))

(define vl-sysfunexpr->name ((x (and (vl-expr-p x)
                                     (vl-sysfunexpr-p x))))
  (string-fix (vl-sysfunname->name (vl-atom->guts x)))
  :guard-hints(("Goal" :in-theory (enable vl-sysfunexpr-p)))
  ///
  (defthm stringp-of-vl-sysfunexpr->name
    (stringp (vl-sysfunexpr->name x))
    :rule-classes :type-prescription))


(define vl-$random-expr-p ((x vl-expr-p))
  :parents (expr-tools)
  :short "Recognize calls of the @('$random') system function."

  :long "<p>The syntax for @('$random') calls is described in Section 17.9.1 on
page 311:</p>

@({random_function ::= $random[ '(' seed ')' ]})

<p>Note that the @('seed') is supposed to be a reg, integer, or time variable.
In this recognizer, if a seed is provided we require it to be an identifier,
but we do not check what kind of identifier it is.</p>"

  (b* (((when (vl-fast-atom-p x))
        nil)
       (op   (vl-nonatom->op x))
       (args (vl-nonatom->args x))
       ((unless (and (eq op :vl-syscall)
                     (consp args)
                     (vl-sysfunexpr-p (first args))
                     (equal (vl-sysfunexpr->name (first args))
                            (hons-copy "$random"))))
        nil)
       ((when (= (len args) 1))
        ;; Seedless $random call -- this is fine
        t)
       ((when (and (= (len args) 2)
                   (vl-idexpr-p (second args))))
        ;; $random(seed) -- seed is supposed to be a reg, integer, or time
        ;; variable, but we only check that it's an identifier.
        t))
    nil)

  ///

  (defthm vl-nonatom-p-when-vl-$random-expr-p
    (implies (and (vl-$random-expr-p x)
                  (force (vl-expr-p x)))
             (vl-nonatom-p x))
    :rule-classes ((:rewrite :backchain-limit-lst 1))))



(defsection vl-expr-atoms
  :parents (expr-tools)
  :short "Gather all of the atoms throughout an expression."
  :long "<p><b>Signature:</b> @(call vl-expr-atoms) returns a @(see
vl-atomlist-p).</p>

<p>We simply gather all of the @(see vl-atom-p)s in the expression, with
repetition.  The resulting list may contain any @(see vl-atom-p), including
even odd things like hid pieces and function names, which you might not
usually think of as atoms.</p>

@(def vl-expr-atoms)"

  (defxdoc vl-exprlist-atoms
    :parents (expr-tools)
    :short "Gather all atoms used throughout an expression list."
    :long "<p>See @(see vl-expr-atoms).</p>")

  (mutual-recursion

   (defund vl-fast-expr-atoms (x acc)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atom-p x)
         (cons x acc)
       (vl-fast-exprlist-atoms (vl-nonatom->args x) acc)))

   (defund vl-fast-exprlist-atoms (x acc)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (consp x)
         (vl-fast-exprlist-atoms (cdr x)
                                 (vl-fast-expr-atoms (car x) acc))
       acc)))

  (mutual-recursion

   (defund vl-expr-atoms (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)
                     :verify-guards nil))
     (mbe :logic (if (vl-atom-p x)
                     (list x)
                   (vl-exprlist-atoms (vl-nonatom->args x)))
          :exec (reverse (vl-fast-expr-atoms x nil))))

   (defund vl-exprlist-atoms (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (mbe :logic (if (consp x)
                     (append (vl-expr-atoms (car x))
                             (vl-exprlist-atoms (cdr x)))
                   nil)
          :exec (reverse (vl-fast-exprlist-atoms x nil)))))

  (defttag vl-optimize)
  (never-memoize vl-fast-expr-atoms)
  (never-memoize vl-fast-exprlist-atoms)
  (progn!
   (set-raw-mode t)
   (defun vl-expr-atoms (x)
     (nreverse (vl-fast-expr-atoms x nil)))
   (defun vl-exprlist-atoms (x)
     (nreverse (vl-fast-exprlist-atoms x nil))))
  (defttag nil)

  (defthm true-listp-of-vl-expr-atoms
    (true-listp (vl-expr-atoms x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-atoms
    (true-listp (vl-exprlist-atoms x))
    :rule-classes :type-prescription)

  (encapsulate
    ()
    (local (FLAG::make-flag vl-fast-flag-expr-atoms
                            vl-fast-expr-atoms
                            :flag-mapping ((vl-fast-expr-atoms . expr)
                                           (vl-fast-exprlist-atoms . list))))

    (local (defthm-vl-fast-flag-expr-atoms vl-fast-expr-atoms-correct
             (expr (equal (vl-fast-expr-atoms x acc)
                          (revappend (vl-expr-atoms x) acc)))
             (list (equal (vl-fast-exprlist-atoms x acc)
                          (revappend (vl-exprlist-atoms x) acc)))
             :hints(("Goal"
                     :induct (vl-fast-flag-expr-atoms flag x acc)
                     :expand ((vl-fast-expr-atoms x acc)
                              (vl-fast-exprlist-atoms x acc)
                              (vl-expr-atoms x)
                              (vl-exprlist-atoms x))))))

    (verify-guards vl-expr-atoms
      :hints(("Goal" :in-theory (enable vl-expr-atoms
                                        vl-fast-expr-atoms
                                        vl-exprlist-atoms
                                        vl-fast-exprlist-atoms)))))

  (encapsulate
    ()
    (local (defthm lemma
             (case flag
               (expr (implies (vl-expr-p x)
                              (vl-atomlist-p (vl-expr-atoms x))))
               (atts t)
               (t (implies (vl-exprlist-p x)
                           (vl-atomlist-p (vl-exprlist-atoms x)))))
             :rule-classes nil
             :hints(("Goal"
                     :induct (vl-expr-induct flag x)
                     :expand ((vl-expr-atoms x)
                              (vl-exprlist-atoms x))))))

    (defthm vl-atomlist-p-of-vl-expr-atoms
      (implies (force (vl-expr-p x))
               (vl-atomlist-p (vl-expr-atoms x)))
      :hints(("Goal" :use ((:instance lemma (flag 'expr))))))

    (defthm vl-atomlist-p-of-vl-exprlist-names
      (implies (force (vl-exprlist-p x))
               (vl-atomlist-p (vl-exprlist-atoms x)))
      :hints(("Goal" :use ((:instance lemma (flag 'list))))))))



(define vl-exprlist-to-plainarglist
  ((x    vl-exprlist-p        "list to convert")
   &key
   (dir  vl-maybe-direction-p "direction for each new plainarg")
   (atts vl-atts-p            "attributes for each new plainarg"))
  :returns (ans vl-plainarglist-p :hyp :fguard)
  :parents (expr-tools)
  :short "Convert expressions into @(see vl-plainarg-p)s."

  (if (consp x)
      (cons (make-vl-plainarg :expr (car x)
                              :dir dir
                              :atts atts)
            (vl-exprlist-to-plainarglist-fn (cdr x) dir atts))
    nil)

  ///

  (defthm vl-exprlist-to-plainarglist-under-iff
    (iff (vl-exprlist-to-plainarglist x :dir dir :atts atts)
         (consp x)))

  (defthm len-of-vl-exprlist-to-plainarglist
    (equal (len (vl-exprlist-to-plainarglist x :dir dir :atts atts))
           (len x))))


(define vl-atomlist-collect-funnames ((x vl-atomlist-p))
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
    (vl-atomlist-collect-funnames (cdr x)))

  :prepwork ((local (in-theory (disable (force))))))


(define vl-expr-funnames ((x vl-expr-p))
  :returns (ans string-listp)
  :parents (expr-tools)
  :short "Collect the names of all functions that occur in a @(see vl-expr-p)
and return them as a string list."
  (vl-atomlist-collect-funnames (vl-expr-atoms x)))


(define vl-exprlist-funnames ((x vl-exprlist-p))
  :returns (ans string-listp)
  :parents (expr-tools)
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



(define vl-partition-plainargs
  ;; BOZO find this a better home
  ((x      vl-plainarglist-p "list to filter")
   ;; bozo make these optional
   (inputs   "accumulator for args with :dir :vl-input")
   (outputs  "accumulator for args with :dir :vl-output")
   (inouts   "accumulator for args with :dir :vl-inout")
   (unknowns "accumulator for args with :dir nil"))
  :returns (mv inputs outputs inouts unknowns)
  :parents (vl-plainarglist-p)

  (b* (((when (atom x))
        (mv inputs outputs inouts unknowns))
       (dir (vl-plainarg->dir (car x)))
       ((when (eq dir :vl-input))
        (vl-partition-plainargs (cdr x) (cons (car x) inputs) outputs inouts unknowns))
       ((when (eq dir :vl-output))
        (vl-partition-plainargs (cdr x) inputs (cons (car x) outputs) inouts unknowns))
       ((when (eq dir :vl-inout))
        (vl-partition-plainargs (cdr x) inputs outputs (cons (car x) inouts) unknowns)))
    (vl-partition-plainargs (cdr x) inputs outputs inouts (cons (car x) unknowns)))

  ///

  (defthm vl-partition-plainarg-basics
    (implies (and (force (vl-plainarglist-p x))
                  (force (vl-plainarglist-p inputs))
                  (force (vl-plainarglist-p outputs))
                  (force (vl-plainarglist-p inouts))
                  (force (vl-plainarglist-p unknowns)))
             (b* (((mv inputs outputs inouts unknowns)
                   (vl-partition-plainargs x inputs outputs inouts unknowns)))
               (and (vl-plainarglist-p inputs)
                    (vl-plainarglist-p outputs)
                    (vl-plainarglist-p inouts)
                    (vl-plainarglist-p unknowns))))))



(defsection vl-expr-selects
  :parents (expr-tools)
  :short "Collects up all the selection expressions (bit-selects, part-selects,
array indexing, and unresolved indexing) and returns them as a flat list of
expressions."

  (mutual-recursion

   (defund vl-expr-selects (x)
     ;; Assumes no nested selects
     (declare (xargs :guard (vl-expr-p x)
                     :measure (vl-expr-count x)))
     (b* (((when (vl-fast-atom-p x))
           nil)
          ((vl-nonatom x) x)
          ((when (or (eq x.op :vl-bitselect)
                     (eq x.op :vl-partselect-colon)
                     (eq x.op :vl-partselect-pluscolon)
                     (eq x.op :vl-partselect-minuscolon)
                     (eq x.op :vl-index)
                     (eq x.op :vl-array-index)))
           (list x)))
       (vl-exprlist-selects x.args)))

   (defund vl-exprlist-selects (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (vl-exprlist-count x)))
     (if (atom x)
         nil
       (append (vl-expr-selects (car x))
               (vl-exprlist-selects (cdr x))))))

  (flag::make-flag vl-flag-expr-selects
                   vl-expr-selects
                   :flag-mapping ((vl-expr-selects . expr)
                                  (vl-exprlist-selects . list)))

  (defthm-vl-flag-expr-selects
    (defthm vl-exprlist-p-of-vl-expr-selects
      (implies (force (vl-expr-p x))
               (vl-exprlist-p (vl-expr-selects x)))
      :flag expr)

    (defthm vl-exprlist-p-of-vl-exprlist-selects
      (implies (force (vl-exprlist-p x))
               (vl-exprlist-p (vl-exprlist-selects x)))
      :flag list)
    :hints(("Goal" :expand ((vl-exprlist-selects x)
                            (vl-expr-selects x))))))


(define vl-bitlist-from-nat ((x natp)
                             (width natp))
  :returns (bits vl-bitlist-p)
  :parents (expr-tools)
  :short "Turn a natural number into a vl-bitlist-p of the given width."
  (b* (((when (zp width)) nil)
       (width (1- width))
       (bit (if (logbitp width x)
                :vl-1val
              :vl-0val)))
    (cons bit (vl-bitlist-from-nat x width)))

  ///

  (defthm len-of-vl-bitlist-from-nat
    (equal (len (vl-bitlist-from-nat x width))
           (nfix width))))
