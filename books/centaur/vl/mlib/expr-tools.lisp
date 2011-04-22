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



(defsection vl-expr-resolved-p
  :parents (expr-tools)
  :short "Recognizes plain constant integer expressions."
  :long "<p>We say an expression is <b>resolved</b> when it is just an atomic,
integer value that is free of X/Z bits.  We often expect to be able to resolve
the expressions that occur in ranges like <tt>wire [3:0] foo;</tt> and in
selects.</p>"

  (definlined vl-expr-resolved-p (x)
    (declare (xargs :guard (vl-expr-p x)))
    (and (vl-fast-atom-p x)
         (vl-fast-constint-p (vl-atom->guts x)))))


(deflist vl-exprlist-resolved-p (x)
  (vl-expr-resolved-p x)
  :guard (vl-exprlist-p x)
  :elementp-of-nil nil
  :parents (expr-tools))


(defsection vl-resolved->val
  :parents (expr-tools)
  :short "Get the value from a resolved expression."
  :long "<p>This is guaranteed to be a natural number.</p>"

  (definlined vl-resolved->val (x)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-expr-resolved-p x))
                    :guard-hints (("Goal" :in-theory (enable vl-expr-resolved-p)))))
    (mbe :logic (nfix (vl-constint->value (vl-atom->guts x)))
         :exec (vl-constint->value (vl-atom->guts x))))

  (local (in-theory (enable vl-resolved->val)))

  (defthm natp-of-vl-resolved->val
    (natp (vl-resolved->val x))
    :rule-classes :type-prescription))



(defsection vl-idexpr-p
  :parents (expr-tools)
  :short "Recognize plain identifier expressions."
  :long "<p>This recognizes simple, non-hierarchical identifier expressions
like <tt>foo</tt>.</p>"

  (definlined vl-idexpr-p (x)
    (declare (xargs :guard (vl-expr-p x)))
    (and (vl-fast-atom-p x)
         (vl-fast-id-p (vl-atom->guts x)))))

(deflist vl-idexprlist-p (x)
  (vl-idexpr-p x)
  :guard (vl-exprlist-p x)
  :elementp-of-nil nil
  :parents (expr-tools))


(defsection vl-idexpr->name
  :parents (expr-tools)
  :short "Get the name from a @(see vl-idexpr-p)."
  :long "<p>This is guaranteed to be a string.</p>"

  (definlined vl-idexpr->name (x)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-idexpr-p x))
                    :guard-hints(("Goal" :in-theory (enable vl-idexpr-p)))))
    (mbe :logic (string-fix (vl-id->name (vl-atom->guts x)))
         :exec (vl-id->name (vl-atom->guts x))))

  (local (in-theory (enable vl-idexpr->name)))

  (defthm stringp-of-vl-idexpr->name
    (stringp (vl-idexpr->name x))
    :rule-classes :type-prescription))


(defsection vl-idexprlist->names

  (defprojection vl-idexprlist->names (x)
    (vl-idexpr->name x)
    :guard (and (vl-exprlist-p x)
                (vl-idexprlist-p x))
    :parents (expr-tools))

  (local (in-theory (enable vl-idexprlist->names)))

  (defthm string-listp-of-vl-idexprlist->names
    (string-listp (vl-idexprlist->names x))))



(defsection vl-idexpr
  :parents (expr-tools)
  :short "Construct an @(see vl-idexpr-p)."
  :long "<p>@(call vl-idexpr) constructs a simple identifier expression with the
given name, width, and type.</p>"

  (definlined vl-idexpr (name finalwidth finaltype)
    (declare (xargs :guard (and (stringp name)
                                (vl-maybe-natp finalwidth)
                                (vl-maybe-exprtype-p finaltype))))
    ;; I didn't used to hons these, but now it seems like a good idea
    ;; since the same identifier may be needed in several contexts.
    (make-honsed-vl-atom :guts (make-honsed-vl-id :name name)
                         :finalwidth finalwidth
                         :finaltype finaltype))

  (local (in-theory (enable vl-idexpr-p vl-idexpr vl-idexpr->name)))

  (defthm vl-idexpr-p-of-vl-idexpr
    (implies (and (force (stringp name))
                  (force (vl-maybe-natp finalwidth))
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
                  (force (vl-maybe-natp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (vl-atom-p (vl-idexpr name finalwidth finaltype)))))



(defsection vl-make-idexpr-list

  (defprojection vl-make-idexpr-list (x finalwidth finaltype)
    (vl-idexpr x finalwidth finaltype)
    :guard (and (string-listp x)
                (vl-maybe-natp finalwidth)
                (vl-maybe-exprtype-p finaltype))
    :result-type vl-exprlist-p
    :parents (expr-tools)
    :long "<p>Each expression is given the specified <tt>finalwidth</tt> and
<tt>finaltype</tt>.</p>")

  (local (in-theory (enable vl-make-idexpr-list)))

  (defthm vl-idexprlist-p-of-vl-make-idexpr-list
    (implies (and (force (string-listp x))
                  (force (vl-maybe-natp finalwidth))
                  (force (vl-maybe-exprtype-p finaltype)))
             (vl-idexprlist-p (vl-make-idexpr-list x finalwidth finaltype))))

  (defthm vl-idexprlist->names-of-vl-make-idexpr-list
    (implies (force (string-listp x))
             (equal (vl-idexprlist->names (vl-make-idexpr-list x finalwidth finaltype))
                    x))))



(defsection vl-expr-widthsfixed-p
  :parents (expr-tools)
  :short "@(call vl-expr-widthsfixed-p) determines if all of the
<tt>finalwidth</tt> fields throughout an expression are natural numbers."

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
<tt>(* foo = bar *)</tt>-style attributes.</p>

<p><tt>vl-expr-names</tt> is necessarily mutually-recursive with
<tt>vl-exprlist-names</tt>.  For efficiency we use a tail-recursive,
accumulator-style functions to do the collection.  Under the hood, we also use
<tt>nreverse</tt> optimization.</p>"

  (defxdoc vl-exprlist-names
    :parents (expr-tools)
    :short "Gather the names of all @(see vl-id-p) atoms throughout an
expression list."
    :long "<p>See @(see vl-expr-names)</p>")

  (mutual-recursion

   (defund vl-expr-names-exec (x acc)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atom-p x)
         (let ((guts (vl-atom->guts x)))
           (if (vl-fast-id-p guts)
               (cons (vl-id->name guts) acc)
             acc))
       (vl-exprlist-names-exec (vl-nonatom->args x) acc)))

   (defund vl-exprlist-names-exec (x acc)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (consp x)
         (vl-exprlist-names-exec (cdr x)
                                 (vl-expr-names-exec (car x) acc))
       acc)))

  (mutual-recursion

   (defund vl-expr-names (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)
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
                     :measure (two-nats-measure (acl2-count x) 0)))
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
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-expr-names-exec ACL2::*never-profile-ht*) t)
   (setf (gethash 'vl-exprlist-names-exec ACL2::*never-profile-ht*) t)
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
    :hints(("Goal" :use ((:instance lemma (flag 'list)))))))





(defsection vl-expr-ops
  :parents (expr-tools)
  :short "Gather all of the operators used throughout an expression."
  :long "<p><b>Signature:</b> @(call vl-expr-ops) returns a @(see
vl-oplist-p).</p>

<p>We simply gather all of the operators, with repetition.  The resulting list
may contain any @(see vl-op-p), including even odd such as <tt>:vl-syscall</tt>
or <tt>:vl-hid-dot</tt>, which you might not ordinarily think of as an
operator.</p>

@(def vl-expr-ops)"

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
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-fast-expr-ops ACL2::*never-profile-ht*) t)
   (setf (gethash 'vl-fast-exprlist-ops ACL2::*never-profile-ht*) t)
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



(defund vl-zbitlist-p (x)
  (declare (xargs :guard (vl-bitlist-p x)))
  (if (consp x)
      (and (equal (car x) :vl-zval)
           (vl-zbitlist-p (cdr x)))
    t))

(defund vl-zatom-p (x)
  (declare (xargs :guard t))
  (and (vl-atom-p x)
       (let ((guts (vl-atom->guts x)))
         (and (vl-weirdint-p guts)
              (vl-zbitlist-p (vl-weirdint->bits guts))))))

(defund vl-obviously-true-expr-p (x)
  (declare (xargs :guard (vl-expr-p x)))
  (and (vl-fast-atom-p x)
       (vl-fast-constint-p (vl-atom->guts x))
       (equal (vl-constint->value (vl-atom->guts x)) 1)))

(defund vl-obviously-false-expr-p (x)
  (declare (xargs :guard (vl-expr-p x)))
  (and (vl-fast-atom-p x)
       (vl-fast-constint-p (vl-atom->guts x))
       (equal (vl-constint->value (vl-atom->guts x)) 0)))




(defsection vl-make-index

  (defund vl-make-index (n)
    (declare (xargs :guard t :verify-guards nil))

; Safely create a constant integer atom whose value is n.  N is expected to be
; a natural number, but our guard is only t.  We complain if we are given a
; non-natural number index, or one which is too large.

; BOZO consider a stronger guard.

    (let* ((value  (if (natp n)
                       n
                     (prog2$ (er hard? 'vl-make-index
                                 "Proposed index is not a natural: ~x0." n)
                             0)))
           (width (+ 1 (integer-length value))))
      (if (<= width 31)
          ;; Prefer to make indices that look like plain decimal numbers,
          ;; I didn't used to hons these, but now it seems like a good idea
          ;; since the same indicies may be needed frequently.
          (make-honsed-vl-atom
           :guts (make-honsed-vl-constint :origwidth 32
                                          :origtype :vl-signed
                                          :value value)
           :finalwidth 32
           :finaltype :vl-signed)
        (make-honsed-vl-atom
         :guts (make-honsed-vl-constint :origwidth width
                                        :origtype :vl-signed
                                        :value value)
         :finalwidth width
         :finaltype :vl-signed))))

  (verify-guards vl-make-index)

  (local (in-theory (enable vl-make-index)))

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





(defund vl-sysfunexpr-p (x)
  (declare (xargs :guard (vl-expr-p x)))
  (and (vl-fast-atom-p x)
       (vl-fast-sysfunname-p (vl-atom->guts x))))

(defund vl-sysfunexpr->name (x)
  (declare (xargs :guard (and (vl-expr-p x)
                              (vl-sysfunexpr-p x))
                  :guard-hints(("Goal" :in-theory (enable vl-sysfunexpr-p)))))
  (string-fix (vl-sysfunname->name (vl-atom->guts x))))

(defthm stringp-of-vl-sysfunexpr->name
  (stringp (vl-sysfunexpr->name x))
  :rule-classes :type-prescription)

(defsection vl-$random-expr-p
  :parents (expr-tools)
  :short "Recognize calls of the <tt>$random</tt> system function."
  :long "<p>The syntax for <tt>$random</tt> calls is described in Section
17.9.1 on page 311:</p>

<code>random_function ::= $random[ '(' seed ')' ]</code>

<p>Note that the <tt>seed</tt> is supposed to be a reg, integer, or time
variable.  In this recognizer, if a seed is provided we require it to be an
identifier, but we do not check what kind of identifier it is.</p>"

  (defund vl-$random-expr-p (x)
    (declare (xargs :guard (vl-expr-p x)))
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
      nil))

  (local (in-theory (enable vl-$random-expr-p)))

  (defthm vl-nonatom-p-when-vl-$random-expr-p
    (implies (and (vl-$random-expr-p x)
                  (force (vl-expr-p x)))
             (vl-nonatom-p x))
    :rule-classes ((:rewrite :backchain-limit-lst 1))))

