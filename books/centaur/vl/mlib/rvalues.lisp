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
(include-book "hid-tools")
(local (include-book "../util/arithmetic"))

#||
(defxdoc rvaluenames
  :parents (mlib)

  :short "Functions for gathering the names of identifiers that are driving
other wires."

  :long "<p>These functions compute lists of simple identifiers (i.e., @(see
vl-id-p) atoms) that are actually driving other wires in the module.  Note that
we deal with simple identifiers and ignore any hierarchical identifiers being
used as rvalues.</p>

<p>There are many similarities to our functions for gathering @(see exprnames),
but the main difference is that the rvalue gathering functions are more
selective.  For instance, consider an assignment such as:</p>

<code>
out = data[addr];
</code>

<p>Here, we only consider <tt>data</tt> to be an rvalue, whereas if we just
gathered up all the @(see exprnames) from the right-hand side of the
assignment, we would think that both <tt>data</tt> and <tt>addr</tt> were
rvalues.</p>

<p>Gathering rvalues from module instances is a subtle business, and our
functions assume that the instances it encounters have already been @(see
argresolve)d.  No rvalues will be inferred from module instances whose
arguments have not been resolved.</p>")


(defsection vl-expr-rvaluenames
  :parents (rvalues vl-expr-p)

  :short "Gather @(see rvaluenames) from an expression."

  :long "<p><b>Signature:</b> @(call vl-expr-rvaluenames) returns a string
list.</p>

<p>We assume that <tt>x</tt> is being used in an rvalue position (that is, it
may be the right-hand side of some assignment, or may be used as the input to
some submodule.)</p>

<h3>Theorems</h3>

  @(thm true-listp-of-vl-expr-rvaluenames)
  @(thm true-listp-of-vl-exprlist-rvaluenames)
  @(thm string-listp-of-vl-expr-rvaluenames)
  @(thm string-listp-of-vl-exprlist-rvaluenames)

<h3>Definition</h3>

<p>For efficiency, we provide a tail-recursive implementation.</p>

  @(def vl-expr-rvaluenames)
  @(def vl-expr-rvaluenames-exec)"

  (mutual-recursion

   (defund vl-expr-rvaluenames-exec (x acc)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (cond ((vl-fast-atom-p x)
            (let ((guts (vl-atom->guts x)))
;; Gather any simple identifiers we find, but ignore any other
;; kinds of atoms (constants, strings, hierarchical id pieces,
;; etc.)
              (if (vl-fast-id-p guts)
                  (cons (vl-id->name guts) acc)
                acc)))

           ((mbe :logic (not (consp x))
                 :exec nil)
;; Stupid termination hack
            acc)

           (t
            (let ((op   (vl-nonatom->op x))
                  (args (vl-nonatom->args x)))
              (case op
                ((:vl-bitselect :vl-partselect-colon)
;; For foo[index] or foo[a:b], we gather names from foo only,
;; since the indicies are expected to be constants.
                 (if (vl-idexpr-p (first args))
                     (cons (vl-idexpr->name (first args)) acc)
                   acc))

                ((:vl-partselect-pluscolon :vl-partselect-minuscolon)
;; For foo[a+:b] or foo[a-:b] -- here, B is expected to be
;; a constant, but FOO and A may have wires in them.
                 (let* ((acc (if (vl-idexpr-p (first args))
                                 (cons (vl-idexpr->name (first args))
                                       acc)
                               acc)))
                   (vl-expr-rvaluenames-exec (second args) acc)))

                ((:vl-hid-dot :vl-hid-arraydot)
;; Don't look further at hierarchical ids.
                 acc)

                (otherwise
                 (vl-exprlist-rvaluenames-exec args acc)))))))

   (defund vl-exprlist-rvaluenames-exec (x acc)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (consp x)
         (vl-exprlist-rvaluenames-exec (cdr x)
                                       (vl-expr-rvaluenames-exec (car x) acc))
       acc)))


  (mutual-recursion

   (defund vl-expr-rvaluenames (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)
                     :verify-guards nil))
     (mbe :logic
          (cond ((vl-atom-p x)
                 (let ((guts (vl-atom->guts x)))
                   (if (vl-id-p guts)
                       (list (vl-id->name guts))
                     nil)))
                ((not (consp x))
                 nil)
                (t
                 (let ((op   (vl-nonatom->op x))
                       (args (vl-nonatom->args x)))
                   (case op
                     ((:vl-bitselect :vl-partselect-colon)
                      (if (vl-idexpr-p (first args))
                          (list (vl-idexpr->name (first args)))
                        nil))
                     ((:vl-partselect-pluscolon :vl-partselect-minuscolon)
                      (if (vl-idexpr-p (first args))
                          (cons (vl-idexpr->name (first args))
                                (vl-expr-rvaluenames (second args)))
                        (vl-expr-rvaluenames (second args))))
                     ((:vl-hid-dot :vl-hid-arraydot)
                      nil)
                     (t
                      (vl-exprlist-rvaluenames args))))))
          :exec
          (reverse (vl-expr-rvaluenames-exec x nil))))

   (defund vl-exprlist-rvaluenames (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (mbe :logic
          (if (consp x)
              (append (vl-expr-rvaluenames (car x))
                      (vl-exprlist-rvaluenames (cdr x)))
            nil)
          :exec
          (reverse (vl-exprlist-rvaluenames-exec x nil)))))

  (defthm true-listp-of-vl-expr-rvaluenames
    (true-listp (vl-expr-rvaluenames x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-rvaluenames
    (true-listp (vl-exprlist-rvaluenames x))
    :rule-classes :type-prescription)

  (FLAG::make-flag vl-fast-flag-expr-rvaluenames
                   vl-expr-rvaluenames-exec
                   :flag-mapping ((vl-expr-rvaluenames-exec . expr)
                                  (vl-exprlist-rvaluenames-exec . list)))

  (defthm-vl-fast-flag-expr-rvaluenames lemma
    (expr (equal (vl-expr-rvaluenames-exec x acc)
                 (revappend (vl-expr-rvaluenames x) acc))
          :name vl-expr-rvaluenames-exec-removal)
    (list (equal (vl-exprlist-rvaluenames-exec x acc)
                 (revappend (vl-exprlist-rvaluenames x) acc))
          :name vl-exprlist-rvaluenames-exec-removal)
    :hints(("Goal"
            :induct (vl-fast-flag-expr-rvaluenames flag x acc)
            :expand ((vl-expr-rvaluenames-exec x acc)
                     (vl-exprlist-rvaluenames-exec x acc)
                     (vl-expr-rvaluenames x)
                     (vl-exprlist-rvaluenames x)))))

  (verify-guards vl-expr-rvaluenames
                 :hints(("Goal" :in-theory (enable vl-expr-rvaluenames
                                                   vl-expr-rvaluenames-exec
                                                   vl-exprlist-rvaluenames
                                                   vl-exprlist-rvaluenames-exec))))

  (FLAG::make-flag vl-flag-expr-rvaluenames
                   vl-expr-rvaluenames
                   :flag-mapping ((vl-expr-rvaluenames . expr)
                                  (vl-exprlist-rvaluenames . list)))

  (defthm-vl-flag-expr-rvaluenames lemma
    (expr (implies (force (vl-expr-p x))
                   (string-listp (vl-expr-rvaluenames x)))
          :name string-listp-of-vl-expr-rvaluenames)
    (list (implies (force (vl-exprlist-p x))
                   (string-listp (vl-exprlist-rvaluenames x)))
          :name string-listp-of-vl-exprlist-rvaluenames)
    :hints(("Goal"
            :induct (vl-flag-expr-rvaluenames flag x)
            :expand ((vl-expr-rvaluenames x)
                     (vl-exprlist-rvaluenames x))))))



(defmacro def-vl-rvaluenames (&key type
                                   exec-body
                                   body
                                   name-exec
                                   name)
  (let* ((mksym-package-symbol 'vl)

         (rec            (mksym type '-p))
         (collect-exec   (or name-exec (mksym type '-rvaluenames-exec)))
         (collect        (or name (mksym type '-rvaluenames)))
         (remove-thm     (mksym collect-exec '-removal))
         (str-thm        (mksym 'string-listp-of- collect))

         (rec-s          (symbol-name rec))
         (collect-s      (symbol-name collect))
         (collect-exec-s (symbol-name collect-exec))
         (remove-thm-s   (symbol-name remove-thm))
         (str-thm-s      (symbol-name str-thm))

         (short          (str::cat "Gather @(see rvaluenames) from a @(see " rec-s ")."))

         (long           (str::cat "<p><b>Signature</b> @(call " collect-s ") returns a
string list.</p>

<h3>Definition</h3>

<p>For efficiency we use a tail-recursive, accumulator-style functions to do
the collection.  Under the hood, we also use <tt>nreverse</tt>
optimization.</p>

  @(def " collect-s ")
  @(def " collect-exec-s ")

<h3>Theorems</h3>

  @(thm " remove-thm-s ")
  @(thm " str-thm-s ")")))

    `(defsection ,collect
       :parents (,rec rvalues)
       :short ,short
       :long ,long

       (defund ,collect-exec (x acc)
         (declare (xargs :guard (,rec x)))
         ,exec-body)

       (defund ,collect (x)
         (declare (xargs :guard (,rec x)
                         :verify-guards nil))
         (mbe :logic ,body
              :exec (reverse (,collect-exec x nil))))

       (local (in-theory (enable ,collect-exec ,collect)))

       (defthm ,remove-thm
         (equal (,collect-exec x acc)
                (append (rev (,collect x))
                        acc)))

       (verify-guards ,collect)

       (defthm ,str-thm
         (implies (force (,rec x))
                  (string-listp (,collect x))))

       (defttag vl-optimize)
       (progn!
        (set-raw-mode t)
        (setf (gethash ',collect-exec ACL2::*never-profile-ht*) t)
        (defun ,collect (x)
          (nreverse (,collect-exec x nil))))
       (defttag nil))))



(defmacro def-vl-rvaluenames-list (&key list element)
  (let* ((mksym-package-symbol 'vl)

         (list-rec             (mksym list '-p))
         (list-collect         (mksym list '-rvaluenames))
         (list-collect-exec    (mksym list '-rvaluenames-exec))
         (element-collect      (mksym element '-rvaluenames))
         (element-collect-exec (mksym element '-rvaluenames-exec))
         (str-thm              (mksym 'string-listp-of- list-collect))

         (list-rec-s          (symbol-name list-rec))
         (list-collect-s      (symbol-name list-collect))
         (list-collect-exec-s (symbol-name list-collect-exec))
         (str-thm-s           (symbol-name str-thm))

         (short (str::cat "Gather @(see rvaluenames) from a @(see " list-rec-s ")."))

         (long (str::cat "<p><b>Signature</b> @(call " list-collect-s ")
returns a string list.</p>

<h3>Definition</h3>

  @(def " list-collect-s ")
  @(def " list-collect-exec-s ")

<h3>Theorems</h3>

<p>Note that we use @(see defmappapend), and do not attempt to display the
theorems it generates here.  Additionally, we prove:</p>

  @(thm " str-thm-s ")")))

    `(defsection ,list-collect
       :parents (,list-rec rvalues)
       :short ,short
       :long ,long

       (defmapappend ,list-collect (x)
         (,element-collect x)
         :guard (,list-rec x)
         :transform-true-list-p t
         :transform-exec ,element-collect-exec)

       (local (in-theory (enable ,list-collect)))

       (defthm ,str-thm
         (implies (force (,list-rec x))
                  (string-listp (,list-collect x)))))))


(def-vl-rvaluenames
  :type vl-assign
  :exec-body (vl-expr-rvaluenames-exec (vl-assign->expr x) acc)
  :body (vl-expr-rvaluenames (vl-assign->expr x)))

(def-vl-rvaluenames-list
  :list vl-assignlist
  :element vl-assign)

(encapsulate
 ()
 (local (in-theory (disable (force))))

 (def-vl-rvaluenames
   :type vl-plainarg
   :exec-body
   ;; BOZO consider warning about unresolved arguments
   (b* (((vl-plainarg x) x))
       (if (and x.expr
                (or (eq x.dir :vl-input)
                    (eq x.dir :vl-inout))
                ;; Special hack.  If we've identified that this input isn't ever
                ;; read by the submodule, don't consider it to be an rvalue.
                (not (assoc-equal "VL_UNUSED_INPUT" x.atts)))
           (vl-expr-rvaluenames-exec x.expr acc)
         acc))
   :body
   (b* (((vl-plainarg x) x))
       (if (and x.expr
                (or (eq x.dir :vl-input)
                    (eq x.dir :vl-inout))
                (not (assoc-equal "VL_UNUSED_INPUT" x.atts)))
           (vl-expr-rvaluenames x.expr)
         nil))))

(def-vl-rvaluenames-list
  :list vl-plainarglist
  :element vl-plainarg)

(def-vl-rvaluenames
  :type vl-gateinst
  :exec-body (vl-plainarglist-rvaluenames-exec (vl-gateinst->args x) acc)
  :body (vl-plainarglist-rvaluenames (vl-gateinst->args x)))

(def-vl-rvaluenames-list
  :list vl-gateinstlist
  :element vl-gateinst)

(def-vl-rvaluenames
  :type vl-modinst
  :exec-body
  (b* (((vl-modinst x) x))
      (if (vl-arguments->namedp x.portargs)
          (prog2$ (cw "; ~s0: in vl-modinst-rvaluenames-exec, skipping ~s1 ~%~
                       ; of module ~s2 due to unresolved arguments."
                      (vl-location-string x.loc) x.instname x.modname)
                  acc)
        (vl-plainarglist-rvaluenames-exec (vl-arguments->args x.portargs) acc)))
  :body
  (b* (((vl-modinst x) x))
      (if (vl-arguments->namedp x.portargs)
          nil
        (vl-plainarglist-rvaluenames (vl-arguments->args x.portargs)))))

(def-vl-rvaluenames-list
  :list vl-modinstlist
  :element vl-modinst)

(def-vl-rvaluenames
  :type vl-assignstmt
  :exec-body (vl-expr-rvaluenames-exec (vl-assignstmt->expr x) acc)
  :body (vl-expr-rvaluenames (vl-assignstmt->expr x)))

(def-vl-rvaluenames
  :type vl-atomicstmt
  :exec-body
  (case (tag x)
    (:vl-assignstmt   (vl-assignstmt-rvaluenames-exec x acc))
    (otherwise        acc))
  :body
  (case (tag x)
    (:vl-assignstmt   (vl-assignstmt-rvaluenames x))
    (otherwise        nil)))


(defsection vl-stmt-rvaluenames

  (mutual-recursion

   (defund vl-stmt-rvaluenames-exec (x acc)
     (declare (xargs :guard (vl-stmt-p x)
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (cond ((vl-fast-atomicstmt-p x)
            (vl-atomicstmt-rvaluenames-exec x acc))

           ((eq (vl-compoundstmt->type x) :vl-ifstmt)
            ;; Well, this is iffy, but I think the condition should be
            ;; considered to be an rvalue, since its value is in some
            ;; sense being read to determine what to do.
            (let* ((acc (vl-expr-rvaluenames-exec (vl-ifstmt->condition x) acc)))
              (vl-stmtlist-rvaluenames-exec (vl-compoundstmt->stmts x) acc)))

           ((eq (vl-compoundstmt->type x) :vl-forstmt)
            (let* ((acc (vl-expr-rvaluenames-exec (vl-forstmt->initrhs x) acc))
                   (acc (vl-expr-rvaluenames-exec (vl-forstmt->nextrhs x) acc)))
              (vl-stmtlist-rvaluenames-exec (vl-compoundstmt->stmts x) acc)))

           (t
            (vl-stmtlist-rvaluenames-exec (vl-compoundstmt->stmts x) acc))))

   (defund vl-stmtlist-rvaluenames-exec (x acc)
     (declare (xargs :guard (vl-stmtlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         acc
       (let ((acc (vl-stmt-rvaluenames-exec (car x) acc)))
         (vl-stmtlist-rvaluenames-exec (cdr x) acc)))))

  (mutual-recursion
   (defund vl-stmt-rvaluenames (x)
     (declare (xargs :guard (vl-stmt-p x)
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (mbe :logic
          (cond ((vl-atomicstmt-p x)
                 (vl-atomicstmt-rvaluenames x))

                ((eq (vl-compoundstmt->type x) :vl-ifstmt)
                 (append (vl-expr-rvaluenames (vl-ifstmt->condition x))
                         (vl-stmtlist-rvaluenames (vl-compoundstmt->stmts x))))


                ((eq (vl-compoundstmt->type x) :vl-forstmt)
                 (append (vl-expr-rvaluenames (vl-forstmt->initrhs x))
                         (vl-expr-rvaluenames (vl-forstmt->nextrhs x))
                         (vl-stmtlist-rvaluenames (vl-compoundstmt->stmts x))))

                (t
                 (vl-stmtlist-rvaluenames (vl-compoundstmt->stmts x))))
          :exec
          (reverse (vl-stmt-rvaluenames-exec x nil))))

   (defund vl-stmtlist-rvaluenames (x)
     (declare (xargs :guard (vl-stmtlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (mbe :logic
          (if (atom x)
              nil
            (append (vl-stmt-rvaluenames (car x))
                    (vl-stmtlist-rvaluenames (cdr x))))
          :exec
          (reverse (vl-stmtlist-rvaluenames-exec x nil)))))

  (flag::make-flag vl-flag-stmt-rvaluenames-exec
                   vl-stmt-rvaluenames-exec
                   :flag-mapping ((vl-stmt-rvaluenames-exec . stmt)
                                  (vl-stmtlist-rvaluenames-exec . list)))

  (defthm-vl-flag-stmt-rvaluenames-exec lemma
    (stmt (equal (vl-stmt-rvaluenames-exec x acc)
                 (revappend (vl-stmt-rvaluenames x) acc))
          :name vl-stmt-rvaluenames-exec-removal)
    (list (equal (vl-stmtlist-rvaluenames-exec x acc)
                 (revappend (vl-stmtlist-rvaluenames x) acc))
          :name vl-stmtlist-rvaluenames-exec-removal)
    :hints(("Goal"
            :induct (vl-flag-stmt-rvaluenames-exec flag x acc)
            :expand ((vl-stmt-rvaluenames x)
                     (vl-stmtlist-rvaluenames x)
                     (vl-stmt-rvaluenames-exec x acc)
                     (vl-stmtlist-rvaluenames-exec x acc)))))

  (defthm-vl-flag-stmt-p lemma
    (stmt (implies (force (vl-stmt-p x))
                   (string-listp (vl-stmt-rvaluenames x)))
          :name string-listp-of-vl-stmt-rvaluenames)
    (list (implies (force (vl-stmtlist-p x))
                   (string-listp (vl-stmtlist-rvaluenames x)))
          :name string-listp-of-vl-stmtlist-rvaluenames)
    :hints(("Goal"
            :induct (vl-flag-stmt-p flag x)
            :expand ((vl-stmt-rvaluenames x)
                     (vl-stmtlist-rvaluenames x)))))

  (verify-guards vl-stmt-rvaluenames-exec)
  (verify-guards vl-stmt-rvaluenames
                 :hints(("Goal" :in-theory (enable vl-stmt-rvaluenames
                                                   vl-stmtlist-rvaluenames)))))

(def-vl-rvaluenames
  :type vl-always
  :exec-body (vl-stmt-rvaluenames-exec (vl-always->stmt x) acc)
  :body (vl-stmt-rvaluenames (vl-always->stmt x)))

(def-vl-rvaluenames-list
  :list vl-alwayslist
  :element vl-always)

(def-vl-rvaluenames
  :type vl-initial
  :exec-body (vl-stmt-rvaluenames-exec (vl-initial->stmt x) acc)
  :body (vl-stmt-rvaluenames (vl-initial->stmt x)))

(def-vl-rvaluenames-list
  :list vl-initiallist
  :element vl-initial)

(def-vl-rvaluenames
  :type vl-module
  :exec-body
  (b* ((assigns   (vl-module->assigns x))
       (initials  (vl-module->initials x))
       (alwayses  (vl-module->alwayses x))
       (gateinsts (vl-module->gateinsts x))
       (modinsts  (vl-module->modinsts x))
       (acc (vl-gateinstlist-rvaluenames-exec gateinsts acc))
       (acc (vl-modinstlist-rvaluenames-exec modinsts acc))
       (acc (vl-assignlist-rvaluenames-exec assigns acc))
       (acc (vl-alwayslist-rvaluenames-exec alwayses acc))
       (acc (vl-initiallist-rvaluenames-exec initials acc)))
      acc)
  :body
  (b* ((assigns   (vl-module->assigns x))
       (initials  (vl-module->initials x))
       (alwayses  (vl-module->alwayses x))
       (gateinsts (vl-module->gateinsts x))
       (modinsts  (vl-module->modinsts x)))
      (append (vl-gateinstlist-rvaluenames gateinsts)
              (vl-modinstlist-rvaluenames modinsts)
              (vl-assignlist-rvaluenames assigns)
              (vl-alwayslist-rvaluenames alwayses)
              (vl-initiallist-rvaluenames initials))))

||#