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
(include-book "lvalues")
(local (include-book "../util/arithmetic"))


#|

(defxdoc lvalues-mentioning
  :parents (mlib)
  :short "Tools for gathering up expressions where a wire is being used as
an lvalue.")


(defsection vl-expr-lvalues-mentioning-aux-exec

; Returns a list of expressions that might be
;   - ordinary identifiers that match name,
;   - bit selects from name, or
;   - part selects from name

 (mutual-recursion

 (defund vl-expr-lvalues-mentioning-aux-exec (name x acc)
  (declare (xargs :guard (and (stringp name)
                              (vl-expr-p x)
                              (vl-expr-lvaluep x))
                  :measure (two-nats-measure (acl2-count x) 1)))
     (cond ((vl-fast-atom-p x)
            (let ((guts (vl-atom->guts x)))
              (if (vl-fast-id-p guts)
                  (if (equal (vl-id->name guts) name)
                      (cons x acc)
                    acc)
                ;; The only other thing that might legitimately be here is a
                ;; hierarchical identifier, which we ignore.
                acc)))

           ((mbe :logic (not (consp x))
                 :exec nil)
            ;; Stupid termination hack
            acc)

           (t
            ;; An lvalue should consist of identifiers, part selects, bit selects,
            ;; concatenations, and multiple concatenations.
            (let ((op   (vl-nonatom->op x))
                  (args (vl-nonatom->args x)))
              (case op
                ((:vl-bitselect :vl-partselect-colon
                                :vl-partselect-pluscolon :vl-partselect-minuscolon)
                 ;; foo[index] or foo[a:b]
                 (if (and (vl-idexpr-p (first args))
                          (equal name (vl-idexpr->name (first args))))
                     (cons x acc)
                   acc))
                ((:vl-concat)
                 ;; { foo, bar, baz, ... }
                 (vl-exprlist-lvalues-mentioning-aux-exec name args acc))
                (otherwise
                 ;; The only other valid thing is a hierarchical identifier.
                 ;; We're not going to try to gather those.
                 acc))))))

 (defund vl-exprlist-lvalues-mentioning-aux-exec (name x acc)
  (declare (xargs :guard (and (stringp name)
                              (vl-exprlist-p x)
                              (vl-exprlist-lvaluesp x))
                  :measure (two-nats-measure (acl2-count x) 0)))
  (if (consp x)
      (vl-exprlist-lvalues-mentioning-aux-exec
       name (cdr x)
       (vl-expr-lvalues-mentioning-aux-exec name (car x) acc))
    acc)))

(mutual-recursion

   (defund vl-expr-lvalues-mentioning-aux (name x)
     (declare (xargs :guard (and (stringp name)
                                 (vl-expr-p x)
                                 (vl-expr-lvaluep x))
                     :measure (two-nats-measure (acl2-count x) 1)
                     :verify-guards nil))
     (mbe :logic
          (cond ((vl-atom-p x)
                 (let ((guts (vl-atom->guts x)))
                   (if (and (vl-id-p guts)
                            (equal (vl-id->name guts) name))
                       (list x)
                     nil)))

                ((not (consp x))
                 nil)

                (t
                 (let ((op   (vl-nonatom->op x))
                       (args (vl-nonatom->args x)))
                   (case op
                     ((:vl-bitselect :vl-partselect-colon :vl-partselect-pluscolon
                                     :vl-partselect-minuscolon)
                      (if (and (vl-idexpr-p (first args))
                               (equal name (vl-idexpr->name (first args))))
                          (list x)
                        nil))
                     ((:vl-concat)
                      (vl-exprlist-lvalues-mentioning-aux name args))
                     (otherwise
                      nil)))))
          :exec
          (reverse (vl-expr-lvalues-mentioning-aux-exec name x nil))))

   (defund vl-exprlist-lvalues-mentioning-aux (name x)
     (declare (xargs :guard (and (stringp name)
                                 (vl-exprlist-p x)
                                 (vl-exprlist-lvaluesp x))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (mbe :logic
          (if (consp x)
              (append (vl-expr-lvalues-mentioning-aux name (car x))
                      (vl-exprlist-lvalues-mentioning-aux name (cdr x)))
            nil)
          :exec
          (reverse (vl-exprlist-lvalues-mentioning-aux-exec name x nil)))))

(defthm true-listp-of-vl-expr-lvalues-mentioning-aux
    (true-listp (vl-expr-lvalues-mentioning-aux name x))
    :rule-classes :type-prescription)

(defthm true-listp-of-vl-exprlist-lvalues-mentioning-aux
    (true-listp (vl-exprlist-lvalues-mentioning-aux name x))
    :rule-classes :type-prescription)

(FLAG::make-flag vl-fast-flag-expr-lvalues-mentioning-aux
                   vl-expr-lvalues-mentioning-aux-exec
                   :flag-mapping ((vl-expr-lvalues-mentioning-aux-exec . expr)
                                  (vl-exprlist-lvalues-mentioning-aux-exec . list)))

(defthm-vl-fast-flag-expr-lvalues-mentioning-aux lemma
    (expr (equal (vl-expr-lvalues-mentioning-aux-exec name x acc)
                 (revappend (vl-expr-lvalues-mentioning-aux name x) acc))
          :name vl-expr-lvalues-mentioning-aux-exec-removal)
    (list (equal (vl-exprlist-lvalues-mentioning-aux-exec name x acc)
                 (revappend (vl-exprlist-lvalues-mentioning-aux name x) acc))
          :name vl-exprlist-lvalues-mentioning-aux-exec-removal)
    :hints(("Goal"
            :induct (vl-fast-flag-expr-lvalues-mentioning-aux flag name x acc)
            :expand ((:free (name) (vl-expr-lvalues-mentioning-aux-exec name x acc))
                     (vl-exprlist-lvalues-mentioning-aux-exec name x acc)
                     (:free (name) (vl-expr-lvalues-mentioning-aux name x))
                     (vl-exprlist-lvalues-mentioning-aux name x))
            :do-not '(generalize fertilize))))

(verify-guards vl-expr-lvalues-mentioning-aux
                 :hints(("Goal" :in-theory (enable vl-expr-lvalues-mentioning-aux
                                                   vl-expr-lvalues-mentioning-aux-exec
                                                   vl-exprlist-lvalues-mentioning-aux
                                                   vl-exprlist-lvalues-mentioning-aux-exec))))

(FLAG::make-flag vl-flag-expr-lvalues-mentioning-aux
                   vl-expr-lvalues-mentioning-aux
                   :flag-mapping ((vl-expr-lvalues-mentioning-aux . expr)
                                  (vl-exprlist-lvalues-mentioning-aux . list)))

(defthm-vl-flag-expr-lvalues-mentioning-aux lemma
    (expr (implies (force (vl-expr-p x))
                   (vl-exprlist-p (vl-expr-lvalues-mentioning-aux name x)))
          :name vl-exprlist-p-of-vl-expr-lvalues-mentioning-aux)
    (list (implies (force (vl-exprlist-p x))
                   (vl-exprlist-p (vl-exprlist-lvalues-mentioning-aux name x)))
          :name vl-exprlist-p-of-vl-exprlist-lvalues-mentioning-aux)
    :hints(("Goal"
            :induct (vl-flag-expr-lvalues-mentioning-aux flag name x)
            :expand ((:free (name) (vl-expr-lvalues-mentioning-aux name x))
                     (:free (name) (vl-exprlist-lvalues-mentioning-aux name x)))))))




(defsection vl-expr-lvalues-mentioning

  (defund vl-expr-lvalues-mentioning (name x)
    (declare (xargs :guard (and (stringp name)
                                (vl-expr-p x))))
    (if (vl-expr-lvaluep x)
        (vl-expr-lvalues-mentioning-aux name x)
      nil))

  (defund vl-expr-lvalues-mentioning-exec (name x acc)
    (declare (xargs :guard (and (stringp name)
                                (vl-expr-p x))))
    (if (vl-expr-lvaluep x)
        (vl-expr-lvalues-mentioning-aux-exec name x acc)
      acc))

  (local (in-theory (enable vl-expr-lvalues-mentioning
                            vl-expr-lvalues-mentioning-exec)))

  (defthm vl-expr-lvalues-mentioning-exec-removal
    (equal (vl-expr-lvalues-mentioning-exec name x acc)
           (revappend (vl-expr-lvalues-mentioning name x) acc)))

  (defthm true-listp-of-vl-expr-lvalues-mentioning
    (true-listp (vl-expr-lvalues-mentioning name x))
    :rule-classes :type-prescription)

  (defthm vl-exprlist-p-of-vl-expr-lvalues-mentioning
    (implies (force (vl-expr-p x))
             (vl-exprlist-p (vl-expr-lvalues-mentioning name x)))))



(defmacro def-vl-lvalues-mentioning (&key type
                                   exec-body
                                   body
                                   name-exec
                                   name)
  (let* ((mksym-package-symbol 'vl)
         (rec            (mksym type '-p))
         (collect-exec   (or name-exec (mksym type '-lvalues-mentioning-exec)))
         (collect        (or name (mksym type '-lvalues-mentioning)))
         (remove-thm     (mksym collect-exec '-removal))
         (expr-thm       (mksym 'vl-exprlist-p-of- collect))

         ;; (rec-s          (symbol-name rec))
         ;; (collect-s      (symbol-name collect))
         ;; (collect-exec-s (symbol-name collect-exec))
         ;; (remove-thm-s   (symbol-name remove-thm))
         ;; (str-thm-s      (symbol-name str-thm))

;;          (short          (cat "Gather @(see lvalues-mentioning) from a @(see " rec-s ")."))

;;          (long           (cat "<p><b>Signature</b> @(call " collect-s ") returns a
;; string list.</p>

;; <h3>Definition</h3>

;; <p>For efficiency we use a tail-recursive, accumulator-style functions to do
;; the collection.  Under the hood, we also use <tt>nreverse</tt>
;; optimization.</p>

;;   @(def " collect-s ")
;;   @(def " collect-exec-s ")

;; <h3>Theorems</h3>

;;   @(thm " remove-thm-s ")
;;   @(thm " str-thm-s ")"))
         )

    `(defsection ,collect
;       :parents (,rec lvalues)
;       :short ,short
;       :long ,long

       (defund ,collect-exec (name x acc)
         (declare (xargs :guard (and (stringp name)
                                     (,rec x))))
         ,exec-body)

       (defund ,collect (name x)
         (declare (xargs :guard (and (stringp name)
                                     (,rec x))
                         :verify-guards nil))
         (mbe :logic ,body
              :exec (reverse (,collect-exec name x nil))))

       (local (in-theory (enable ,collect-exec ,collect)))

       (defthm ,remove-thm
         (equal (,collect-exec name x acc)
                (append (rev (,collect name x))
                        acc)))

       (verify-guards ,collect)

       (defthm ,expr-thm
         (implies (force (,rec x))
                  (vl-exprlist-p (,collect name x))))

       (defttag vl-optimize)
       (never-memoize ,collect-exec)
       (progn!
        (set-raw-mode t)
        (defun ,collect (x)
          (nreverse (,collect-exec name x nil))))
       (defttag nil))))



(defmacro def-vl-lvalues-mentioning-list (&key list element)
  (let* ((mksym-package-symbol 'vl)
         (list-rec             (mksym list '-p))
         (list-collect         (mksym list '-lvalues-mentioning))
;         (list-collect-exec    (mksym list '-lvalues-mentioning-exec))
         (element-collect      (mksym element '-lvalues-mentioning))
         (element-collect-exec (mksym element '-lvalues-mentioning-exec))
         (expr-thm             (mksym 'vl-exprlist-p-of- list-collect))

;;          (list-rec-s          (symbol-name list-rec))
;;          (list-collect-s      (symbol-name list-collect))
;;          (list-collect-exec-s (symbol-name list-collect-exec))
;;          (str-thm-s           (symbol-name str-thm))

;;          (short (cat "Gather @(see lvalues-mentioning) from a @(see " list-rec-s ")."))

;;          (long (cat "<p><b>Signature</b> @(call " list-collect-s ")
;; returns a string list.</p>

;; <h3>Definition</h3>

;;   @(def " list-collect-s ")
;;   @(def " list-collect-exec-s ")

;; <h3>Theorems</h3>

;; <p>Note that we use @(see defmappapend), and do not attempt to display the
;; theorems it generates here.  Additionally, we prove:</p>

;;   @(thm " str-thm-s ")"))
         )

    `(defsection ,list-collect
       ;; :parents (,list-rec lvalues)
       ;; :short ,short
       ;; :long ,long

       (defmapappend ,list-collect (name x)
         (,element-collect name x)
         :guard (and (stringp name)
                     (,list-rec x))
         :transform-true-list-p t
         :transform-exec ,element-collect-exec)

       (local (in-theory (enable ,list-collect)))

       (defthm ,expr-thm
         (implies (force (,list-rec x))
                  (vl-exprlist-p (,list-collect name x)))))))


(def-vl-lvalues-mentioning
  :type vl-assign
  :exec-body (vl-expr-lvalues-mentioning-exec name (vl-assign->lvalue x) acc)
  :body (vl-expr-lvalues-mentioning name (vl-assign->lvalue x)))

(def-vl-lvalues-mentioning-list
  :list vl-assignlist
  :element vl-assign)

(encapsulate
 ()
 (local (in-theory (disable (force))))

 (def-vl-lvalues-mentioning
   :type vl-plainarg
   :exec-body
   (let ((expr (vl-plainarg->expr x))
         (dir  (vl-plainarg->dir x))
         (atts (vl-plainarg->atts x)))
     ;; BOZO consider warning about unresolved arguments
     (if (and expr
              (or (eq dir :vl-output)
                  (eq dir :vl-inout))
              ;; Special hack.  If we've identified that this output isn't set
              ;; by the submodule, we don't consider its wires to be lvalues.
              (not (assoc-equal "VL_UNSET_OUTPUT" atts)))
         (vl-expr-lvalues-mentioning-exec name expr acc)
       acc))
   :body
   (let ((expr (vl-plainarg->expr x))
         (dir  (vl-plainarg->dir x))
         (atts (vl-plainarg->atts x)))
     (if (and expr
              (or (eq dir :vl-output)
                  (eq dir :vl-inout))
              (not (assoc-equal "VL_UNSET_OUTPUT" atts)))
         (vl-expr-lvalues-mentioning name expr)
       nil))))

(def-vl-lvalues-mentioning-list
  :list vl-plainarglist
  :element vl-plainarg)

(def-vl-lvalues-mentioning
  :type vl-gateinst
  :exec-body (vl-plainarglist-lvalues-mentioning-exec name (vl-gateinst->args x) acc)
  :body (vl-plainarglist-lvalues-mentioning name (vl-gateinst->args x)))

(def-vl-lvalues-mentioning-list
  :list vl-gateinstlist
  :element vl-gateinst)

(def-vl-lvalues-mentioning
  :type vl-modinst
  :exec-body
  (let ((args (vl-modinst->portargs x)))
    (if (vl-arguments->namedp args)
        (prog2$ (cw "; ~s0: in vl-modinst-lvalues-mentioning-exec, skipping ~s1 ~%~
                     ; of module ~s2 due to unresolved arguments."
                    (vl-location-string (vl-modinst->loc x))
                    (vl-modinst->instname x)
                    (vl-modinst->modname x))
                acc)
      (vl-plainarglist-lvalues-mentioning-exec
       name (vl-arguments->args args) acc)))
  :body
  (let ((args (vl-modinst->portargs x)))
    (if (vl-arguments->namedp args)
        nil
      (vl-plainarglist-lvalues-mentioning
       name (vl-arguments->args args)))))

(def-vl-lvalues-mentioning-list
  :list vl-modinstlist
  :element vl-modinst)

(def-vl-lvalues-mentioning
  :type vl-assignstmt
  :exec-body (vl-expr-lvalues-mentioning-exec name (vl-assignstmt->lvalue x) acc)
  :body (vl-expr-lvalues-mentioning name (vl-assignstmt->lvalue x)))

(def-vl-lvalues-mentioning
  :type vl-deassignstmt
  :exec-body (vl-expr-lvalues-mentioning-exec name (vl-deassignstmt->lvalue x) acc)
  :body (vl-expr-lvalues-mentioning name (vl-deassignstmt->lvalue x)))

(def-vl-lvalues-mentioning
  :type vl-atomicstmt
  :exec-body
  (case (tag x)
    (:vl-assignstmt   (vl-assignstmt-lvalues-mentioning-exec name x acc))
    (:vl-deassignstmt (vl-deassignstmt-lvalues-mentioning-exec name x acc))
    (otherwise        acc))
  :body
  (case (tag x)
    (:vl-assignstmt   (vl-assignstmt-lvalues-mentioning name x))
    (:vl-deassignstmt (vl-deassignstmt-lvalues-mentioning name x))
    (otherwise        nil)))

(defsection vl-stmt-lvalues-mentioning

  (mutual-recursion

   (defund vl-stmt-lvalues-mentioning-exec (name x acc)
     (declare (xargs :guard (and (stringp name)
                                 (vl-stmt-p x))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (cond ((vl-fast-atomicstmt-p x)
            (vl-atomicstmt-lvalues-mentioning-exec x acc))

; It looks to me like none of the compound statements have lvalues except for
; for loops, which have the initial and next lhs.  So I explicitly check for
; this here, then recursively check the substatements.

           ((eq (vl-compoundstmt->type x) :vl-forstmt)
            (let* ((acc (vl-expr-lvalues-mentioning-exec (vl-forstmt->initlhs x) acc))
                   (acc (vl-expr-lvalues-mentioning-exec (vl-forstmt->nextlhs x) acc)))
              (vl-stmtlist-lvalues-mentioning-exec (vl-compoundstmt->stmts x) acc)))

           (t
            (vl-stmtlist-lvalues-mentioning-exec (vl-compoundstmt->stmts x) acc))))

   (defund vl-stmtlist-lvalues-mentioning-exec (x acc)
     (declare (xargs :guard (vl-stmtlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         acc
       (let ((acc (vl-stmt-lvalues-mentioning-exec (car x) acc)))
         (vl-stmtlist-lvalues-mentioning-exec (cdr x) acc)))))

  (mutual-recursion
   (defund vl-stmt-lvalues-mentioning (x)
     (declare (xargs :guard (vl-stmt-p x)
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (mbe :logic
          (cond ((vl-atomicstmt-p x)
                 (vl-atomicstmt-lvalues-mentioning x))

                ((eq (vl-compoundstmt->type x) :vl-forstmt)
                 (append (vl-expr-lvalues-mentioning (vl-forstmt->initlhs x))
                         (vl-expr-lvalues-mentioning (vl-forstmt->nextlhs x))
                         (vl-stmtlist-lvalues-mentioning (vl-compoundstmt->stmts x))))

                (t
                 (vl-stmtlist-lvalues-mentioning (vl-compoundstmt->stmts x))))
          :exec
          (reverse (vl-stmt-lvalues-mentioning-exec x nil))))

   (defund vl-stmtlist-lvalues-mentioning (x)
     (declare (xargs :guard (vl-stmtlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (mbe :logic
          (if (atom x)
              nil
            (append (vl-stmt-lvalues-mentioning (car x))
                    (vl-stmtlist-lvalues-mentioning (cdr x))))
          :exec
          (reverse (vl-stmtlist-lvalues-mentioning-exec x nil)))))

  (flag::make-flag vl-flag-stmt-lvalues-mentioning-exec
                   vl-stmt-lvalues-mentioning-exec
                   :flag-mapping ((vl-stmt-lvalues-mentioning-exec . stmt)
                                  (vl-stmtlist-lvalues-mentioning-exec . list)))

  (defthm-vl-flag-stmt-lvalues-mentioning-exec lemma
    (stmt (equal (vl-stmt-lvalues-mentioning-exec x acc)
                 (revappend (vl-stmt-lvalues-mentioning x) acc))
          :name vl-stmt-lvalues-mentioning-exec-removal)
    (list (equal (vl-stmtlist-lvalues-mentioning-exec x acc)
                 (revappend (vl-stmtlist-lvalues-mentioning x) acc))
          :name vl-stmtlist-lvalues-mentioning-exec-removal)
    :hints(("Goal"
            :induct (vl-flag-stmt-lvalues-mentioning-exec flag x acc)
            :expand ((vl-stmt-lvalues-mentioning x)
                     (vl-stmtlist-lvalues-mentioning x)
                     (vl-stmt-lvalues-mentioning-exec x acc)
                     (vl-stmtlist-lvalues-mentioning-exec x acc)))))

  (defthm-vl-flag-stmt-p lemma
    (stmt (implies (force (vl-stmt-p x))
                   (string-listp (vl-stmt-lvalues-mentioning x)))
          :name string-listp-of-vl-stmt-lvalues-mentioning)
    (list (implies (force (vl-stmtlist-p x))
                   (string-listp (vl-stmtlist-lvalues-mentioning x)))
          :name string-listp-of-vl-stmtlist-lvalues-mentioning)
    :hints(("Goal"
            :induct (vl-flag-stmt-p flag x)
            :expand ((vl-stmt-lvalues-mentioning x)
                     (vl-stmtlist-lvalues-mentioning x)))))

  (verify-guards vl-stmt-lvalues-mentioning-exec)
  (verify-guards vl-stmt-lvalues-mentioning
                 :hints(("Goal" :in-theory (enable vl-stmt-lvalues-mentioning
                                                   vl-stmtlist-lvalues-mentioning)))))

(def-vl-lvalues-mentioning
  :type vl-always
  :exec-body (vl-stmt-lvalues-mentioning-exec (vl-always->stmt x) acc)
  :body (vl-stmt-lvalues-mentioning (vl-always->stmt x)))

(def-vl-lvalues-mentioning-list
  :list vl-alwayslist
  :element vl-always)

(def-vl-lvalues-mentioning
  :type vl-initial
  :exec-body (vl-stmt-lvalues-mentioning-exec (vl-initial->stmt x) acc)
  :body (vl-stmt-lvalues-mentioning (vl-initial->stmt x)))

(def-vl-lvalues-mentioning-list
  :list vl-initiallist
  :element vl-initial)

(def-vl-lvalues-mentioning
  :type vl-module
  :exec-body
  (b* ((assigns   (vl-module->assigns x))
       (initials  (vl-module->initials x))
       (alwayses  (vl-module->alwayses x))
       (gateinsts (vl-module->gateinsts x))
       (modinsts  (vl-module->modinsts x))
       (acc (vl-gateinstlist-lvalues-mentioning-exec gateinsts acc))
       (acc (vl-modinstlist-lvalues-mentioning-exec modinsts acc))
       (acc (vl-assignlist-lvalues-mentioning-exec assigns acc))
       (acc (vl-alwayslist-lvalues-mentioning-exec alwayses acc))
       (acc (vl-initiallist-lvalues-mentioning-exec initials acc)))
      acc)
  :body
  (b* ((assigns   (vl-module->assigns x))
       (initials  (vl-module->initials x))
       (alwayses  (vl-module->alwayses x))
       (gateinsts (vl-module->gateinsts x))
       (modinsts  (vl-module->modinsts x)))
      (append (vl-gateinstlist-lvalues-mentioning gateinsts)
              (vl-modinstlist-lvalues-mentioning modinsts)
              (vl-assignlist-lvalues-mentioning assigns)
              (vl-alwayslist-lvalues-mentioning alwayses)
              (vl-initiallist-lvalues-mentioning initials))))

|#