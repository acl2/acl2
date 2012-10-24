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
(include-book "../mlib/expr-tools")
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))


(defxdoc array-indexing
  :parents (transforms)
  :short "Introduce <tt>:vl-array-index</tt> operators."

  :long "<p>When our parser encounters a subexpression like <tt>foo[i]</tt>, it
does not know whether <tt>foo</tt> is an ordinary vector like <tt>wire [3:0]
foo</tt> or an array like <tt>reg [63:0] foo [128:0];</tt>.  So, the parser
just puts in <tt>:vl-bitselect</tt> operators everywhere that this syntax
occurs.  In this transform, we convert these so-called bit-selects that
actually refer to arrays into <tt>:vl-array-index</tt> operations.</p>")



(defsection vl-regdecllist-collect-array-names
  :parents (array-indexing)
  :short "Gather the names of all registers which are arrays."

  (defund vl-regdecllist-collect-array-names (x)
    (declare (xargs :guard (vl-regdecllist-p x)))
    (cond ((atom x)
           nil)
          ((consp (vl-regdecl->arrdims (car x)))
           (cons (vl-regdecl->name (car x))
                 (vl-regdecllist-collect-array-names (cdr x))))
          (t
           (vl-regdecllist-collect-array-names (cdr x)))))

  (local (in-theory (enable vl-regdecllist-collect-array-names)))

  (defthm string-listp-of-vl-regdecllist-collect-array-names
    (implies (force (vl-regdecllist-p x))
             (string-listp (vl-regdecllist-collect-array-names x)))))



(defsection vl-netdecllist-collect-array-names
  :parents (array-indexing)
  :short "Gather the names of all nets which are arrays."

  (defund vl-netdecllist-collect-array-names (x)
    (declare (xargs :guard (vl-netdecllist-p x)))
    (cond ((atom x)
           nil)
          ((consp (vl-netdecl->arrdims (car x)))
           (cons (vl-netdecl->name (car x))
                 (vl-netdecllist-collect-array-names (cdr x))))
          (t
           (vl-netdecllist-collect-array-names (cdr x)))))

  (local (in-theory (enable vl-netdecllist-collect-array-names)))

  (defthm string-listp-of-vl-netdecllist-collect-array-names
    (implies (force (vl-netdecllist-p x))
             (string-listp (vl-netdecllist-collect-array-names x)))))



; We actually never introduce warnings, but we go ahead and put the warnings
; accumulator in now so that if we ever want to add warnings it's easy to do
; so.

(defsection vl-expr-make-array-indexing
  :parents (array-indexing)
  :short "Introduce <tt>:vl-array-index</tt> operators throughout a @(see vl-expr-p)."

  (mutual-recursion

   (defund vl-expr-make-array-indexing (x arrnames fal warnings)
     "Returns (MV WARNINGS-PRIME X-PRIME)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (string-listp arrnames)
                                 (equal fal (make-lookup-alist arrnames))
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atom-p x))
           (mv warnings x))

          (op   (vl-nonatom->op x))
          (args (vl-nonatom->args x))
          ((mv warnings args)
           (vl-exprlist-make-array-indexing args arrnames fal warnings))
          (x-prime (if (and (eq op :vl-bitselect)
                            (vl-idexpr-p (first args))
                            (fast-memberp (vl-idexpr->name (first args)) arrnames fal))
                       (change-vl-nonatom x
                                          :op :vl-array-index
                                          :args args)
                     (change-vl-nonatom x :args args))))
       (mv warnings x-prime)))

   (defund vl-exprlist-make-array-indexing (x arrnames fal warnings)
     "Returns (MV WARNINGS-PRIME X-PRIME)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (string-listp arrnames)
                                 (equal fal (make-lookup-alist arrnames))
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv warnings nil))
          ((mv warnings car-prime)
           (vl-expr-make-array-indexing (car x) arrnames fal warnings))
          ((mv warnings cdr-prime)
           (vl-exprlist-make-array-indexing (cdr x) arrnames fal warnings)))
       (mv warnings (cons car-prime cdr-prime)))))

  (defthm vl-exprlist-make-array-indexing-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-make-array-indexing x arrnames fal warnings)
                    (mv warnings nil)))
    :hints(("Goal" :in-theory (enable vl-exprlist-make-array-indexing))))

  (defthm vl-exprlist-make-array-indexing-when-of-cons
    (equal (vl-exprlist-make-array-indexing (cons a x) arrnames fal warnings)
           (b* (((mv warnings car-prime) (vl-expr-make-array-indexing a arrnames fal warnings))
                ((mv warnings cdr-prime) (vl-exprlist-make-array-indexing x arrnames fal warnings)))
             (mv warnings (cons car-prime cdr-prime))))
    :hints(("Goal" :in-theory (enable vl-exprlist-make-array-indexing))))

  (local (defun my-induction (x arrnames fal warnings)
           (if (atom x)
               (mv warnings nil)
             (b* (((mv warnings &) (vl-expr-make-array-indexing (car x) arrnames fal warnings)))
               (my-induction (cdr x) arrnames fal warnings)))))

  (defthm len-of-vl-exprlist-make-array-indexing
    (equal (len (mv-nth 1 (vl-exprlist-make-array-indexing x arrnames fal warnings)))
           (len x))
    :hints(("Goal"
            :induct (my-induction x arrnames fal warnings)
            :expand (vl-exprlist-make-array-indexing x arrnames fal warnings))))

  (defthm true-listp-of-vl-exprlist-make-array-indexing
    (true-listp (mv-nth 1 (vl-exprlist-make-array-indexing x arrnames fal warnings)))
    :rule-classes :type-prescription
    :hints(("Goal"
            :induct (my-induction x arrnames fal warnings)
            :expand (vl-exprlist-make-array-indexing x arrnames fal warnings))))

  (defthm vl-exprlist-make-array-indexing-under-iff
    (iff (mv-nth 1 (vl-exprlist-make-array-indexing x arrnames fal warnings))
         (consp x))
    :hints(("Goal"
            :induct (my-induction x arrnames fal warnings)
            :expand (vl-exprlist-make-array-indexing x arrnames fal warnings))))

  (FLAG::make-flag vl-flag-expr-make-array-indexing
                   vl-expr-make-array-indexing
                   :flag-mapping ((vl-expr-make-array-indexing . expr)
                                  (vl-exprlist-make-array-indexing . list)))

  (defthm-vl-flag-expr-make-array-indexing
    (defthm vl-warninglist-p-of-vl-expr-make-array-indexing
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 (vl-expr-make-array-indexing x arrnames fal warnings))))
      :flag expr)
    (defthm vl-warninglist-p-of-vl-exprlist-make-array-indexing
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 (vl-exprlist-make-array-indexing x arrnames fal warnings))))
      :flag list)
    :hints(("Goal"
            :expand ((vl-expr-make-array-indexing x arrnames fal warnings)
                     (vl-exprlist-make-array-indexing x arrnames fal warnings)))))

  (defthm-vl-flag-expr-make-array-indexing
    (defthm vl-expr-p-of-vl-expr-make-array-indexing
      (implies (force (vl-expr-p x))
               (vl-expr-p (mv-nth 1 (vl-expr-make-array-indexing x arrnames fal warnings))))
      :flag expr)
    (defthm vl-exprlist-p-of-vl-exprlist-make-array-indexing
      (implies (force (vl-exprlist-p x))
               (vl-exprlist-p (mv-nth 1 (vl-exprlist-make-array-indexing x arrnames fal warnings))))
      :flag list)
    :hints(("Goal"
            :expand ((vl-expr-make-array-indexing x arrnames fal warnings)
                     (vl-exprlist-make-array-indexing x arrnames fal warnings)))))

  (verify-guards vl-expr-make-array-indexing))




(defmacro def-vl-make-array-indexing (name &key type body)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (short      (cat "Introduce <tt>:vl-array-index</tt> operators throughout
a @(see " type-s ")"))

         (long       (cat "<p><b>Signature:</b> @(call " name-s ") returns
<tt>(mv warnings-prime x-prime)</tt></p>")))

  `(defsection ,name
     :parents (array-indexing)
     :short ,short
     :long ,long

     (defund ,name (x arrnames fal warnings)
       (declare (xargs :guard (and (,type x)
                                   (string-listp arrnames)
                                   (equal fal (make-lookup-alist arrnames))
                                   (vl-warninglist-p warnings))))
      ,body)

     (local (in-theory (enable ,name)))

     (defthm ,thm-warn
       (implies (force (vl-warninglist-p warnings))
                (vl-warninglist-p (mv-nth 0 (,name x arrnames fal warnings)))))

     (defthm ,thm-type
       (implies (force (,type x))
                (,type (mv-nth 1 (,name x arrnames fal warnings))))))))


(defmacro def-vl-make-array-indexing-list (name &key type element)
  (let* ((name-s     (symbol-name name))
         (type-s     (symbol-name type))
         (thm-warn-s (cat "VL-WARNINGLIST-P-" name-s))
         (thm-type-s (cat type-s "-OF-" name-s))
         (thm-true-s (cat "TRUE-LISTP-OF-" name-s))
         (thm-warn   (intern-in-package-of-symbol thm-warn-s name))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (thm-true   (intern-in-package-of-symbol thm-true-s name))
         (short      (cat "Introduce <tt>:vl-array-index</tt> operators throughout
a @(see " type-s ")"))
         (long       (cat "<p><b>Signature:</b> @(call " name-s ") returns
<tt>(mv warnings-prime x-prime)</tt></p>")))

  `(defsection ,name
     :parents (array-indexing)
     :short ,short
     :long ,long

    (defund ,name (x arrnames fal warnings)
      (declare (xargs :guard (and (,type x)
                                  (string-listp arrnames)
                                  (equal fal (make-lookup-alist arrnames))
                                  (vl-warninglist-p warnings))))
      (b* (((when (atom x))
            (mv warnings nil))
           ((mv warnings car-prime) (,element (car x) arrnames fal warnings))
           ((mv warnings cdr-prime) (,name (cdr x) arrnames fal warnings)))
        (mv warnings (cons car-prime cdr-prime))))

    (local (in-theory (enable ,name)))

    (defthm ,thm-warn
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 0 (,name x arrnames fal warnings)))))

    (defthm ,thm-type
      (implies (force (,type x))
               (,type (mv-nth 1 (,name x arrnames fal warnings)))))

    (defthm ,thm-true
      (true-listp (mv-nth 1 (,name x arrnames fal warnings)))
      :rule-classes :type-prescription))))



(def-vl-make-array-indexing vl-maybe-expr-make-array-indexing
  :type vl-maybe-expr-p
  :body (if (not x)
            (mv warnings nil)
          (vl-expr-make-array-indexing x arrnames fal warnings)))

(def-vl-make-array-indexing vl-assign-make-array-indexing
  :type vl-assign-p
  :body (b* (((vl-assign x) x)
             ((mv warnings lvalue-prime)
              (vl-expr-make-array-indexing x.lvalue arrnames fal warnings))
             ((mv warnings expr-prime)
              (vl-expr-make-array-indexing x.expr arrnames fal warnings)))
            (mv warnings
                (change-vl-assign x
                                  :lvalue lvalue-prime
                                  :expr expr-prime))))

(def-vl-make-array-indexing-list vl-assignlist-make-array-indexing
  :type vl-assignlist-p
  :element vl-assign-make-array-indexing)


(def-vl-make-array-indexing vl-plainarg-make-array-indexing
  :type vl-plainarg-p
  :body (b* (((vl-plainarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-make-array-indexing x.expr arrnames fal warnings)))
            (mv warnings (change-vl-plainarg x :expr expr-prime))))

(def-vl-make-array-indexing-list vl-plainarglist-make-array-indexing
  :type vl-plainarglist-p
  :element vl-plainarg-make-array-indexing)


(def-vl-make-array-indexing vl-namedarg-make-array-indexing
  :type vl-namedarg-p
  :body (b* (((vl-namedarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-make-array-indexing x.expr arrnames fal warnings)))
            (mv warnings (change-vl-namedarg x :expr expr-prime))))

(def-vl-make-array-indexing-list vl-namedarglist-make-array-indexing
  :type vl-namedarglist-p
  :element vl-namedarg-make-array-indexing)

(def-vl-make-array-indexing vl-arguments-make-array-indexing
  :type vl-arguments-p
  :body (b* (((vl-arguments x) x)
             ((mv warnings args-prime)
              (if x.namedp
                  (vl-namedarglist-make-array-indexing x.args arrnames fal warnings)
                (vl-plainarglist-make-array-indexing x.args arrnames fal warnings))))
            (mv warnings (vl-arguments x.namedp args-prime))))

(def-vl-make-array-indexing vl-modinst-make-array-indexing
  :type vl-modinst-p
  :body (b* (((vl-modinst x) x)
             ((mv warnings args-prime)
              (vl-arguments-make-array-indexing x.portargs arrnames fal warnings)))
            (mv warnings (change-vl-modinst x :portargs args-prime))))

(def-vl-make-array-indexing-list vl-modinstlist-make-array-indexing
  :type vl-modinstlist-p
  :element vl-modinst-make-array-indexing)

(def-vl-make-array-indexing vl-gateinst-make-array-indexing
  :type vl-gateinst-p
  :body (b* (((vl-gateinst x) x)
             ((mv warnings args-prime)
              (vl-plainarglist-make-array-indexing x.args arrnames fal warnings)))
            (mv warnings (change-vl-gateinst x :args args-prime))))

(def-vl-make-array-indexing-list vl-gateinstlist-make-array-indexing
  :type vl-gateinstlist-p
  :element vl-gateinst-make-array-indexing)

(def-vl-make-array-indexing vl-delaycontrol-make-array-indexing
  :type vl-delaycontrol-p
  :body (b* (((vl-delaycontrol x) x)
             ((mv warnings value-prime)
              (vl-expr-make-array-indexing x.value arrnames fal warnings)))
            (mv warnings (change-vl-delaycontrol x :value value-prime))))

(def-vl-make-array-indexing vl-evatom-make-array-indexing
  :type vl-evatom-p
  :body (b* (((vl-evatom x) x)
             ((mv warnings expr-prime)
              (vl-expr-make-array-indexing x.expr arrnames fal warnings)))
            (mv warnings (change-vl-evatom x :expr expr-prime))))

(def-vl-make-array-indexing-list vl-evatomlist-make-array-indexing
  :type vl-evatomlist-p
  :element vl-evatom-make-array-indexing)

(def-vl-make-array-indexing vl-eventcontrol-make-array-indexing
  :type vl-eventcontrol-p
  :body (b* (((vl-eventcontrol x) x)
             ((mv warnings atoms-prime)
              (vl-evatomlist-make-array-indexing x.atoms arrnames fal warnings)))
            (mv warnings (change-vl-eventcontrol x :atoms atoms-prime))))

(def-vl-make-array-indexing vl-repeateventcontrol-make-array-indexing
  :type vl-repeateventcontrol-p
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv warnings expr-prime)
              (vl-expr-make-array-indexing x.expr arrnames fal warnings))
             ((mv warnings ctrl-prime)
              (vl-eventcontrol-make-array-indexing x.ctrl arrnames fal warnings))
             (x-prime (change-vl-repeateventcontrol x
                                                    :expr expr-prime
                                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(encapsulate
 ()
 (local (in-theory (disable vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p)))
 (def-vl-make-array-indexing vl-delayoreventcontrol-make-array-indexing
   :type vl-delayoreventcontrol-p
   :body (case (tag x)
           (:vl-delaycontrol
            (vl-delaycontrol-make-array-indexing x arrnames fal warnings))
           (:vl-eventcontrol
            (vl-eventcontrol-make-array-indexing x arrnames fal warnings))
           (:vl-repeat-eventcontrol
            (vl-repeateventcontrol-make-array-indexing x arrnames fal warnings))
           (otherwise
            (mv (er hard 'vl-delayoreventcontrol-make-array-indexing "Provably impossible.")
                x)))))

(def-vl-make-array-indexing vl-maybe-delayoreventcontrol-make-array-indexing
  :type vl-maybe-delayoreventcontrol-p
  :body (if x
            (vl-delayoreventcontrol-make-array-indexing x arrnames fal warnings)
          (mv warnings nil)))

(defthm vl-maybe-delayoreventcontrol-make-array-indexing-under-iff
  (implies (force (vl-maybe-delayoreventcontrol-p x))
           (iff (mv-nth 1 (vl-maybe-delayoreventcontrol-make-array-indexing x arrnames fal warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-make-array-indexing
                           vl-maybe-delayoreventcontrol-p)
                          (vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-make-array-indexing))
          :use ((:instance vl-delayoreventcontrol-p-of-vl-delayoreventcontrol-make-array-indexing)))))



(def-vl-make-array-indexing vl-assignstmt-make-array-indexing
  :type vl-assignstmt-p
  :body (b* (((vl-assignstmt x) x)
             ((mv warnings lvalue-prime)
              (vl-expr-make-array-indexing x.lvalue arrnames fal warnings))
             ((mv warnings expr-prime)
              (vl-expr-make-array-indexing x.expr arrnames fal warnings))
             ((mv warnings ctrl-prime)
              (vl-maybe-delayoreventcontrol-make-array-indexing x.ctrl arrnames fal warnings))
             (x-prime
              (change-vl-assignstmt x
                                    :lvalue lvalue-prime
                                    :expr expr-prime
                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(def-vl-make-array-indexing vl-deassignstmt-make-array-indexing
  :type vl-deassignstmt-p
  :body (b* (((vl-deassignstmt x) x)
             ((mv warnings lvalue-prime)
              (vl-expr-make-array-indexing x.lvalue arrnames fal warnings))
             (x-prime
              (change-vl-deassignstmt x :lvalue lvalue-prime)))
            (mv warnings x-prime)))

(def-vl-make-array-indexing vl-enablestmt-make-array-indexing
  :type vl-enablestmt-p
  :body (b* (((vl-enablestmt x) x)
             ((mv warnings id-prime)
              (vl-expr-make-array-indexing x.id arrnames fal warnings))
             ((mv warnings args-prime)
              (vl-exprlist-make-array-indexing x.args arrnames fal warnings))
             (x-prime
              (change-vl-enablestmt x
                                    :id id-prime
                                    :args args-prime)))
            (mv warnings x-prime)))

(def-vl-make-array-indexing vl-disablestmt-make-array-indexing
  :type vl-disablestmt-p
  :body (b* (((vl-disablestmt x) x)
             ((mv warnings id-prime)
              (vl-expr-make-array-indexing x.id arrnames fal warnings))
             (x-prime
              (change-vl-disablestmt x :id id-prime)))
            (mv warnings x-prime)))

(def-vl-make-array-indexing vl-eventtriggerstmt-make-array-indexing
  :type vl-eventtriggerstmt-p
  :body (b* (((vl-eventtriggerstmt x) x)
             ((mv warnings id-prime)
              (vl-expr-make-array-indexing x.id arrnames fal warnings))
             (x-prime
              (change-vl-eventtriggerstmt x :id id-prime)))
            (mv warnings x-prime)))

(def-vl-make-array-indexing vl-atomicstmt-make-array-indexing
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (mv warnings x))
          (:vl-assignstmt       (vl-assignstmt-make-array-indexing x arrnames fal warnings))
          (:vl-deassignstmt     (vl-deassignstmt-make-array-indexing x arrnames fal warnings))
          (:vl-enablestmt       (vl-enablestmt-make-array-indexing x arrnames fal warnings))
          (:vl-disablestmt      (vl-disablestmt-make-array-indexing x arrnames fal warnings))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-make-array-indexing x arrnames fal warnings))
          (otherwise
           (mv (er hard 'vl-atomicstmt-make-array-indexing
                   "Impossible case.   This is not really an error.  We are just ~
                    using the guard mechanism to prove that all cases have been ~
                    covered.")
               x))))

(defsection vl-stmt-make-array-indexing

  (mutual-recursion

   (defund vl-stmt-make-array-indexing (x arrnames fal warnings)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (string-listp arrnames)
                                 (equal fal (make-lookup-alist arrnames))
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (if (vl-fast-atomicstmt-p x)
         (vl-atomicstmt-make-array-indexing x arrnames fal warnings)
       (b* (((vl-compoundstmt x) x)
            ((mv warnings exprs-prime)
             (vl-exprlist-make-array-indexing x.exprs arrnames fal warnings))
            ((mv warnings stmts-prime)
             (vl-stmtlist-make-array-indexing x.stmts arrnames fal warnings))
            ((mv warnings ctrl-prime)
             (vl-maybe-delayoreventcontrol-make-array-indexing x.ctrl arrnames fal warnings))
            (x-prime
             (change-vl-compoundstmt x
                                     :exprs exprs-prime
                                     :stmts stmts-prime
                                     :ctrl ctrl-prime)))
         (mv warnings x-prime))))

   (defund vl-stmtlist-make-array-indexing (x arrnames fal warnings)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (string-listp arrnames)
                                 (equal fal (make-lookup-alist arrnames))
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv warnings nil))
          ((mv warnings car-prime)
           (vl-stmt-make-array-indexing (car x) arrnames fal warnings))
          ((mv warnings cdr-prime)
           (vl-stmtlist-make-array-indexing (cdr x) arrnames fal warnings)))
       (mv warnings (cons car-prime cdr-prime)))))

  (FLAG::make-flag vl-flag-stmt-make-array-indexing
                   vl-stmt-make-array-indexing
                   :flag-mapping ((vl-stmt-make-array-indexing . stmt)
                                  (vl-stmtlist-make-array-indexing . list)))

  (defthm-vl-flag-stmt-make-array-indexing
    (defthm vl-warninglist-p-of-vl-stmt-make-array-indexing
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 0 (vl-stmt-make-array-indexing x arrnames fal warnings))))
      :flag stmt)
    (defthm vl-warninglist-p-of-vl-stmtlist-make-array-indexing
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p
                (mv-nth 0 (vl-stmtlist-make-array-indexing x arrnames fal warnings))))
      :flag list)
    :hints(("Goal"
            :expand ((vl-stmt-make-array-indexing x arrnames fal warnings)
                     (vl-stmtlist-make-array-indexing x arrnames fal warnings)))))

  (defthm vl-stmtlist-make-array-indexing-when-not-consp
    (implies (not (consp x))
             (equal (vl-stmtlist-make-array-indexing x arrnames fal warnings)
                    (mv warnings nil)))
    :hints(("Goal" :in-theory (enable vl-stmtlist-make-array-indexing))))

  (defthm vl-stmtlist-make-array-indexing-of-cons
    (equal (vl-stmtlist-make-array-indexing (cons a x) arrnames fal warnings)
           (b* (((mv warnings car-prime)
                 (vl-stmt-make-array-indexing a arrnames fal warnings))
                ((mv warnings cdr-prime)
                 (vl-stmtlist-make-array-indexing x arrnames fal warnings)))
             (mv warnings (cons car-prime cdr-prime))))
    :hints(("Goal" :in-theory (enable vl-stmtlist-make-array-indexing))))

  (local (defun my-induction (x arrnames fal warnings)
           (if (atom x)
               (mv warnings x)
             (b* (((mv warnings car-prime)
                   (vl-stmt-make-array-indexing (car x) arrnames fal warnings))
                  ((mv warnings cdr-prime)
                   (my-induction (cdr x) arrnames fal warnings)))
               (mv warnings (cons car-prime cdr-prime))))))

  (defthm len-of-vl-stmtlist-make-array-indexing
    (equal (len (mv-nth 1 (vl-stmtlist-make-array-indexing x arrnames fal warnings)))
           (len x))
    :hints(("Goal" :induct (my-induction x arrnames fal warnings))))

  (defthm-vl-flag-stmt-make-array-indexing
    (defthm vl-stmt-p-of-vl-stmt-make-array-indexing
      (implies (force (vl-stmt-p x))
               (vl-stmt-p (mv-nth 1 (vl-stmt-make-array-indexing x arrnames fal warnings))))
      :flag stmt)
    (defthm vl-stmtlist-p-of-vl-stmtlist-make-array-indexing
      (implies (force (vl-stmtlist-p x))
               (vl-stmtlist-p (mv-nth 1 (vl-stmtlist-make-array-indexing x arrnames fal warnings))))
      :flag list)
    :hints(("Goal"
            :expand ((vl-stmt-make-array-indexing x arrnames fal warnings)
                     (vl-stmtlist-make-array-indexing x arrnames fal warnings)))))

  (verify-guards vl-stmt-make-array-indexing))

(def-vl-make-array-indexing vl-always-make-array-indexing
  :type vl-always-p
  :body (b* (((vl-always x) x)
             ((mv warnings stmt-prime)
              (vl-stmt-make-array-indexing x.stmt arrnames fal warnings))
             (x-prime
              (change-vl-always x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-make-array-indexing-list vl-alwayslist-make-array-indexing
  :type vl-alwayslist-p
  :element vl-always-make-array-indexing)

(def-vl-make-array-indexing vl-initial-make-array-indexing
  :type vl-initial-p
  :body (b* (((vl-initial x) x)
             ((mv warnings stmt-prime)
              (vl-stmt-make-array-indexing x.stmt arrnames fal warnings))
             (x-prime
              (change-vl-initial x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-make-array-indexing-list vl-initiallist-make-array-indexing
  :type vl-initiallist-p
  :element vl-initial-make-array-indexing)

(def-vl-make-array-indexing vl-port-make-array-indexing
  :type vl-port-p
  :body (b* (((vl-port x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-make-array-indexing x.expr arrnames fal warnings))
             (x-prime
              (change-vl-port x :expr expr-prime)))
          (mv warnings x-prime)))

(def-vl-make-array-indexing-list vl-portlist-make-array-indexing
  :type vl-portlist-p
  :element vl-port-make-array-indexing)




(defund vl-module-make-array-indexing (x)
  (declare (xargs :guard (vl-module-p x)))
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       (names (append (vl-regdecllist-collect-array-names x.regdecls)
                      (vl-netdecllist-collect-array-names x.netdecls)))
       ((unless names)
        x)
       (fal      (make-lookup-alist names))
       (warnings x.warnings)
       ((mv warnings ports)     (vl-portlist-make-array-indexing     x.ports names fal warnings))
       ((mv warnings assigns)   (vl-assignlist-make-array-indexing   x.assigns names fal warnings))
       ((mv warnings modinsts)  (vl-modinstlist-make-array-indexing  x.modinsts names fal warnings))
       ((mv warnings gateinsts) (vl-gateinstlist-make-array-indexing x.gateinsts names fal warnings))
       ((mv warnings alwayses)  (vl-alwayslist-make-array-indexing   x.alwayses names fal warnings))
       ((mv warnings initials)  (vl-initiallist-make-array-indexing  x.initials names fal warnings))
       (- (fast-alist-free fal)))

      (change-vl-module x
                        :ports ports
                        :assigns assigns
                        :modinsts modinsts
                        :gateinsts gateinsts
                        :alwayses alwayses
                        :initials initials
                        :warnings warnings)))

(defthm vl-module-p-of-vl-module-make-array-indexing
  (implies (force (vl-module-p x))
           (vl-module-p (vl-module-make-array-indexing x)))
  :hints(("Goal" :in-theory (enable vl-module-make-array-indexing))))

(defthm vl-module->name-of-vl-module-make-array-indexing
  (equal (vl-module->name (vl-module-make-array-indexing x))
         (vl-module->name x))
  :hints(("Goal" :in-theory (enable vl-module-make-array-indexing))))



(defprojection vl-modulelist-make-array-indexing (x)
  (vl-module-make-array-indexing x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(defthm vl-modulelist->names-of-vl-modulelist-make-array-indexing
  (equal (vl-modulelist->names (vl-modulelist-make-array-indexing x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))
