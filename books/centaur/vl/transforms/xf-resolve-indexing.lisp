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
(include-book "../mlib/expr-tools")
(include-book "../mlib/stmt-tools")
(include-book "../mlib/modnamespace")
(local (include-book "../util/arithmetic"))

(defxdoc resolve-indexing
  :parents (transforms)
  :short "Resolve @(':vl-index') operators into @(':vl-bitselect') and
@(':vl-array-index') operators."

  :long "<p>When our @(see parser) encounters a subexpression like @('foo[i]'),
it does not know whether @('foo') is an ordinary vector like @('wire [3:0]
foo'), an array like @('reg [63:0] foo [128:0];'), or something more
complicated like a reference into an array of instances or similar.  To account
for this, the parser just produces @(':vl-index') operators whenever it sees a
selection like @('foo[i]').</p>

<p>In this transform, we convert these unresolved index operators into proper
@(':vl-bitselect') or @(':vl-array-index') operations when we can tell that
they are pointing at an ordinary wire or an array, respectively.  This
transform should typically be run very early in the transformation sequence, as
later transforms often expect to find proper @(':vl-bitselect') operators.</p>

<p>Note that this transform may not convert all occurrences of @(':vl-index')
operators.  For instance, we don't (currently) try to follow hierarchical
identifiers.  We might eventually want to make this transform smarter, to be
able to handle more cases.</p>")

(local (xdoc::set-default-parents resolve-indexing))

(define vl-regdecllist-filter-arrays
  :short "Filter register declarations into arrays and non-arrays."
  ((x          vl-regdecllist-p "Decls we're filtering.")
   (arrays     vl-regdecllist-p "Accumulator for the arrays.")
   (non-arrays vl-regdecllist-p "Accumulator for the non-arrays."))
  :returns
  (mv (arrays vl-regdecllist-p
              :hyp (and (force (vl-regdecllist-p x))
                        (force (vl-regdecllist-p arrays))))
      (non-arrays vl-regdecllist-p
                  :hyp (and (force (vl-regdecllist-p x))
                            (force (vl-regdecllist-p non-arrays)))))
  (cond ((atom x)
         (mv arrays non-arrays))
        ((consp (vl-regdecl->arrdims (car x)))
         (vl-regdecllist-filter-arrays (cdr x)
                                       (cons (car x) arrays)
                                       non-arrays))
        (t
         (vl-regdecllist-filter-arrays (cdr x)
                                       arrays
                                       (cons (car x) non-arrays)))))

(define vl-netdecllist-filter-arrays
  :short "Filter register declarations into arrays and non-arrays."
  ((x          vl-netdecllist-p "Decls we're filtering.")
   (arrays     vl-netdecllist-p "Accumulator for the arrays.")
   (non-arrays vl-netdecllist-p "Accumulator for the non-arrays."))
  :returns
  (mv (arrays vl-netdecllist-p
              :hyp (and (force (vl-netdecllist-p x))
                        (force (vl-netdecllist-p arrays))))
      (non-arrays vl-netdecllist-p
                  :hyp (and (force (vl-netdecllist-p x))
                            (force (vl-netdecllist-p non-arrays)))))
  (cond ((atom x)
         (mv arrays non-arrays))
        ((consp (vl-netdecl->arrdims (car x)))
         (vl-netdecllist-filter-arrays (cdr x)
                                       (cons (car x) arrays)
                                       non-arrays))
        (t
         (vl-netdecllist-filter-arrays (cdr x)
                                       arrays
                                       (cons (car x) non-arrays)))))

;; BOZO maybe we can also have arrays of variables, events, etc.?

(defines vl-expr-resolve-indexing-aux
  :short "Core routine for introducing @(':vl-array-index') and
@(':vl-bitselect') operators throughout a @(see vl-expr-p)."

  (define vl-expr-resolve-indexing-aux
    ((x        vl-expr-p)
     (arrfal   "Fast alist binding names of arrays to anything.")
     (wirefal  "Fast alist binding names of wires (non-arrays) to anything.")
     (warnings vl-warninglist-p
               "We don't currently add any warnings, but we put this warnings
                accumulator in, in case we ever want to."))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (changedp     booleanp :rule-classes :type-prescription
                      "Optimization, don't re-cons index-free expresions.")
        (new-x        vl-expr-p :hyp (force (vl-expr-p x))))
    :verify-guards nil
    :measure (vl-expr-count x)
    :flag :expr
    (b* (((when (vl-fast-atom-p x))
          (mv (ok) nil x))
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x))
         ((mv warnings args-changedp args)
          (vl-exprlist-resolve-indexing-aux args arrfal wirefal warnings))

         (name (and (eq op :vl-index)
                    (vl-idexpr-p (first args))
                    (vl-idexpr->name (first args))))

         ((unless name)
          ;; BOZO maybe some kind of hierarchical identifier or similar?  We
          ;; could do something smarter here to try to track it down and figure
          ;; it out.  Or, maybe we should leave those things as
          ;; unresolved-indexes.
          (mv (ok)
              args-changedp
              (if (not args-changedp)
                  x
                (change-vl-nonatom x :args args))))

         ((when (hons-get name wirefal))
          (mv (ok) t (change-vl-nonatom x :op :vl-bitselect)))
         ((when (hons-get name arrfal))
          (mv (ok) t (change-vl-nonatom x :op :vl-array-index))))

      ;; Else somehow not a name we know about?  It seems reasonably safe to
      ;; leave it unresolved.  We could add a warning here, but we won't for
      ;; now.
      (mv (ok)
          args-changedp
          (if (not args-changedp)
              x
            (change-vl-nonatom x :args args)))))

  (define vl-exprlist-resolve-indexing-aux
    ((x        vl-exprlist-p)
     (arrfal   "Fast alist binding names of arrays to anything.")
     (wirefal  "Fast alist binding names of wires (non-arrays) to anything.")
     (warnings vl-warninglist-p))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (changedp     booleanp :rule-classes :type-prescription)
        (new-x        (and (implies (force (vl-exprlist-p x))
                                    (vl-exprlist-p new-x))
                           (equal (len new-x) (len x)))))
    :verify-guards nil
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil nil))
         ((mv warnings car-changedp car-prime)
          (vl-expr-resolve-indexing-aux (car x) arrfal wirefal warnings))
         ((mv warnings cdr-changedp cdr-prime)
          (vl-exprlist-resolve-indexing-aux (cdr x) arrfal wirefal warnings))
         (changedp (or car-changedp cdr-changedp))
         (new-x    (cons car-prime cdr-prime)))
      (mv warnings changedp new-x)))
  ///
  (defthm-vl-expr-resolve-indexing-aux-flag
    (defthm true-listp-of-vl-exprlist-resolve-indexing-aux
      (b* (((mv ?warnings ?changedp new-x)
            (vl-exprlist-resolve-indexing-aux x arrfal wirefal warnings)))
        (true-listp new-x))
      :rule-classes :type-prescription
      :flag :list)
    :skip-others t)

  (local (defthm-vl-expr-resolve-indexing-aux-flag
           ;; BOZO wtf, why do I need this?
           (defthm l0
             (b* (((mv ?warnings ?changedp new-x)
                   (vl-exprlist-resolve-indexing-aux x arrfal wirefal warnings)))
               (iff new-x (consp x)))
             :flag :list)
           :skip-others t))

  (verify-guards vl-expr-resolve-indexing-aux))

(defmacro def-vl-resolve-indexing (name &key type body)
  `(define ,name
     :short ,(cat "Resolve @(':vl-index') operators throughout a
                   @(see " (symbol-name type) ").")
     ((x        ,type)
      (arrfal   "Fast alist binding array names to whatever.")
      (wirefal  "Fast alist binding wire names to whatever.")
      (warnings vl-warninglist-p))
     :returns
     (mv (warnings vl-warninglist-p)
         (new-x    ,type :hyp (force (,type x))))
     (b* ((warnings (vl-warninglist-fix warnings)))
       ,body)))

(defmacro def-vl-resolve-indexing-list (name &key type element)
  `(define ,name
     :short ,(cat "Resolve @(':vl-index') operators throughout a
                   @(see " (symbol-name type) ").")
     ((x        ,type)
      (arrfal   "Fast alist binding array names to whatever.")
      (wirefal  "Fast alist binding wire names to whatever.")
      (warnings vl-warninglist-p))
     :returns
     (mv (warnings vl-warninglist-p)
         (new-x    ,type :hyp (force (,type x))))
     (b* (((when (atom x))
           (mv (ok) nil))
          ((mv warnings car-prime) (,element (car x) arrfal wirefal warnings))
          ((mv warnings cdr-prime) (,name (cdr x) arrfal wirefal warnings)))
       (mv warnings (cons car-prime cdr-prime)))
     ///
     (defthm ,(intern-in-package-of-symbol
               (cat "TRUE-LISTP-OF-" (symbol-name name))
               name)
       (true-listp (mv-nth 1 (,name x arrfal wirefal warnings)))
       :rule-classes :type-prescription)

     (defthm ,(intern-in-package-of-symbol
               (cat "LEN-OF-" (symbol-name name))
               name)
       (equal (len (mv-nth 1 (,name x arrfal wirefal warnings)))
              (len x)))))

(def-vl-resolve-indexing vl-expr-resolve-indexing
  ;; Simple wrapper that just bundles up the changedp optimization.
  :type vl-expr-p
  :body
  (b* (((mv warnings ?changedp new-x)
        (vl-expr-resolve-indexing-aux x arrfal wirefal warnings)))
    (mv warnings new-x)))

(def-vl-resolve-indexing-list vl-exprlist-resolve-indexing
  ;; Simple wrapper that just bundles up the changedp optimization.
  :type vl-exprlist-p
  :element vl-expr-resolve-indexing)



(def-vl-resolve-indexing vl-maybe-expr-resolve-indexing
  :type vl-maybe-expr-p
  :body (if (not x)
            (mv warnings nil)
          (vl-expr-resolve-indexing x arrfal wirefal warnings)))

(def-vl-resolve-indexing vl-assign-resolve-indexing
  :type vl-assign-p
  :body (b* (((vl-assign x) x)
             ((mv warnings lvalue-prime)
              (vl-expr-resolve-indexing x.lvalue arrfal wirefal warnings))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings)))
            (mv warnings
                (change-vl-assign x
                                  :lvalue lvalue-prime
                                  :expr expr-prime))))

(def-vl-resolve-indexing-list vl-assignlist-resolve-indexing
  :type vl-assignlist-p
  :element vl-assign-resolve-indexing)


(def-vl-resolve-indexing vl-plainarg-resolve-indexing
  :type vl-plainarg-p
  :body (b* (((vl-plainarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings)))
            (mv warnings (change-vl-plainarg x :expr expr-prime))))

(def-vl-resolve-indexing-list vl-plainarglist-resolve-indexing
  :type vl-plainarglist-p
  :element vl-plainarg-resolve-indexing)


(def-vl-resolve-indexing vl-namedarg-resolve-indexing
  :type vl-namedarg-p
  :body (b* (((vl-namedarg x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings)))
            (mv warnings (change-vl-namedarg x :expr expr-prime))))

(def-vl-resolve-indexing-list vl-namedarglist-resolve-indexing
  :type vl-namedarglist-p
  :element vl-namedarg-resolve-indexing)

(def-vl-resolve-indexing vl-arguments-resolve-indexing
  :type vl-arguments-p
  :body (b* (((vl-arguments x) x)
             ((mv warnings args-prime)
              (if x.namedp
                  (vl-namedarglist-resolve-indexing x.args arrfal wirefal warnings)
                (vl-plainarglist-resolve-indexing x.args arrfal wirefal warnings))))
            (mv warnings (vl-arguments x.namedp args-prime))))

(def-vl-resolve-indexing vl-modinst-resolve-indexing
  :type vl-modinst-p
  :body (b* (((vl-modinst x) x)
             ((mv warnings args-prime)
              (vl-arguments-resolve-indexing x.portargs arrfal wirefal warnings)))
            (mv warnings (change-vl-modinst x :portargs args-prime))))

(def-vl-resolve-indexing-list vl-modinstlist-resolve-indexing
  :type vl-modinstlist-p
  :element vl-modinst-resolve-indexing)

(def-vl-resolve-indexing vl-gateinst-resolve-indexing
  :type vl-gateinst-p
  :body (b* (((vl-gateinst x) x)
             ((mv warnings args-prime)
              (vl-plainarglist-resolve-indexing x.args arrfal wirefal warnings)))
            (mv warnings (change-vl-gateinst x :args args-prime))))

(def-vl-resolve-indexing-list vl-gateinstlist-resolve-indexing
  :type vl-gateinstlist-p
  :element vl-gateinst-resolve-indexing)

(def-vl-resolve-indexing vl-delaycontrol-resolve-indexing
  :type vl-delaycontrol-p
  :body (b* (((vl-delaycontrol x) x)
             ((mv warnings value-prime)
              (vl-expr-resolve-indexing x.value arrfal wirefal warnings)))
            (mv warnings (change-vl-delaycontrol x :value value-prime))))

(def-vl-resolve-indexing vl-evatom-resolve-indexing
  :type vl-evatom-p
  :body (b* (((vl-evatom x) x)
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings)))
            (mv warnings (change-vl-evatom x :expr expr-prime))))

(def-vl-resolve-indexing-list vl-evatomlist-resolve-indexing
  :type vl-evatomlist-p
  :element vl-evatom-resolve-indexing)

(def-vl-resolve-indexing vl-eventcontrol-resolve-indexing
  :type vl-eventcontrol-p
  :body (b* (((vl-eventcontrol x) x)
             ((mv warnings atoms-prime)
              (vl-evatomlist-resolve-indexing x.atoms arrfal wirefal warnings)))
            (mv warnings (change-vl-eventcontrol x :atoms atoms-prime))))

(def-vl-resolve-indexing vl-repeateventcontrol-resolve-indexing
  :type vl-repeateventcontrol-p
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings))
             ((mv warnings ctrl-prime)
              (vl-eventcontrol-resolve-indexing x.ctrl arrfal wirefal warnings))
             (x-prime (change-vl-repeateventcontrol x
                                                    :expr expr-prime
                                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(encapsulate
 ()
 (local (in-theory (disable vl-delayoreventcontrol-p-when-vl-maybe-delayoreventcontrol-p)))
 (def-vl-resolve-indexing vl-delayoreventcontrol-resolve-indexing
   :type vl-delayoreventcontrol-p
   :body (case (tag x)
           (:vl-delaycontrol
            (vl-delaycontrol-resolve-indexing x arrfal wirefal warnings))
           (:vl-eventcontrol
            (vl-eventcontrol-resolve-indexing x arrfal wirefal warnings))
           (:vl-repeat-eventcontrol
            (vl-repeateventcontrol-resolve-indexing x arrfal wirefal warnings))
           (otherwise
            (mv (er hard 'vl-delayoreventcontrol-resolve-indexing "Provably impossible.")
                x)))))

(def-vl-resolve-indexing vl-maybe-delayoreventcontrol-resolve-indexing
  :type vl-maybe-delayoreventcontrol-p
  :body (if x
            (vl-delayoreventcontrol-resolve-indexing x arrfal wirefal warnings)
          (mv warnings nil)))

(defthm vl-maybe-delayoreventcontrol-resolve-indexing-under-iff
  (implies (force (vl-maybe-delayoreventcontrol-p x))
           (iff (mv-nth 1 (vl-maybe-delayoreventcontrol-resolve-indexing x arrfal wirefal warnings))
                x))
  :hints(("Goal"
          :in-theory (e/d (vl-maybe-delayoreventcontrol-resolve-indexing
                           vl-maybe-delayoreventcontrol-p)
                          (return-type-of-vl-delayoreventcontrol-resolve-indexing.new-x))
          :use ((:instance
                 return-type-of-vl-delayoreventcontrol-resolve-indexing.new-x)))))


(def-vl-resolve-indexing vl-assignstmt-resolve-indexing
  :type vl-assignstmt-p
  :body (b* (((vl-assignstmt x) x)
             ((mv warnings lvalue-prime)
              (vl-expr-resolve-indexing x.lvalue arrfal wirefal warnings))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings))
             ((mv warnings ctrl-prime)
              (vl-maybe-delayoreventcontrol-resolve-indexing x.ctrl arrfal wirefal warnings))
             (x-prime
              (change-vl-assignstmt x
                                    :lvalue lvalue-prime
                                    :expr expr-prime
                                    :ctrl ctrl-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing vl-deassignstmt-resolve-indexing
  :type vl-deassignstmt-p
  :body (b* (((vl-deassignstmt x) x)
             ((mv warnings lvalue-prime)
              (vl-expr-resolve-indexing x.lvalue arrfal wirefal warnings))
             (x-prime
              (change-vl-deassignstmt x :lvalue lvalue-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing vl-enablestmt-resolve-indexing
  :type vl-enablestmt-p
  :body (b* (((vl-enablestmt x) x)
             ((mv warnings id-prime)
              (vl-expr-resolve-indexing x.id arrfal wirefal warnings))
             ((mv warnings args-prime)
              (vl-exprlist-resolve-indexing x.args arrfal wirefal warnings))
             (x-prime
              (change-vl-enablestmt x
                                    :id id-prime
                                    :args args-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing vl-disablestmt-resolve-indexing
  :type vl-disablestmt-p
  :body (b* (((vl-disablestmt x) x)
             ((mv warnings id-prime)
              (vl-expr-resolve-indexing x.id arrfal wirefal warnings))
             (x-prime
              (change-vl-disablestmt x :id id-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing vl-eventtriggerstmt-resolve-indexing
  :type vl-eventtriggerstmt-p
  :body (b* (((vl-eventtriggerstmt x) x)
             ((mv warnings id-prime)
              (vl-expr-resolve-indexing x.id arrfal wirefal warnings))
             (x-prime
              (change-vl-eventtriggerstmt x :id id-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing vl-atomicstmt-resolve-indexing
  :type vl-atomicstmt-p
  :body (case (tag x)
          (:vl-nullstmt         (mv warnings x))
          (:vl-assignstmt       (vl-assignstmt-resolve-indexing x arrfal wirefal warnings))
          (:vl-deassignstmt     (vl-deassignstmt-resolve-indexing x arrfal wirefal warnings))
          (:vl-enablestmt       (vl-enablestmt-resolve-indexing x arrfal wirefal warnings))
          (:vl-disablestmt      (vl-disablestmt-resolve-indexing x arrfal wirefal warnings))
          (:vl-eventtriggerstmt (vl-eventtriggerstmt-resolve-indexing x arrfal wirefal warnings))
          (otherwise
           (mv (er hard 'vl-atomicstmt-resolve-indexing
                   "Impossible case.   This is not really an error.  We are just ~
                    using the guard mechanism to prove that all cases have been ~
                    covered.")
               x))))


(defines vl-stmt-resolve-indexing

  (define vl-stmt-resolve-indexing
    ((x        vl-stmt-p)
     (arrfal   "Fast alist binding names of arrays to anything.")
     (wirefal  "Fast alist binding names of wires (non-arrays) to anything.")
     (warnings vl-warninglist-p))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (new-x))
    :verify-guards nil
    :measure (two-nats-measure (acl2-count x) 1)
    :flag :stmt
    (b* (((when (vl-fast-atomicstmt-p x))
          (vl-atomicstmt-resolve-indexing x arrfal wirefal warnings))
         ((vl-compoundstmt x) x)
         ((mv warnings exprs-prime)
          (vl-exprlist-resolve-indexing x.exprs arrfal wirefal warnings))
         ((mv warnings stmts-prime)
          (vl-stmtlist-resolve-indexing x.stmts arrfal wirefal warnings))
         ((mv warnings ctrl-prime)
          (vl-maybe-delayoreventcontrol-resolve-indexing x.ctrl arrfal wirefal warnings))
         (x-prime
          (change-vl-compoundstmt x
                                  :exprs exprs-prime
                                  :stmts stmts-prime
                                  :ctrl ctrl-prime)))
      (mv (ok) x-prime)))

  (define vl-stmtlist-resolve-indexing
    ((x        vl-stmtlist-p)
     (arrfal   "Fast alist binding names of arrays to anything.")
     (wirefal  "Fast alist binding names of wires (non-arrays) to anything.")
     (warnings vl-warninglist-p))
    :returns
    (mv (new-warnings vl-warninglist-p)
        (new-x))
    :measure (two-nats-measure (acl2-count x) 0)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings car-prime)
          (vl-stmt-resolve-indexing (car x) arrfal wirefal warnings))
         ((mv warnings cdr-prime)
          (vl-stmtlist-resolve-indexing (cdr x) arrfal wirefal warnings)))
      (mv warnings (cons car-prime cdr-prime))))

  ///
  (defthm vl-stmtlist-resolve-indexing-when-atom
    (implies (atom x)
             (equal (vl-stmtlist-resolve-indexing x arrfal wirefal warnings)
                    (mv (vl-warninglist-fix warnings) nil))))

  (defthm vl-stmtlist-resolve-indexing-of-cons
    (equal (vl-stmtlist-resolve-indexing (cons a x) arrfal wirefal warnings)
           (b* (((mv warnings car-prime)
                 (vl-stmt-resolve-indexing a arrfal wirefal warnings))
                ((mv warnings cdr-prime)
                 (vl-stmtlist-resolve-indexing x arrfal wirefal warnings)))
             (mv warnings (cons car-prime cdr-prime)))))

  (local (defun my-induction (x arrfal wirefal warnings)
           (b* (((when (atom x))
                 (mv warnings x))
                ((mv warnings car-prime)
                 (vl-stmt-resolve-indexing (car x) arrfal wirefal warnings))
                ((mv warnings cdr-prime)
                 (my-induction (cdr x) arrfal wirefal warnings)))
             (mv warnings (cons car-prime cdr-prime)))))

  (defthm len-of-vl-stmtlist-resolve-indexing
    (b* (((mv ?warnings new-x)
          (vl-stmtlist-resolve-indexing x arrfal wirefal warnings)))
      (equal (len new-x)
             (len x)))
    :hints(("Goal" :induct (my-induction x arrfal wirefal warnings))))

  (defthm-vl-stmt-resolve-indexing-flag
    (defthm vl-stmt-p-of-vl-stmt-resolve-indexing
      (b* (((mv ?warnings new-x)
            (vl-stmt-resolve-indexing x arrfal wirefal warnings)))
        (implies (force (vl-stmt-p x))
                 (vl-stmt-p new-x)))
      :flag :stmt)

    (defthm vl-stmtlist-p-of-vl-stmtlist-resolve-indexing
      (b* (((mv ?warnings new-x)
            (vl-stmtlist-resolve-indexing x arrfal wirefal warnings)))
        (implies (force (vl-stmtlist-p x))
                 (vl-stmtlist-p new-x)))
      :flag :list))

  (verify-guards vl-stmt-resolve-indexing))

(def-vl-resolve-indexing vl-always-resolve-indexing
  :type vl-always-p
  :body (b* (((vl-always x) x)
             ((mv warnings stmt-prime)
              (vl-stmt-resolve-indexing x.stmt arrfal wirefal warnings))
             (x-prime
              (change-vl-always x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing-list vl-alwayslist-resolve-indexing
  :type vl-alwayslist-p
  :element vl-always-resolve-indexing)

(def-vl-resolve-indexing vl-initial-resolve-indexing
  :type vl-initial-p
  :body (b* (((vl-initial x) x)
             ((mv warnings stmt-prime)
              (vl-stmt-resolve-indexing x.stmt arrfal wirefal warnings))
             (x-prime
              (change-vl-initial x :stmt stmt-prime)))
            (mv warnings x-prime)))

(def-vl-resolve-indexing-list vl-initiallist-resolve-indexing
  :type vl-initiallist-p
  :element vl-initial-resolve-indexing)

(def-vl-resolve-indexing vl-port-resolve-indexing
  :type vl-port-p
  :body (b* (((vl-port x) x)
             ((unless x.expr)
              (mv warnings x))
             ((mv warnings expr-prime)
              (vl-expr-resolve-indexing x.expr arrfal wirefal warnings))
             (x-prime
              (change-vl-port x :expr expr-prime)))
          (mv warnings x-prime)))

(def-vl-resolve-indexing-list vl-portlist-resolve-indexing
  :type vl-portlist-p
  :element vl-port-resolve-indexing)


(def-vl-resolve-indexing vl-fundecl-resolve-indexing
  :type vl-fundecl-p
  :body
  (b* (((vl-fundecl x) x)

       ;; This is tricky because the function can have its own declarations.
       ((mv regdecls vardecls eventdecls paramdecls)
        (vl-filter-blockitems x.decls))

       ;; Remove any locally declared names from the global arrfal/wirefal
       ;; we've been given.  In practice, shadowed-names should be short
       ;; because most functions are pretty simple and don't have more than a
       ;; few variables.  So, I'm not worried about just using
       ;; set-difference-equal calls, here.
       (shadowed-names
        (mergesort (append (vl-regdecllist->names regdecls)
                           (vl-vardecllist->names vardecls)
                           (vl-eventdecllist->names eventdecls)
                           (vl-paramdecllist->names paramdecls))))
       (visible-global-arrnames
        (set-difference-equal (alist-keys arrfal) shadowed-names))
       (visible-global-wirenames
        (set-difference-equal (alist-keys wirefal) shadowed-names))

       ;; It would probably be safe to turn indexing operations that are
       ;; selecting from most parameters and variables into bitselects.  But
       ;; for now we'll play it safe, and only really try to deal with
       ;; registers here.
       ((mv reg-arrays reg-wires)
        (vl-regdecllist-filter-arrays regdecls nil nil))

       ;; The function's inputs are also okay to turn into bit selects, because
       ;; they can't be arrays.
       (innames         (vl-taskportlist->names x.inputs))

       (local-arrnames  (append-without-guard reg-arrays visible-global-arrnames))
       (local-wirenames (append-without-guard reg-wires
                                              innames
                                              visible-global-wirenames))
       (local-arrfal    (make-lookup-alist local-arrnames))
       (local-wirefal   (make-lookup-alist local-wirenames))
       ((mv warnings new-body)
        (vl-stmt-resolve-indexing x.body local-arrfal local-wirefal warnings))
       (- (fast-alist-free local-arrfal))
       (- (fast-alist-free local-wirefal))
       (new-x (change-vl-fundecl x :body new-body)))
    (mv warnings new-x)))

(def-vl-resolve-indexing-list vl-fundecllist-resolve-indexing
  :type vl-fundecllist-p
  :element vl-fundecl-resolve-indexing)

(define vl-module-resolve-indexing ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)

       ((mv reg-arrays reg-wires)
        (vl-regdecllist-filter-arrays x.regdecls nil nil))
       ((mv net-arrays net-wires)
        (vl-netdecllist-filter-arrays x.netdecls nil nil))

       (arr-names (append (vl-regdecllist->names reg-arrays)
                          (vl-netdecllist->names net-arrays)))
       (wire-names (append (vl-regdecllist->names reg-wires)
                           (vl-netdecllist->names net-wires)))

       (arrfal  (make-lookup-alist arr-names))
       (wirefal (make-lookup-alist wire-names))

       (warnings x.warnings)
       ((mv warnings ports)     (vl-portlist-resolve-indexing     x.ports arrfal wirefal warnings))
       ((mv warnings assigns)   (vl-assignlist-resolve-indexing   x.assigns arrfal wirefal warnings))
       ((mv warnings modinsts)  (vl-modinstlist-resolve-indexing  x.modinsts arrfal wirefal warnings))
       ((mv warnings gateinsts) (vl-gateinstlist-resolve-indexing x.gateinsts arrfal wirefal warnings))
       ((mv warnings alwayses)  (vl-alwayslist-resolve-indexing   x.alwayses arrfal wirefal warnings))
       ((mv warnings initials)  (vl-initiallist-resolve-indexing  x.initials arrfal wirefal warnings))
       ((mv warnings fundecls)  (vl-fundecllist-resolve-indexing  x.fundecls arrfal wirefal warnings))

       (- (fast-alist-free arrfal))
       (- (fast-alist-free wirefal))
       (new-x (change-vl-module x
                                :ports ports
                                :assigns assigns
                                :modinsts modinsts
                                :gateinsts gateinsts
                                :alwayses alwayses
                                :initials initials
                                :fundecls fundecls
                                :warnings warnings)))
    new-x))

(defprojection vl-modulelist-resolve-indexing (x)
  (vl-module-resolve-indexing x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-resolve-indexing ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x)
       (new-mods (vl-modulelist-resolve-indexing x.mods)))
    (change-vl-design x :mods new-mods)))

