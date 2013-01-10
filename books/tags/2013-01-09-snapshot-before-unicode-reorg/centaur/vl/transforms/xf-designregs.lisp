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
(include-book "../mlib/writer")
(include-book "../mlib/hid-tools")
(include-book "../mlib/expr-tools")
(include-book "../mlib/range-tools")
(include-book "../mlib/find-item")
(include-book "../util/sum-nats")
(include-book "../util/cwtime")
(include-book "defsort/defsort" :dir :system)
(local (include-book "../util/arithmetic"))

(local (include-book "../primitives"))
(local (include-book "centaur/esim/esim-sexpr-support" :dir :system))

(defxdoc design-regs
  :parents (transforms)
  :short "Identify designer-visible registers within a module."

  :long "<p>We expect to run this only on fully-simplified modules.  In
particular, sizing needs to have been done and we need to have converted all
latches and flops into @('VL_N_BIT_REG') and @('VL_N_BIT_LATCH') instances.</p>

<p><b>BOZO</b> at the moment this doesn't handle modules with externals.
That's going to be a huge mess.</p>")



(defenum vl-dreg-type-p (:vl-flop :vl-latch)
  :parents (design-regs)
  :short "Valid @('type') entries for a @(see vl-dreg-p)"

  :long "<p>At the moment we only collect @('vl-dreg-p') objects for flops and
latches which have been inferred.  We may wish to add support for other kinds
of registers in the future.</p>")



(defsection vl-dreg-type-from-modname
  :parents (design-regs)
  :short "Infer the appropriate @(see vl-dreg-type-p) given a module name."

  :long "<p>@(call vl-dreg-type-from-modname) is given the name of a module and
returns either a @(see vl-dreg-type-p) or @('NIL').</p>

<p>We return @(':vl-flop') for any @('x') matching @('VL_N_BIT_FLOP') and
@(':vl-latch') for any @('x') matching @('VL_N_BIT_LATCH').  For all other
@('x'), we return @('NIL').</p>"

  (defund vl-dreg-type-from-modname (x)
    (declare (xargs :guard (stringp x)
                    :guard-debug t))
    (b* ((xl (length x))
         ((unless (and (str::strprefixp "VL_" x)
                       (< 3 xl)))
          nil)
         ((mv val len)
          (str::parse-nat-from-string x 0 0 3 xl))
         ((unless (and (posp len)
                       (posp val)))
          nil)
         (new-pos (+ len 3))
         (tail    (and (< new-pos xl)
                       (str::subseq x new-pos nil))))
        (cond ((equal tail "_BIT_FLOP")
               :vl-flop)
              ((equal tail "_BIT_LATCH")
               :vl-latch)
              (t
               nil))))

  (assert! (equal (vl-dreg-type-from-modname "VL_1_BIT_LATCH") :vl-latch))
  (assert! (equal (vl-dreg-type-from-modname "VL_24_BIT_LATCH") :vl-latch))
  (assert! (equal (vl-dreg-type-from-modname "VL_1_BIT_FLOP") :vl-flop))
  (assert! (equal (vl-dreg-type-from-modname "VL_32_BIT_FLOP") :vl-flop))
  (assert! (not (vl-dreg-type-from-modname "VL_1_BIT_LATCHX")))
  (assert! (not (vl-dreg-type-from-modname "VL_1_BIT_FLOPX")))
  (assert! (not (vl-dreg-type-from-modname "VL_1__BIT_FLOP")))

  (local (in-theory (enable vl-dreg-type-from-modname)))

  (defthm vl-dreg-type-p-of-vl-dreg-type-from-modname
    (equal (vl-dreg-type-p (vl-dreg-type-from-modname x))
           (if (vl-dreg-type-from-modname x)
               t
             nil))))



(defaggregate vl-dreg
  (hid range iname type)
  :tag :vl-dreg
  :require ((vl-expr-p-of-vl-dreg->hid       (vl-expr-p hid))
            (vl-hidexpr-p-of-vl-dreg->hid    (vl-hidexpr-p hid))
            (vl-hid-indicies-resolved-p-of-vl-dreg->hid
             (vl-hid-indicies-resolved-p hid))
            (vl-hid-fixed-p-of-vl-dreg->hid
             (vl-hid-fixed-p hid))

            (vl-maybe-range-p-of-vl-dreg->range
             (vl-maybe-range-p range))
            (vl-maybe-range-resolved-p-of-vl-dreg->range
             (vl-maybe-range-resolved-p range))

            (stringp-of-vl-dreg->iname (stringp iname))

            (vl-dreg-type-p-of-vl-dreg->type (vl-dreg-type-p type)))

  :parents (design-regs)

  :short "Description of a <b>d</b>esign <b>reg</b>ister."

  :long "<p>We can create @('vl-dreg-p') objects corresponding to all of the
@('reg') elements of some fully-simplified modules.</p>

<ul>

<li>@('hid') is a @(see vl-hidexpr-p) that represents the path to this
@('reg'); its indicies are resolved as in @(see
vl-hid-indicies-resolved-p).</li>

<li>@('range') is the range for this register with resolved indicies, or
@('nil') if this is a plain @('reg').</li>

<li>@('iname') is the name of the @('VL_N_BIT_FLOP') or @('VL_N_BIT_LATCH')
instance in the final module.  Usually if the reg is named @('foo'), then
@('iname') will be named @('foo_inst'), but the actual name may vary since it's
generated by a @(see vl-namefactory-p).</li>

<li>@('type') is a @(see vl-dreg-type-p) that indicates the kind of register we
are dealing with.</li>

</ul>")

(defthm vl-dreg->type-cases
  (implies (and (not (equal (vl-dreg->type x) :vl-flop))
                (vl-dreg-p x))
           (equal (vl-dreg->type x) :vl-latch))
  :hints(("Goal" :in-theory (e/d (vl-dreg-type-p)
                                 (vl-dreg-type-p-of-vl-dreg->type))
          :use ((:instance vl-dreg-type-p-of-vl-dreg->type)))))


(defsection vl-dreg-flatname

  (defund vl-dreg-flatname (x)
    (declare (xargs :guard (vl-dreg-p x)))
    (vl-flatten-hidexpr (vl-dreg->hid x)))

  (defthm stringp-of-vl-dreg-flatname
    (stringp (vl-dreg-flatname x))
    :rule-classes :type-prescription))



(defsection vl-dreglist-p

  (deflist vl-dreglist-p (x)
    (vl-dreg-p x)
    :guard t
    :elementp-of-nil nil)

  (defprojection vl-dreglist-flatnames (x)
    (vl-dreg-flatname x)
    :guard (vl-dreglist-p x)
    :rest
    ((defthm string-listp-of-vl-dreglist-flatnames
       (string-listp (vl-dreglist-flatnames x)))))

  (defprojection vl-dreglist-types (x)
    (vl-dreg->type x)
    :guard (vl-dreglist-p x)
    :nil-preservingp t))



(defsection vl-dregalist-p
  :parents (design-regs)
  :short "Alist mapping module names to lists of @(see vl-dreg-p)."

  (defund vl-dregalist-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        t
      (and (consp (car x))
           (stringp (caar x))
           (vl-dreglist-p (cdar x))
           (vl-dregalist-p (cdr x)))))

  (local (in-theory (enable vl-dregalist-p)))

  (defthm vl-dregalist-p-when-atom
    (implies (atom x)
             (vl-dregalist-p x)))

  (defthm vl-dregalist-p-of-cons
    (equal (vl-dregalist-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (vl-dreglist-p (cdr a))
                (vl-dregalist-p x))))

  (defthm vl-dreglist-p-of-hons-assoc-equal
    (implies (vl-dregalist-p x)
             (vl-dreglist-p (cdr (hons-assoc-equal a x))))))




(defsection vl-extend-dreglist
  :parents (design-regs)
  :short "@(call vl-extend-dreglist) extends @('x'), a list of @(see
vl-dreg-p)s, by prepending @('instname') to the @('hid') of every member of
@('x')."

  :long "<p>This is a basic operation for constructing the full list of dregs
for a module.  For example, if the full list of dregs for @('foo') includes
@('a.b.c') and @('d.e.f'), then calling @('vl-extend-dreg') will give us a new
list of dregs that includes @('foo.a.b.c') and @('foo.d.e.f').  See @(see
vl-modinst-infer-dregs).</p>"

  (defund vl-extend-dreglist (instname x)
    (declare (xargs :guard (and (stringp instname)
                                (vl-dreglist-p x))))
    (if (atom x)
        nil
      (let* ((dreg1         (car x))
             (new-hid-part1 (make-vl-atom :guts (make-vl-hidpiece :name instname)))
             (new-hid-part2 (vl-dreg->hid dreg1))
             (new-hid       (make-vl-nonatom :op :vl-hid-dot
                                             :args (list new-hid-part1 new-hid-part2)))
             (dreg1-prime   (change-vl-dreg dreg1 :hid new-hid)))
        (cons dreg1-prime (vl-extend-dreglist instname (cdr x))))))

  (local (in-theory (enable vl-extend-dreglist)))

  (defthm true-listp-of-vl-extend-dreglist
    (true-listp (vl-extend-dreglist instname x))
    :rule-classes :type-prescription)

  (defthm vl-dreglist-p-of-vl-extend-dreglist
    (implies (and (force (stringp instname))
                  (force (vl-dreglist-p x)))
             (vl-dreglist-p (vl-extend-dreglist instname x)))))



; Ugh.  Collecting the dregs for the hierarchy is tricky because we need to
; process the lower-level modules first and then eventually recur up to the
; higher-level modules.  One way to do this might be to add a stack depth, but
; I think it's easier to just require that the modules be put into dependency
; order via vl-deporder-sort.  So, that's the approach I take below.


(defsection vl-modinst-collect-dregs
  :parents (design-regs)
  :short "Construct the list of @(see vl-dreg-p)s for a @(see vl-modinst-p)."

  :long "<p>@(call vl-modinst-collect-dregs) is given as inputs:</p>

<ul>

<li>@('x'), a module instance, </li>

<li>@('mod'), the module wherein @('x') occurs, and </li>

<li>@('alist'), which is a fast @(see vl-dregalist-p) that, loosely speaking,
must associate all previously encountered module names with their associated
lists of dregs; see @(see vl-modulelist-infer-dregs).</li>

</ul>

<p>If @('x') is an instance of an @('VL_N_BIT_FLOP') or @('VL_N_BIT_LATCH'), we
produce a single @(see vl-dreg-p) corresponding to the output of @('x').  The
range for this dreg is determined by the corresponding wire in @('mod').</p>

<p>Otherwise, suppose @('x') is an instance of module @('foo').  We look up the
dregs for @('foo') and extend each of them with the instance name of @('x');
see @(see vl-extend-dreglist).</p>"

  (defund vl-modinst-collect-dregs (x mod alist)
    (declare (xargs :guard (and (vl-modinst-p x)
                                (vl-module-p mod)
                                (vl-dregalist-p alist))))
    (b* ((modname  (vl-modinst->modname x))
         (instname (vl-modinst->instname x))
         (type     (vl-dreg-type-from-modname modname))

         ((unless type)
          ;; Not a VL_N_BIT_FLOP or VL_N_BIT_REG, so just look it up in the alist.
          (b* ((lookup    (hons-get modname alist))
               ((unless instname)
                (er hard? 'vl-modinst-collect-dregs
                    "expected all module instances to be named."))
               ((unless lookup)
                (er hard? 'vl-modinst-collect-dregs
                    "Expected all submodules to be bound in alist, but there ~
                     is no entry for module ~x0.  Are the modules in dependency ~
                     order?" modname)))
              (vl-extend-dreglist instname (cdr lookup))))

         ;; Otherwise, we found an VL_N_BIT_FLOP or VL_N_BIT_REG instance.
         ;; In either case, the ports have the form (q clk d) where q is
         ;; the output wire.
         (args   (vl-modinst->portargs x))
         ((when (vl-arguments->namedp args))
          (er hard? 'vl-modinst-collect-dregs "expected all arguments to be resolved."))

         (args   (vl-arguments->args args))
         ((unless (and (equal (len args) 3)
                       (eq (vl-plainarg->dir (car args)) :vl-output)
                       (equal (vl-plainarg->portname (car args)) "q")))
          (er hard? 'vl-modinst-collect-dregs
              "ports for flop/latch not (q clk d)?  inst: ~x0~%" x))

         (q-expr  (vl-plainarg->expr (car args)))
         (q-width (and q-expr (vl-expr->finalwidth q-expr)))
         ((unless (and q-expr
                       (vl-idexpr-p q-expr)
                       (posp q-width)))
          (er hard? 'vl-modinst-collect-dregs "q for flop/latch invalid??"))

         (q-name (vl-idexpr->name q-expr))
         (q-decl (vl-find-netdecl q-name (vl-module->netdecls mod)))
         ((unless q-decl)
          (er hard? 'vl-modinst-collect-dregs "expected declaration of ~s0." q-name))

         (q-range (vl-netdecl->range q-decl))
         ((unless (and (vl-maybe-range-resolved-p q-range)
                       (equal (vl-maybe-range-size q-range) q-width)))
          (er hard? 'vl-modinst-collect-dregs "range/port size mismatch"))

         ((unless instname)
          (er hard? 'vl-modinst-collect-dregs "expected instance to be named"))

         (hid    (make-vl-atom :guts (make-vl-hidpiece :name q-name)))
         (dreg   (make-vl-dreg :hid hid
                               :range q-range
                               :iname instname
                               :type type)))
        (list dreg)))

  (local (in-theory (enable vl-modinst-collect-dregs)))

  (defthm true-listp-of-vl-modinst-collect-dregs
    (true-listp (vl-modinst-collect-dregs x mod alist))
    :rule-classes :type-prescription)

  (defthm vl-dreglist-p-of-vl-modinst-collect-dregs
    (implies (and (force (vl-modinst-p x))
                  (force (vl-module-p mod))
                  (force (vl-dregalist-p alist)))
             (vl-dreglist-p (vl-modinst-collect-dregs x mod alist)))))





(defmapappend vl-modinstlist-collect-dregs (x mod alist)
  (vl-modinst-collect-dregs x mod alist)
  :guard (and (vl-modinstlist-p x)
              (vl-module-p mod)
              (vl-dregalist-p alist))
  :transform-true-list-p t
  ;; It should be pretty straightforward to develop a transform-exec version of
  ;; vl-modinst-collect-dregs for a more efficient implementation, but I
  ;; suspect it isn't worth the effort.
  :transform-exec nil
  :parents (design-regs)
  :short "Construct the list of @(see vl-dreg-p)s for a list of @(see
vl-modinst-p)s."
  :rest
  ((defthm vl-dreglist-p-of-vl-modinstlist-collect-dregs
     (implies (and (force (vl-modinstlist-p x))
                   (force (vl-module-p mod))
                   (force (vl-dregalist-p alist)))
              (vl-dreglist-p (vl-modinstlist-collect-dregs x mod alist))))))



(defsection vl-modulelist-collect-dregs
  :parents (design-regs)
  :short "Construct a @(see vl-dregalist-p) for a list of modules."
  :long "<p><b>Signature:</b> @(call vl-modulelist-collect-dregs) returns a
@(see vl-dregalist-p).</p>

<p>Note: A fast alist is returned.</p>

<p>Note: @('x') must fully-transformed and in dependency order; see @(see
vl-deporder-sort).  A hard error will result if these conditions are not
met.</p>"

  (defund vl-modulelist-collect-dregs-aux (x alist)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (vl-dregalist-p alist))))
    (if (atom x)
        alist
      (b* ((mod1   (car x))
           (name1  (vl-module->name mod1))
           ((when (vl-dreg-type-from-modname name1))
            ;; VL_N_BIT_FLOP or VL_N_BIT_LATCH are "primitives", don't put
            ;; them into the alist.
            (vl-modulelist-collect-dregs-aux (cdr x) alist))
           (insts1 (vl-module->modinsts mod1))
           (dregs  (vl-modinstlist-collect-dregs insts1 mod1 alist))
           (alist  (hons-acons name1 dregs alist)))
          (vl-modulelist-collect-dregs-aux (cdr x) alist))))

  (defund vl-modulelist-collect-dregs (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (vl-modulelist-collect-dregs-aux x (len x)))

  (local (in-theory (enable vl-modulelist-collect-dregs-aux
                            vl-modulelist-collect-dregs)))

  (defthm vl-dregalist-p-of-vl-modulelist-collect-dregs-aux
    (implies (and (force (vl-modulelist-p x))
                  (force (vl-dregalist-p alist)))
             (vl-dregalist-p (vl-modulelist-collect-dregs-aux x alist))))

  (defthm vl-dregalist-p-of-vl-modulelist-collect-dregs
    (implies (force (vl-modulelist-p x))
             (vl-dregalist-p (vl-modulelist-collect-dregs x)))))




(defsection vl-dreg<

  (defund vl-dreg< (x y)
    (declare (xargs :guard (and (vl-dreg-p x)
                                (vl-dreg-p y))))
    (b* ((flat-x (vl-flatten-hidexpr (vl-dreg->hid x)))
         (flat-y (vl-flatten-hidexpr (vl-dreg->hid y))))
        (or (str::strnat< flat-x flat-y)
            (and (equal flat-x flat-y)
                 (<< x y)))))

  (local (in-theory (enable vl-dreg<)))

  (defthm vl-dreg<-irreflexive
    (not (vl-dreg< x x)))

  (defthm vl-dreg<-antisymmetric
    (implies (vl-dreg< x y)
             (not (vl-dreg< y x))))

  (defthm vl-dreg<-transitive
    (implies (and (vl-dreg< x y)
                  (vl-dreg< y z))
             (vl-dreg< x z))))



(defsection vl-dreg-sort

  (acl2::defsort :comparablep vl-dreg-p
                 :compare< vl-dreg<
                 :prefix vl-dreg)

  (defthm vl-dreg-list-p-removal
    (equal (vl-dreg-list-p x)
           (vl-dreglist-p x))
    :hints(("Goal" :in-theory (enable vl-dreg-list-p))))

  (defthm vl-dreglist-p-of-vl-dreg-sort
    (implies (force (vl-dreglist-p x))
             (vl-dreglist-p (vl-dreg-sort x)))
    :hints(("Goal"
            :in-theory (disable vl-dreg-sort-creates-comparable-listp)
            :use ((:instance vl-dreg-sort-creates-comparable-listp (acl2::x x)))))))



(defpp vl-pp-pretty-range (x)
  :guard (and (vl-range-p x)
              (vl-range-resolved-p x))
  :body
  (vl-ps-seq (vl-print "[")
             (vl-print (vl-resolved->val (vl-range->msb x)))
             (vl-print ":")
             (vl-print (vl-resolved->val (vl-range->lsb x)))
             (vl-print "]")))

(defpp vl-pp-pretty-maybe-range (x)
  :guard (and (vl-maybe-range-p x)
              (vl-maybe-range-resolved-p x))
  :body
  (if x
      (vl-pp-pretty-range x)
    ps))

(defpp vl-pp-dreg (x)
  :guard (vl-dreg-p x)
  :body
  (b* ((hid   (vl-dreg->hid x))
       (range (vl-dreg->range x))
       (iname (vl-dreg->iname x))
       (type  (vl-dreg->type x)))
      (vl-ps-seq
       (vl-print (vl-flatten-hidexpr hid))
       (vl-pp-pretty-maybe-range range)
       (vl-print (case type
                   (:vl-flop " (flop)")
                   (:vl-latch " (latch)")))
       (vl-print " (driver: ")
       (vl-print iname)
       (vl-print ")"))))

(defpp vl-pp-dreglist-aux (x)
  :guard (vl-dreglist-p x)
  :body
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-dreg (car x))
               (vl-println "")
               (vl-pp-dreglist-aux (cdr x)))))

(defpp vl-pp-dreglist (x)
  :guard (vl-dreglist-p x)
  :body (vl-pp-dreglist-aux (vl-dreg-sort (redundant-list-fix x))))

(defsection vl-pps-dreglist

  (defund vl-pps-dreglist (x)
    (declare (xargs :guard (vl-dreglist-p x)))
    (with-local-ps (vl-pp-dreglist x)))

  (local (in-theory (enable vl-pps-dreglist)))

  (defthm stringp-of-vl-pps-dreglist
    (stringp (vl-pps-dreglist x))
    :rule-classes :type-prescription))






(defsection vl-emap-p
  :parents (design-regs)
  :short "A mapping from EMOD state bits to registers in the design."
  :long "<p>This is just an alist mapping symbols to symbols.  See also @(see
vl-dreglist-emap).</p>"

  (defund vl-emap-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        (not x)
      (and (consp (car x))
           (symbolp (caar x))
           (symbolp (cdar x))
           (vl-emap-p (cdr x)))))

  (local (in-theory (enable vl-emap-p)))

  (defthm vl-emap-p-when-atom
    (implies (atom x)
             (equal (vl-emap-p x)
                    (not x))))

  (defthm vl-emap-p-of-cons
    (equal (vl-emap-p (cons a x))
           (and (consp a)
                (symbolp (car a))
                (symbolp (cdr a))
                (vl-emap-p x))))

  (defthm vl-emap-p-of-append
    (implies (and (force (vl-emap-p x))
                  (force (vl-emap-p y)))
             (vl-emap-p (append x y))))

  (defthm alistp-when-vl-emap-p
    (implies (vl-emap-p x)
             (alistp x)))

  (defthm symbolp-of-cdr-hons-assoc-equal-of-vl-emap-p
    (implies (vl-emap-p x)
             (symbolp (cdr (hons-assoc-equal a x)))))

  (defthm vl-emap-p-of-pairlis$
    (implies (and (force (symbol-listp x))
                  (force (symbol-listp y)))
             (vl-emap-p (pairlis$ x y)))
    :hints(("Goal" :in-theory (enable (:induction pairlis$)))))

  (defthm symbol-listp-of-strip-cars-when-vl-emap-p
    (implies (vl-emap-p x)
             (symbol-listp (strip-cars x))))

  (defthm symbol-listp-of-strip-cdrs-when-vl-emap-p
    (implies (vl-emap-p x)
             (symbol-listp (strip-cdrs x)))))




;; If these change, the names in the discussions and code below will need to
;; also be updated.

(local (assert! (equal (acl2::mod-state (vl-module->esim *VL-1-BIT-FLOP*))
                       '(ACL2::S- ACL2::S+))))

(local (assert! (equal (acl2::mod-state (vl-module->esim *VL-1-BIT-LATCH*))
                       '(ACL2::S))))



(defxdoc vl-dreglist-emap
  :parents (design-regs)
  :short "Map from EMOD state bits to actual registers in the design."

  :long "<p>Each register in the Verilog module corresponds to some number of
state bits in the Emod simulation.  For instance, if @('foo.bar.baz') is a
@('reg') with range @('[3:0]'), and represents a flop, then we might end up
with 8 state bits with names like:</p>

@({
   foo!bar!baz_inst!bit_0!S-
   foo!bar!baz_inst!bit_0!S+
   foo!bar!baz_inst!bit_1!S-
   foo!bar!baz_inst!bit_1!S+
   ...
})

<p>The function @('vl-dreglist-emap') can be used to construct an alist that
maps these bits to names like:</p>

@({
   foo.bar.baz[0]:master        // for flops
   foo.bar.baz[0]:slave
   foo.bar.baz[1]:master
   foo.bar.baz[2]:master
   ...
})

<p>Meanwhile, if this @('baz') is a latch instead of a flop, then there will
only be four state bits with names:</p>

@({
  foo!bar!baz_inst!bit_0!S
  foo!bar!baz_inst!bit_1!S
  foo!bar!baz_inst!bit_2!S
  foo!bar!baz_inst!bit_3!S
})

<p>And here @('vl-dreglist-emap') will bind these bits to the Verilog-style
names:</p>

@({
  foo.bar.baz[0]
  foo.bar.baz[1]
  foo.bar.baz[2]
  foo.bar.baz[3]
})

<p>We originally developed emaps for a now-defunct equivalence checking tool
named @('vl-equiv'), but these names are still used in a signal-hunting
tool.</p>

<p>@(call vl-dreglist-emap) is given a list of @(see vl-dreg-p)s.  Ordinarily
this list should be the list of dregs that have been collected for some module;
see @(see vl-modulelist-collect-dregs).</p>

<p>We return @('(mv successp emap)').  On success, @('emap') is an ordinary,
non-fast association list that binds Emod-style names (symbols) such as
@('|foo!bar!baz_inst!bit_0!BIT!S-|') to Verilog-style names (symbols) such as
@('|foo.bar.baz[0]:master|').  See @(see vl-emap-p).  The cars and cdrs of the
map are guaranteed to be unique and non-nil.</p>")


(defsection vl-dreg-emod-root

; (VL-DREG-EMOD-ROOT X) is given a dreg and constructs a name like
; "foo!bar!baz_inst".  Although this name is similar to the flattened
; HID name for X, it is different because:
;
;   (1) We use "!" rather than "." as the separator, because we are
;       producing the name of the EMOD state bit, and
;
;   (2) We use "baz_inst" (or similar) instead of "baz".  See the
;       documentation for dregs.  Basically, "baz" becomes an ordinary
;       wire, and "baz_inst" is the instance name of the VL_N_BIT_FLOP
;       or VL_N_BIT_LATCH that is driving baz.
;
; I originally built the string with cat.  Now I instead append
; onto a character list, for efficiency.

  (defund vl-dreg-emod-root-aux (x acc)
    ;; Given a hierarchical identifier expression like foo.bar.baz, we produce
    ;; a string like "foo!bar!".  That is, we chop off the final part of the
    ;; name ("baz") and join the other names together with "!".
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-hidexpr-p x)
                                (vl-hid-indicies-resolved-p x)
                                (character-listp acc))))
    (if (vl-fast-atom-p x)
        acc
      (let ((op   (vl-nonatom->op x))
            (args (vl-nonatom->args x)))
        (case op
          (:vl-hid-dot
           (b* ((acc (str::revappend-chars (vl-hidpiece->name (vl-atom->guts (first args)))
                                           acc))
                (acc (cons #\! acc)))
             (vl-dreg-emod-root-aux (second args) acc)))
          (:vl-hid-arraydot
           (progn$
            (er hard? 'vl-dreg-emod-root-aux "Add support for arraydot?")
            acc))
          (otherwise
           (progn$
            (er hard 'vl-dreg-emod-root-aux "Impossible")
            acc))))))

  (defthm character-listp-of-vl-dreg-emod-root-aux
    (implies (character-listp acc)
             (character-listp (vl-dreg-emod-root-aux x acc)))
    :hints(("Goal" :in-theory (enable vl-dreg-emod-root-aux))))


  (defund vl-dreg-emod-root (x acc)
    ;; Given a dreg for something like foo.bar.baz, we construct a string like
    ;; foo!bar!baz_inst
    (declare (xargs :guard (and (vl-dreg-p x)
                                (character-listp acc))))
    (let ((acc (vl-dreg-emod-root-aux (vl-dreg->hid x) acc)))
      (str::revappend-chars (vl-dreg->iname x) acc)))

  (defthm character-listp-of-vl-dreg-emod-root
    (implies (character-listp acc)
             (character-listp (vl-dreg-emod-root x acc)))
    :hints(("Goal" :in-theory (enable vl-dreg-emod-root)))))



(defsection vl-dreg-flop-emap

; (VL-DREG-FLOP-EMAP X) is given a dreg (which must have type flop) and
; produces a mapping from EMOD state bits to Verilog-style names.
;
; The mod-state of a VL_1_BIT_FLOP looks like (S- S+).
;
; However, the mod-state for a VL_N_BIT_FLOP for N>1 is more complex because we
; use a list of VL_1_BIT_FLOP instances, and in fact looks like this:
;
;    ((|bit_0!S-|     |bit_0!S+)
;     (|bit_1!S-|     |bit_1!S+)
;     ...
;     (|bit_{n-1}!S-| |bit_{n-1}!S+))
;
; In either case, regard the S- bits as "master" bits, whereas the S+ bits are
; "slave" bits.
;
; We need to construct a mapping between names like foo.bar.baz[3]:master and
; foo!bar!baz_inst!bit_3!S-.  To complicate this, the range of foo.bar.baz
; might use indicies like [13:10] instead of [3:0], in which case we need to
; actually map from foo.bar.baz[13]:master to foo!bar!baz_inst!bit_3!S- and so
; on.  This is because basically when we have:
;
;    reg [13:10] foo;
;    always @(posedge clk) foo <= rhs;
;
; We end up with something that looks roughly like this:
;
;    wire [13:10] foo;
;    VL_4_BIT_FLOP(foo, rhs_temp);
;
; The state bits like |...!bit_3!S-| are always indexed from 0 to N-1, because
; they are coming from the VL_4_BIT_FLOP instance.  Then, bits like foo[13] are
; connected to the output bit q[3] of the flop.
;
; We deal with the disconnect in indicies by constructing the list of Verilog
; style names separately from the list of Emod style names.  We then zip the
; two lists togeter using pairlis$.

  (defun vl-make-name-array (head n tail)
    (declare (xargs :ruler-extenders :all))
    (cons (cons n (cat head (natstr n) tail))
          (if (zp n)
              nil
            (vl-make-name-array head (1- n) tail))))

  (defconst *vl-master-name-array*
    ;; Array of pre-computed strings "[0]:master", "[1]:master", ..., "[255]:master"
    (compress1 '*vl-master-name-array*
               (cons (list :HEADER
                           :DIMENSIONS (list 256)
                           :MAXIMUM-LENGTH 257
                           :DEFAULT 0
                           :NAME '*vl-master-name-array*)
                     (vl-make-name-array "[" 255 "]:master"))))

  (defconst *vl-slave-name-array*
    ;; Array of pre-computed strings "[0]:slave", "[1]:slave", ..., "[255]:slave"
    (compress1 '*vl-slave-name-array*
               (cons (list :HEADER
                           :DIMENSIONS (list 256)
                           :MAXIMUM-LENGTH 257
                           :DEFAULT 0
                           :NAME '*vl-slave-name-array*)
                     (vl-make-name-array "[" 255 "]:slave"))))

  (defund vl-verilog-style-flop-master-names (root indices acc)
    (declare (xargs :guard (and (stringp root)
                                (nat-listp indices))))
    (if (atom indices)
        acc
      (let* (([n]master
              (mbe :logic
                   (cat "[" (natstr (car indices)) "]:master")
                   :exec
                   (if (< (car indices) 256)
                       (aref1 '*vl-master-name-array* *vl-master-name-array* (car indices))
                     (cat "[" (natstr (car indices)) "]:master"))))
             (root[n]master (cat root [n]master))
             (master        (intern root[n]master "ACL2"))
             (acc           (cons master acc)))
        (vl-verilog-style-flop-master-names root (cdr indices) acc))))

  (local (assert! (equal (vl-verilog-style-flop-master-names "foo" (list 5 4 3) nil)
                         (list 'ACL2::|foo[3]:master|
                               'ACL2::|foo[4]:master|
                               'ACL2::|foo[5]:master|))))

  (defthm symbol-listp-of-vl-verilog-style-flop-master-names
    (implies (symbol-listp acc)
             (symbol-listp (vl-verilog-style-flop-master-names root indices acc)))
    :hints(("Goal" :in-theory (enable vl-verilog-style-flop-master-names))))

  (defthm len-of-vl-verilog-style-flop-master-names
    (equal (len (vl-verilog-style-flop-master-names root indices acc))
           (+ (len indices)
              (len acc)))
    :hints(("Goal" :in-theory (enable vl-verilog-style-flop-master-names))))


  (defund vl-verilog-style-flop-slave-names (root indices acc)
    (declare (xargs :guard (and (stringp root)
                                (nat-listp indices))))
    (if (atom indices)
        acc
      (let* (([n]slave
              (mbe :logic
                   (cat "[" (natstr (car indices)) "]:slave")
                   :exec
                   (if (< (car indices) 256)
                       (aref1 '*vl-slave-name-array* *vl-slave-name-array* (car indices))
                     (cat "[" (natstr (car indices)) "]:slave"))))
             (root[n]slave (cat root [n]slave))
             (slave        (intern root[n]slave "ACL2"))
             (acc          (cons slave acc)))
        (vl-verilog-style-flop-slave-names root (cdr indices) acc))))

  (local (assert! (equal (vl-verilog-style-flop-slave-names "foo" (list 5 4 3) nil)
                         (list 'ACL2::|foo[3]:slave|
                               'ACL2::|foo[4]:slave|
                               'ACL2::|foo[5]:slave|))))

  (defthm symbol-listp-of-vl-verilog-style-flop-slave-names
    (implies (symbol-listp acc)
             (symbol-listp (vl-verilog-style-flop-slave-names root indices acc)))
    :hints(("Goal" :in-theory (enable vl-verilog-style-flop-slave-names))))

  (defthm len-of-vl-verilog-style-flop-slave-names
    (equal (len (vl-verilog-style-flop-slave-names root indices acc))
           (+ (len indices) (len acc)))
    :hints(("Goal" :in-theory (enable vl-verilog-style-flop-slave-names))))



  (defconst *vl-emod-master-name-array*
    ;; Array of pre-computed strings "!bit_0!S-" "!bit_1!S-" ... "!bit_255!S-"
    (compress1 '*vl-emod-master-name-array*
               (cons (list :HEADER
                           :DIMENSIONS (list 256)
                           :MAXIMUM-LENGTH 257
                           :DEFAULT 0
                           :NAME '*vl-emod-master-name-array*)
                     (vl-make-name-array "!bit_" 255 "!S-"))))

  (defconst *vl-emod-slave-name-array*
    ;; Array of pre-computed strings "!bit_0!S+" "!bit_1!S+" ... "!bit_255!S+"
    (compress1 '*vl-emod-slave-name-array*
               (cons (list :HEADER
                           :DIMENSIONS (list 256)
                           :MAXIMUM-LENGTH 257
                           :DEFAULT 0
                           :NAME '*vl-emod-slave-name-array*)
                     (vl-make-name-array "!bit_" 255 "!S+"))))

  (defund vl-emod-style-flop-master-names (root n acc)
    ;; Only for multi-bit version!
    (declare (xargs :guard (and (posp n)
                                (stringp root))))
    (if (mbe :logic (zp n) :exec nil)
        ;; Stupid termination hack
        acc
      (b* ((!bit_n-1!BIT!S-
            (mbe :logic
                 (cat "!bit_" (natstr (- n 1)) "!S-")
                 :exec
                 (if (< n 257)
                     (aref1 '*vl-emod-master-name-array* *vl-emod-master-name-array* (- n 1))
                   (cat "!bit_" (natstr (- n 1)) "!S-"))))
           (master (intern (cat root !bit_n-1!BIT!S-) "ACL2"))
           (acc    (cons master acc)))
        (if (= n 1)
            acc
          (vl-emod-style-flop-master-names root (- n 1) acc)))))

  (local (assert! (equal (vl-emod-style-flop-master-names "foo" 3 nil)
                         (list 'ACL2::|foo!bit_0!S-|
                               'ACL2::|foo!bit_1!S-|
                               'ACL2::|foo!bit_2!S-|))))

  (defthm symbol-listp-of-vl-emod-style-flop-master-names
    (implies (symbol-listp acc)
             (symbol-listp (vl-emod-style-flop-master-names root n acc)))
    :hints(("Goal" :in-theory (enable vl-emod-style-flop-master-names))))

  (defthm len-of-vl-emod-style-flop-master-names
    (equal (len (vl-emod-style-flop-master-names root n acc))
           (+ (nfix n) (len acc)))
    :hints(("Goal" :in-theory (enable vl-emod-style-flop-master-names))))


  (defund vl-emod-style-flop-slave-names (root n acc)
    ;; Only for multi-bit version!
    (declare (xargs :guard (and (posp n)
                                (stringp root))))
    (if (mbe :logic (zp n) :exec nil)
        ;; Stupid termination hack
        acc
      (b* ((!bit_n-1!BIT!S+
            (mbe :logic
                 (cat "!bit_" (natstr (- n 1)) "!S+")
                 :exec
                 (if (< n 257)
                     (aref1 '*vl-emod-slave-name-array* *vl-emod-slave-name-array* (- n 1))
                   (cat "!bit_" (natstr (- n 1)) "!S+"))))
           (slave (intern (cat root !bit_n-1!BIT!S+) "ACL2"))
           (acc   (cons slave acc)))
        (if (= n 1)
            acc
          (vl-emod-style-flop-slave-names root (- n 1) acc)))))

  (local (assert! (equal (vl-emod-style-flop-slave-names "foo" 3 nil)
                         (list 'ACL2::|foo!bit_0!S+|
                               'ACL2::|foo!bit_1!S+|
                               'ACL2::|foo!bit_2!S+|))))

  (defthm symbol-listp-of-vl-emod-style-flop-slave-names
    (implies (symbol-listp acc)
             (symbol-listp (vl-emod-style-flop-slave-names root n acc)))
    :hints(("Goal" :in-theory (enable vl-emod-style-flop-slave-names))))

  (defthm len-of-vl-emod-style-flop-slave-names
    (equal (len (vl-emod-style-flop-slave-names root n acc))
           (+ (nfix n) (len acc)))
    :hints(("Goal" :in-theory (enable vl-emod-style-flop-slave-names))))



  (defund vl-dreg-flop-emap (x enames-acc vnames-acc)
    (declare (xargs :guard (and (vl-dreg-p x)
                                (equal (vl-dreg->type x) :vl-flop))
                    :guard-debug t))
    (b* ((range    (vl-dreg->range x))

         (msb      (if (not range)
                       0
                     (vl-resolved->val (vl-range->msb range))))
         (lsb      (if (not range)
                       0
                     (vl-resolved->val (vl-range->lsb range))))

         (high         (max msb lsb))
         (low          (min msb lsb))
         (|[low:high]| (nats-from low (+ high 1)))  ;; (low, low+1, ..., high)
         (|[msb:lsb]|  (if (>= msb lsb)
                           (reverse |[low:high]|)
                         |[low:high]|))

         ;; Verilog names.
         (vroot      (vl-flatten-hidexpr (vl-dreg->hid x)))
         (vnames-acc (vl-verilog-style-flop-master-names vroot |[msb:lsb]| vnames-acc))
         (vnames-acc (vl-verilog-style-flop-slave-names vroot |[msb:lsb]| vnames-acc))

         ;; Emod names.
         (eroot    (reverse (coerce (vl-dreg-emod-root x nil) 'string)))
         (size     (+ 1 (- high low)))
         (enames-acc
          (if (= size 1)
              ;; Special case: just (!S- and !S+)
              (list* (intern (cat eroot "!S+") "ACL2")
                     (intern (cat eroot "!S-") "ACL2")
                     enames-acc)
            (let* ((enames-acc (vl-emod-style-flop-master-names eroot size enames-acc)))
              (vl-emod-style-flop-slave-names eroot size enames-acc)))))

      (mv enames-acc vnames-acc)))

  (local (defconst *test-dreg*
           (make-vl-dreg
            :hid (make-vl-nonatom
                  :op :vl-hid-dot
                  :args (list (make-vl-atom :guts (vl-hidpiece "foo"))
                              (make-vl-nonatom
                               :op :vl-hid-dot
                               :args (list (make-vl-atom :guts (vl-hidpiece "bar"))
                                           (make-vl-atom :guts (vl-hidpiece "baz"))))))
            :iname "baz_inst"
            :range (make-vl-range :msb (vl-make-index 13)
                                  :lsb (vl-make-index 10))
            :type :vl-flop)))

  (local (assert!
          (mv-let (enames vnames)
            (vl-dreg-flop-emap *test-dreg* nil nil)
            (equal (mergesort (pairlis$ enames vnames))
                   (mergesort
                    '((ACL2::|foo!bar!baz_inst!bit_3!S-| . ACL2::|foo.bar.baz[13]:master|)
                      (ACL2::|foo!bar!baz_inst!bit_2!S-| . ACL2::|foo.bar.baz[12]:master|)
                      (ACL2::|foo!bar!baz_inst!bit_1!S-| . ACL2::|foo.bar.baz[11]:master|)
                      (ACL2::|foo!bar!baz_inst!bit_0!S-| . ACL2::|foo.bar.baz[10]:master|)
                      (ACL2::|foo!bar!baz_inst!bit_3!S+| . ACL2::|foo.bar.baz[13]:slave|)
                      (ACL2::|foo!bar!baz_inst!bit_2!S+| . ACL2::|foo.bar.baz[12]:slave|)
                      (ACL2::|foo!bar!baz_inst!bit_1!S+| . ACL2::|foo.bar.baz[11]:slave|)
                      (ACL2::|foo!bar!baz_inst!bit_0!S+|
                             . ACL2::|foo.bar.baz[10]:slave|)))))))

  (local (defconst *test-dreg2*
           (make-vl-dreg
            :hid (make-vl-nonatom
                  :op :vl-hid-dot
                  :args (list (make-vl-atom :guts (vl-hidpiece "foo"))
                              (make-vl-nonatom
                               :op :vl-hid-dot
                               :args (list (make-vl-atom :guts (vl-hidpiece "bar"))
                                           (make-vl-atom :guts (vl-hidpiece "baz"))))))
            :iname "baz_inst"
            :range nil
            :type :vl-flop)))

  (local (assert!
          (mv-let (enames vnames)
            (vl-dreg-flop-emap *test-dreg2* nil nil)
            (equal (mergesort (pairlis$ enames vnames))
                   (mergesort
                    '((ACL2::|foo!bar!baz_inst!S+| . ACL2::|foo.bar.baz[0]:slave|)
                      (ACL2::|foo!bar!baz_inst!S-| . ACL2::|foo.bar.baz[0]:master|)))))))

  (defthm vl-dreg-flop-emap-basics
    (implies (and (force (vl-dreg-p x))
                  (force (equal (vl-dreg->type x) :vl-flop)))
             (let ((ret (vl-dreg-flop-emap x enames-acc vnames-acc)))
               (and (implies (symbol-listp enames-acc)
                             (symbol-listp (mv-nth 0 ret)))
                    (implies (symbol-listp vnames-acc)
                             (symbol-listp (mv-nth 1 ret))))))
    :hints(("Goal" :in-theory (enable vl-dreg-flop-emap))))

  (defthm len-of-vl-dreg-flop-emap-0
    (implies (force (vl-dreg-p x))
             (equal (len (mv-nth 0 (vl-dreg-flop-emap x enames-acc vnames-acc)))
                    (+ (* 2 (vl-maybe-range-size (vl-dreg->range x)))
                       (len enames-acc))))
    :hints(("Goal" :in-theory (enable vl-dreg-flop-emap
                                      vl-range-size
                                      vl-maybe-range-size))))

  (defthm len-of-vl-dreg-flop-emap-1
    (implies (force (vl-dreg-p x))
             (equal (len (mv-nth 1 (vl-dreg-flop-emap x enames-acc vnames-acc)))
                    (+ (* 2 (vl-maybe-range-size (vl-dreg->range x)))
                       (len vnames-acc))))
    :hints(("Goal" :in-theory (enable vl-dreg-flop-emap
                                      vl-range-size
                                      vl-maybe-range-size)))))



(defsection vl-dreg-latch-emap

; (VL-DREG-LATCH-EMAP X) is given a dreg (which must have type latch) and
; produces a mapping from EMOD state bits to Verilog-style names.
;
; The situation here is very similar to that for flops, but somewhat simpler
; since there aren't master/slave pairs of bits for each latch bit, but rather
; just a single bit.
;
; For a VL_1_BIT_LATCH, the lone state bit is called S.
;
; For larger N, VL_N_BIT_LATCH has the following state bits:
;
;  |bit_0!S|
;  |bit_1!S|
;   ...
;  |bit_{n-1}!S|
;
; Again we have a potential disconnect between the Verilog indices and the
; internal state bit indices caused by non-standard ranges like [13:10], and
; we handle this in the same way as for flops.

  (defconst *vl-verilog-latch-name-array*
    ;; Array of pre-computed strings "[0]", "[1]", ..., "[255]"
    (compress1 '*vl-verilog-latch-name-array*
               (cons (list :HEADER
                           :DIMENSIONS (list 256)
                           :MAXIMUM-LENGTH 257
                           :DEFAULT 0
                           :NAME '*vl-verilog-latch-name-array*)
                     (vl-make-name-array "[" 255 "]"))))

  (defund vl-verilog-style-latch-names (root indices acc)
    ;; In practice indices need to count down from the max index to the smallest
    ;; index for this wire.
    (declare (xargs :guard (and (stringp root)
                                (nat-listp indices))))
    (if (atom indices)
        acc
      (let* (([n]
              (mbe :logic
                   (cat "[" (natstr (car indices)) "]")
                   :exec
                   (if (< (car indices) 256)
                       (aref1 '*vl-verilog-latch-name-array* *vl-verilog-latch-name-array*
                              (car indices))
                     (cat "[" (natstr (car indices)) "]"))))
             (acc (cons (intern (cat root [n]) "ACL2") acc)))
        (vl-verilog-style-latch-names root (cdr indices) acc))))

  (local (assert! (equal (vl-verilog-style-latch-names "foo" (list 5 4 3) nil)
                         (list 'ACL2::|foo[3]|
                               'ACL2::|foo[4]|
                               'ACL2::|foo[5]|))))

  (defthm symbol-listp-of-vl-verilog-style-latch-names
    (implies (symbol-listp acc)
             (symbol-listp (vl-verilog-style-latch-names root indices acc)))
    :hints(("Goal" :in-theory (enable vl-verilog-style-latch-names))))

  (defthm len-of-vl-verilog-style-latch-names
    (equal (len (vl-verilog-style-latch-names root indices acc))
           (+ (len indices)
              (len acc)))
    :hints(("Goal" :in-theory (enable vl-verilog-style-latch-names))))



  (defconst *vl-emod-latch-name-array*
    ;; Array of pre-computed strings "!bit_0!S" "!bit_1!S" ... "!bit_255!S"
    (compress1 '*vl-emod-latch-name-array*
               (cons (list :HEADER
                           :DIMENSIONS (list 256)
                           :MAXIMUM-LENGTH 257
                           :DEFAULT 0
                           :NAME '*vl-emod-latch-name-array*)
                     (vl-make-name-array "!bit_" 255 "!S"))))

  (defund vl-emod-style-latch-names (root n acc)
    ;; Only for multi-bit version!
    (declare (xargs :guard (and (posp n)
                                (stringp root))))
    (if (mbe :logic (zp n) :exec nil)
        ;; Stupid termination hack
        acc
      (b* ((!bit_n-1!S
            (mbe :logic
                 (cat "!bit_" (natstr (- n 1)) "!S")
                 :exec
                 (if (< n 257)
                     (aref1 '*vl-emod-latch-name-array* *vl-emod-latch-name-array*
                            (- n 1))
                   (cat "!bit_" (natstr (- n 1))  "!S"))))
           (sym  (intern (cat root !bit_n-1!S) "ACL2"))
           (acc  (cons sym acc)))
        (if (= n 1)
            acc
          (vl-emod-style-latch-names root (- n 1) acc)))))

  (local (assert! (equal (vl-emod-style-latch-names "foo" 3 nil)
                         (list 'ACL2::|foo!bit_0!S|
                               'ACL2::|foo!bit_1!S|
                               'ACL2::|foo!bit_2!S|))))

  (defthm symbol-listp-of-vl-emod-style-latch-names
    (implies (symbol-listp acc)
             (symbol-listp (vl-emod-style-latch-names root n acc)))
    :hints(("Goal" :in-theory (enable vl-emod-style-latch-names))))

  (defthm len-of-vl-emod-style-latch-names
    (equal (len (vl-emod-style-latch-names root n acc))
           (+ (nfix n) (len acc)))
    :hints(("Goal" :in-theory (enable vl-emod-style-latch-names))))


  (defund vl-dreg-latch-emap (x enames-acc vnames-acc)
    (declare (xargs :guard (and (vl-dreg-p x)
                                (equal (vl-dreg->type x) :vl-latch))
                    :guard-debug t))
    (b* ((range    (vl-dreg->range x))
         (msb      (if (not range)
                       0
                     (vl-resolved->val (vl-range->msb range))))
         (lsb      (if (not range)
                       0
                     (vl-resolved->val (vl-range->lsb range))))

         (high         (max msb lsb))
         (low          (min msb lsb))
         (|[low:high]| (nats-from low (+ high 1)))
         (|[msb:lsb]|  (if (>= msb lsb)
                           (reverse |[low:high]|)
                         |[low:high]|))


         ;; Verilog names.
         (vroot      (vl-flatten-hidexpr (vl-dreg->hid x)))
         (vnames-acc (vl-verilog-style-latch-names vroot |[msb:lsb]| vnames-acc))

         ;; Emod names.
         (eroot    (reverse (coerce (vl-dreg-emod-root x nil) 'string)))
         (size     (+ 1 (- high low)))
         (enames-acc (if (= size 1)
                         ;; Special case: just !S
                         (cons (intern (cat eroot "!S") "ACL2")
                               enames-acc)
                       (vl-emod-style-latch-names eroot size enames-acc))))

      (mv enames-acc vnames-acc)))

  (local (defconst *test-dreg*
           (make-vl-dreg
            :hid (make-vl-nonatom
                  :op :vl-hid-dot
                  :args (list (make-vl-atom :guts (vl-hidpiece "foo"))
                              (make-vl-nonatom
                               :op :vl-hid-dot
                               :args (list (make-vl-atom :guts (vl-hidpiece "bar"))
                                           (make-vl-atom :guts (vl-hidpiece "baz"))))))
            :iname "baz_inst"
            :range (make-vl-range :msb (vl-make-index 13)
                                  :lsb (vl-make-index 10))
            :type :vl-latch)))

  (local (assert!
          (mv-let (enames vnames)
            (vl-dreg-latch-emap *test-dreg* nil nil)
            (equal (mergesort (pairlis$ enames vnames))
                   (mergesort
                    '((ACL2::|foo!bar!baz_inst!bit_3!S| . ACL2::|foo.bar.baz[13]|)
                      (ACL2::|foo!bar!baz_inst!bit_2!S| . ACL2::|foo.bar.baz[12]|)
                      (ACL2::|foo!bar!baz_inst!bit_1!S| . ACL2::|foo.bar.baz[11]|)
                      (ACL2::|foo!bar!baz_inst!bit_0!S| . ACL2::|foo.bar.baz[10]|)))))))

  (defthm vl-dreg-latch-emap-basics
    (implies (and (force (vl-dreg-p x))
                  (force (equal (vl-dreg->type x) :vl-latch)))
             (let ((ret (vl-dreg-latch-emap x enames-acc vnames-acc)))
               (and (implies (symbol-listp enames-acc)
                             (symbol-listp (mv-nth 0 ret)))
                    (implies (symbol-listp vnames-acc)
                             (symbol-listp (mv-nth 1 ret))))))
    :hints(("Goal" :in-theory (enable vl-dreg-latch-emap))))

  (defthm len-of-vl-dreg-latch-emap-0
    (implies (force (vl-dreg-p x))
             (equal (len (mv-nth 0 (vl-dreg-latch-emap x enames-acc vnames-acc)))
                    (+ (vl-maybe-range-size (vl-dreg->range x))
                       (len enames-acc))))
    :hints(("Goal" :in-theory (enable vl-dreg-latch-emap
                                      vl-range-size
                                      vl-maybe-range-size))))

  (defthm len-of-vl-dreg-latch-emap-1
    (implies (force (vl-dreg-p x))
             (equal (len (mv-nth 1 (vl-dreg-latch-emap x enames-acc vnames-acc)))
                    (+ (vl-maybe-range-size (vl-dreg->range x))
                       (len vnames-acc))))
    :hints(("Goal" :in-theory (enable vl-dreg-latch-emap
                                      vl-range-size
                                      vl-maybe-range-size)))))




(defsection vl-dreg-emap

  (defund vl-dreg-emap (x enames-acc vnames-acc)
    (declare (xargs :guard (vl-dreg-p x)))
    (case (vl-dreg->type x)
      (:vl-flop  (vl-dreg-flop-emap x enames-acc vnames-acc))
      (:vl-latch (vl-dreg-latch-emap x enames-acc vnames-acc))
      (otherwise
       (progn$ (er hard 'vl-dreg-emap "Impossbile")
               (mv enames-acc vnames-acc)))))

  (local (in-theory (enable vl-dreg-emap)))

  (defthm vl-dreg-emap-basics
    (implies (force (vl-dreg-p x))
             (let ((ret (vl-dreg-emap x enames-acc vnames-acc)))
               (and (implies (symbol-listp enames-acc)
                             (symbol-listp (mv-nth 0 ret)))
                    (implies (symbol-listp vnames-acc)
                             (symbol-listp (mv-nth 1 ret)))))))

  (defthm len-of-vl-dreg-emap
    (let ((ret (vl-dreg-emap x enames-acc vnames-acc)))
      (implies (and (vl-dreg-p x)
                    (equal (len enames-acc) (len vnames-acc)))
               (equal (len (mv-nth 1 ret))
                      (len (mv-nth 0 ret)))))))


(defsection vl-dreglist-emap-aux

  (defund vl-dreglist-emap-aux (x enames-acc vnames-acc)
    (declare (xargs :guard (vl-dreglist-p x)))
    (if (atom x)
        (mv enames-acc vnames-acc)
      (b* (((mv enames-acc vnames-acc)
            (vl-dreg-emap (car x) enames-acc vnames-acc)))
        (vl-dreglist-emap-aux (cdr x) enames-acc vnames-acc))))

  (local (in-theory (enable vl-dreglist-emap-aux)))

  (defthm vl-dreglist-emap-aux-basics
    (implies (force (vl-dreglist-p x))
             (let ((ret (vl-dreglist-emap-aux x enames-acc vnames-acc)))
               (and (implies (symbol-listp enames-acc)
                             (symbol-listp (mv-nth 0 ret)))
                    (implies (symbol-listp vnames-acc)
                             (symbol-listp (mv-nth 1 ret)))))))

  (defthm len-of-vl-dreglist-emap
    (let ((ret (vl-dreglist-emap-aux x enames-acc vnames-acc)))
      (implies (and (vl-dreglist-p x)
                    (equal (len enames-acc) (len vnames-acc)))
               (equal (len (mv-nth 1 ret))
                      (len (mv-nth 0 ret)))))))

(defsection vl-dreglist-emap

  ;; See above for documentation

  (local (defthm crock
           (implies (symbol-listp x)
                    (true-listp x))))

  (defund vl-dreglist-emap (x)
    "Returns (MV SUCCESSP EMAP)"
    (declare (xargs :guard (vl-dreglist-p x)))
    (b* (((mv enames vnames)
          (cwtime (vl-dreglist-emap-aux x nil nil)
                  :mintime 1/2))
         ((unless (cwtime (and (not (member 'ACL2::|| enames))
                               (not (member 'ACL2::|| vnames))
                               (not (member nil enames))
                               (not (member nil vnames))
                               (uniquep enames)
                               (uniquep vnames))
                          :mintime 1/2
                          :name vl-dreglist-emap-sanity-check))
          ;; Basic sanity check.
          (cw "Generated EMAP is invalid.")
          (mv nil nil)))
      (mv t (pairlis$ enames vnames))))

  (local (in-theory (enable vl-dreglist-emap)))

  (defthm true-listp-of-vl-dreglist-emap
    (true-listp (mv-nth 1 (vl-dreglist-emap x)))
    :rule-classes :type-prescription)

  (defthm vl-emap-p-of-vl-dreglist-emap
    (implies (force (vl-dreglist-p x))
             (vl-emap-p (mv-nth 1 (vl-dreglist-emap x)))))

  (defthm no-duplicatesp-equal-of-strip-cars-of-vl-dreglist-emap
    (implies (force (vl-dreglist-p x))
             (no-duplicatesp-equal (strip-cars (mv-nth 1 (vl-dreglist-emap x))))))

  (defthm no-duplicatesp-equal-of-strip-cdrs-of-vl-dreglist-emap
    (implies (force (vl-dreglist-p x))
             (no-duplicatesp-equal (strip-cdrs (mv-nth 1 (vl-dreglist-emap x)))))))



