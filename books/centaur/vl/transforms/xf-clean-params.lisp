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
(include-book "../mlib/allexprs")
(include-book "../mlib/modnamespace")
(include-book "../mlib/filter")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))



(defxdoc clean-params
  :parents (transforms)
  :short "Eliminate unused parameters from modules."
  :long "<p>Parameter-cleaning is an optional transformation which is intended
to reduce the number of modules introduced by unparameterization.</p>

<p>We find that many frequently-instantiated, low-level modules often have
parameters that are not actually used in the RTL model.  For instance, a module
might have a size or delay parameter that does not affect its RTL-level
semantics.</p>

<p>Unfortunately, every time the module is instantiated with, say, a different
delay, @(see unparameterization) will produce a new instance of it that is
specialized for that particular delay.  This can lead us to make a lot of
copies of identical modules, with different names.  And, each of these modules
then has to go through the rest of the transformation process, which can be
slow.</p>

<p>So, our idea in this transformation is to cut out irrelevant parameters
before unparameterization is invoked.</p>")


(defaggregate vl-useless-params
  (positions names)
  :tag :vl-useless-params
  :require ((integer-listp-of-vl-useless-params->positions (integer-listp positions))
            (string-listp-of-vl-useless-params->names      (string-listp names)))
  :parents (clean-params)
  :short "Records of which parameters are useless."
  :long "<p>The @('names') are the names of any irrelevant parameters and the
@('positions') are their zero-indexed positions in the parameter declaration
order.  We apply these structures to module instances to eliminate any useless
parameters.</p>")


(defsection vl-useless-params-map-p
  :parents (clean-params)
  :short "Alist mapping module names to their @(see vl-useless-params-p) entries."

;; BOZO use defalist instead?

  (defund vl-useless-params-map-p (x)
    (declare (xargs :guard t))
    (if (consp x)
        (and (consp (car x))
             (stringp (caar x))
             (vl-useless-params-p (cdar x))
             (vl-useless-params-map-p (cdr x)))
      (eq x nil)))

  (local (in-theory (enable vl-useless-params-map-p)))

  (defthm vl-useless-params-map-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-useless-params-map-p x)
                    (not x))))

  (defthm vl-useless-params-map-p-of-cons
    (equal (vl-useless-params-map-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (vl-useless-params-p (cdr a))
                (vl-useless-params-map-p x))))

  (defthm vl-useless-params-p-of-hons-assoc-equal
    (implies (force (vl-useless-params-map-p x))
             (equal (vl-useless-params-p (cdr (hons-assoc-equal a x)))
                    (if (hons-assoc-equal a x)
                        t
                      nil)))))



(defsection vl-plainarglist-elim-useless-params

  (defund vl-plainarglist-elim-useless-params (current-place positions plainargs)
    (declare (xargs :guard (and (natp current-place)
                                (integer-listp positions)
                                (true-listp positions)
                                (vl-plainarglist-p plainargs))
                    :measure (acl2-count plainargs)))
    (cond ((atom plainargs)
           nil)
          ((member current-place positions)
           ;; Skip it.
           (vl-plainarglist-elim-useless-params (+ 1 current-place)
                                               positions
                                               (cdr plainargs)))
          (t
           ;; Keep it.
           (cons (car plainargs)
                 (vl-plainarglist-elim-useless-params (+ 1 current-place)
                                                     positions
                                                     (cdr plainargs))))))

  (local (in-theory (enable vl-plainarglist-elim-useless-params)))

  (defthm vl-plainarglist-p-of-vl-plainarglist-elim-useless-params
    (implies (force (vl-plainarglist-p plainargs))
             (vl-plainarglist-p
              (vl-plainarglist-elim-useless-params current-place positions plainargs)))))


(defsection vl-namedarglist-elim-useless-params

  (defund vl-namedarglist-elim-useless-params (names namedargs)
    (declare (xargs :guard (and (string-listp names)
                                (vl-namedarglist-p namedargs))))
    (cond ((atom namedargs)
           nil)
          ((member-equal (vl-namedarg->name (car namedargs)) names)
           ;; Skip it.
           (vl-namedarglist-elim-useless-params names (cdr namedargs)))
          (t
           ;; Keep it.
           (cons (car namedargs)
                 (vl-namedarglist-elim-useless-params names (cdr namedargs))))))

  (local (in-theory (enable vl-namedarglist-elim-useless-params)))

  (defthm vl-namedarglist-p-of-vl-namedarglist-elim-useless-params
    (implies (force (vl-namedarglist-p namedargs))
             (vl-namedarglist-p (vl-namedarglist-elim-useless-params names namedargs)))))


(defsection vl-arguments-elim-useless-params
  :parents (clean-params)
  :short "Apply a @(see vl-useless-params-p) to clean up an @(see vl-arguments-p)
structure."

  :long "<p>@(call vl-arguments-elim-useless-params) returns a new arguments
structure where any useless arguments are removed.</p>"

  (local (defthm true-listp-when-integer-listp
           (implies (integer-listp x)
                    (true-listp x))))

  (defund vl-arguments-elim-useless-params (useless arguments)
    (declare (xargs :guard (and (vl-useless-params-p useless)
                                (vl-arguments-p arguments))))
    (if (vl-arguments->namedp arguments)
        (vl-arguments t
                      (vl-namedarglist-elim-useless-params (vl-useless-params->names useless)
                                                           (vl-arguments->args arguments)))
      (vl-arguments nil
                    (vl-plainarglist-elim-useless-params 0
                                                         (vl-useless-params->positions useless)
                                                         (vl-arguments->args arguments)))))

  (local (in-theory (enable vl-arguments-elim-useless-params)))

  (defthm vl-arguments-p-of-vl-arguments-elim-useless-params
    (implies (force (vl-arguments-p arguments))
             (vl-arguments-p (vl-arguments-elim-useless-params useless arguments)))))




(defsection vl-modinst-elim-useless-params

  (defund vl-modinst-elim-useless-params (x map)
    (declare (xargs :guard (and (vl-modinst-p x)
                                (vl-useless-params-map-p map))))
    (b* ((paramargs (vl-modinst->paramargs x))
         ((unless (vl-arguments->args paramargs))
          ;; Optimization.  No changes if no params.
          x)
         (modname   (vl-modinst->modname x))
         (entry     (hons-get modname map))
         ((unless entry)
          x)
         (args-prime (vl-arguments-elim-useless-params (cdr entry) paramargs))

;         (- (or (equal paramargs args-prime)
;                (cw "; instance of ~s0: ~s1 --> ~s2~%"
;                    modname
;                    (with-local-ps (vl-pp-arguments paramargs))
;                    (with-local-ps (vl-pp-arguments args-prime)))))
         )

        (change-vl-modinst x :paramargs args-prime)))

  (local (in-theory (enable vl-modinst-elim-useless-params)))

  (defthm vl-modinst-p-of-vl-modinst-elim-useless-params
    (implies (force (vl-modinst-p x))
             (vl-modinst-p (vl-modinst-elim-useless-params x map)))))


(defsection vl-modinstlist-elim-useless-params

  (defprojection vl-modinstlist-elim-useless-params (x map)
    (vl-modinst-elim-useless-params x map)
    :guard (and (vl-modinstlist-p x)
                (vl-useless-params-map-p map)))

  (defthm vl-modinstlist-p-of-vl-modinstlist-elim-useless-params
    (implies (force (vl-modinstlist-p x))
             (vl-modinstlist-p (vl-modinstlist-elim-useless-params x map)))
    :hints(("Goal" :induct (len x)))))


(defsection vl-module-elim-useless-params

  (defund vl-module-elim-useless-params (x map)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-useless-params-map-p map))))
    (let* ((modinsts (vl-module->modinsts x))
           (modinsts (vl-modinstlist-elim-useless-params modinsts map)))
      (change-vl-module x :modinsts modinsts)))

  (local (in-theory (enable vl-module-elim-useless-params)))

  (defthm vl-module-p-of-vl-module-elim-useless-params
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-elim-useless-params x map))))

  (defthm vl-module->name-of-vl-module-elim-useless-params
    (equal (vl-module->name (vl-module-elim-useless-params x map))
           (vl-module->name x))))


(defsection vl-modulelist-elim-useless-params

  (defprojection vl-modulelist-elim-useless-params (x map)
    (vl-module-elim-useless-params x map)
    :guard (and (vl-modulelist-p x)
                (vl-useless-params-map-p map)))

  (local (in-theory (enable vl-modulelist-elim-useless-params)))

  (defthm vl-modulelist-p-of-vl-modulelist-elim-useless-params
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-elim-useless-params x map))))

  (defthm vl-modulelist->names-of-vl-modulelist-elim-useless-params
    (equal (vl-modulelist->names (vl-modulelist-elim-useless-params x map))
           (vl-modulelist->names x))))



(defsection vl-positions-of-params
  :parents (clean-params)
  :short "Compute a zero-indexed list of parameter positions."

  :long "<p>We use this to construct the @(see vl-useless-params-p) structure
after identifying the names of the useless parameters.</p>"

  (defund vl-position-of-param (name paramdecls)
    (declare (xargs :guard (and (stringp name)
                                (vl-paramdecllist-p paramdecls)
                                (member-equal name (vl-paramdecllist->names paramdecls)))))
    (cond ((atom paramdecls)
           (prog2$ (er hard 'vl-position-of-param "Provably impossible.")
                   ;; Return zero for a nice base case.
                   0))
          ((equal name (vl-paramdecl->name (car paramdecls)))
           0)
          (t
           (+ 1 (vl-position-of-param name (cdr paramdecls))))))

  (defund vl-positions-of-params (names paramdecls)
    (declare (xargs :guard (and (string-listp names)
                                (vl-paramdecllist-p paramdecls)
                                (subsetp-equal names (vl-paramdecllist->names paramdecls)))))
    (if (atom names)
        nil
      (cons (vl-position-of-param (car names) paramdecls)
            (vl-positions-of-params (cdr names) paramdecls))))

  (defthm integer-listp-of-vl-positions-of-params
    (integer-listp (vl-positions-of-params names paramdecls))
    :hints(("Goal" :in-theory (enable vl-positions-of-params)))))




(defsection vl-module-clean-params
  :parents (clean-params)
  :short "Identify and remove useless parameters from a module."
  :long "<p><b>Signature:</b> @(call vl-module-clean-params) returns @('(mv
x-prime useless)').</p>

<p>Here, @('x-prime') is the updated module, and @('useless') is either
@('nil') to indicate that no parameters are useless, or is a @(see
vl-useless-params-p) structure that indicates the names and positions of any
useless parameters that have been eliminated.</p>

<p>This is only one part of parameter cleaning.  To safely remove the
parameters, we must not only delete them from the module itself, but also
eliminate the appropriate parameters from all instances of the module
throughout the module list.</p>"

  (defund vl-module-clean-params (x)
    "Returns (mv x-prime useless/nil)"
    (declare (xargs :guard (vl-module-p x)
                    :verify-guards nil))
    (b* (((when (vl-module->hands-offp x))
          (mv x nil))

         (paramdecls (vl-module->paramdecls x))
         ((when (not paramdecls))
          ;; Optimization.  Nothing to do for param-free modules.
          (mv x nil))

         ;; Now, see which params are unused.
         (param-names      (vl-paramdecllist->names paramdecls))
         (all-used-names   (vl-exprlist-names (vl-module-allexprs x)))

         (useful-param-names
          ;; This looks expensive but isn't.  Although the set of
          ;; all-used-names might be very large (say 1000 names), the set of
          ;; param-names is generally very small (say 3 names).  So, you can
          ;; basically think of the member-equal call as being effectively
          ;; constant-time.  Hence, this is nearly linear, and should be better
          ;; than mergesorting first and using set intersect.
          (intersection-equal all-used-names param-names))

         (useless-param-names
          (set-difference-equal param-names useful-param-names))

         ((unless useless-param-names)
          (mv x nil))
         (- (cw "; Removing ~x0 unused parameters from ~s1: ~x2~%"
                (len useless-param-names)
                (vl-module->name x)
                (mergesort useless-param-names)))

         (useless-param-pos (vl-positions-of-params useless-param-names paramdecls))
;         (- (cw "; ~s0: eliminate ~&1 ~x2.~%"
;                (vl-module->name x) useless-param-names useless-param-pos))


         (useless-struct    (make-vl-useless-params :positions useless-param-pos
                                                    :names useless-param-names))
         (new-paramdecls    (vl-delete-paramdecls useless-param-names paramdecls))
         (x-prime           (change-vl-module x :paramdecls new-paramdecls)))

      (mv x-prime useless-struct)))

  (verify-guards vl-module-clean-params
    :hints ((set-reasoning)))

  (local (in-theory (enable vl-module-clean-params)))

  (defthm vl-module-p-of-vl-module-clean-params
    (implies (force (vl-module-p x))
             (vl-module-p (mv-nth 0 (vl-module-clean-params x)))))

  (defthm vl-module->name-of-vl-module-clean-params
    (equal (vl-module->name (mv-nth 0 (vl-module-clean-params x)))
           (vl-module->name x)))

  (defthm vl-useless-params-p-of-vl-module-clean-params
    (implies (force (vl-module-p x))
             (iff (vl-useless-params-p (mv-nth 1 (vl-module-clean-params x)))
                  (mv-nth 1 (vl-module-clean-params x))))))


(defsection vl-modulelist-clean-params-aux

  (defund vl-modulelist-clean-params-aux (x)
    "Returns (MV X-PRIME USELESS-MAP)"
    (declare (xargs :guard (vl-modulelist-p x)))

; Eliminate param decls for useless params from each module, and build a map
; that explains what has been eliminated.

    (if (atom x)
        (mv nil nil)
      (b* (((mv car-prime car-entry)
            (vl-module-clean-params (car x)))
           ((mv cdr-prime map)
            (vl-modulelist-clean-params-aux (cdr x)))
           (map
            (if car-entry
                (hons-acons (vl-module->name (car x)) car-entry map)
              map)))
          (mv (cons car-prime cdr-prime) map))))

  (local (in-theory (enable vl-modulelist-clean-params-aux)))

  (defthm vl-modulelist-p-of-vl-modulelist-clean-params-aux
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 0 (vl-modulelist-clean-params-aux x)))))

  (defthm vl-modulelist->names-of-vl-modulelist-clean-params-aux
    (equal (vl-modulelist->names (mv-nth 0 (vl-modulelist-clean-params-aux x)))
           (vl-modulelist->names x)))

  (defthm vl-useless-params-map-p-of-vl-modulelist-clean-params-aux
    (implies (force (vl-modulelist-p x))
             (vl-useless-params-map-p (mv-nth 1 (vl-modulelist-clean-params-aux x))))))



(defsection vl-modulelist-clean-params-loop

  (local (defthm alistp-when-vl-useless-params-map-p
           (implies (vl-useless-params-map-p x)
                    (alistp x))
           :hints(("Goal" :induct (len x)))))

  (defund vl-modulelist-clean-params-loop (x n)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (natp n))
                    :measure (nfix n)))

    (b* (((when (zp n))
          (prog2$
           (cw "Warning: ran out of passes in vl-modulelist-clean-params-loop.~%")
           x))

         ((mv x-prime map)
          (vl-modulelist-clean-params-aux x))

         ((unless map)
          ;; Reached a fixed point.  Nothing more to do.  No fast-alist to free.
          x)

;         (- (cw "; Eliminated useless params from ~x0 modules: ~&1.~%"
;                (len map) (strip-cars map)))

         (x-prime (vl-modulelist-elim-useless-params x-prime map))
         (- (flush-hons-get-hash-table-link map)))

        (vl-modulelist-clean-params-loop x-prime (- n 1))))

  (local (in-theory (enable vl-modulelist-clean-params-loop)))

  (defthm vl-modulelist-p-of-vl-modulelist-clean-params-loop
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-clean-params-loop x n))))

  (defthm vl-modulelist->names-of-vl-modulelist-clean-params-loop
    (equal (vl-modulelist->names (vl-modulelist-clean-params-loop x n))
           (vl-modulelist->names x))))


(defsection vl-modulelist-clean-params

  (defund vl-modulelist-clean-params (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (vl-modulelist-clean-params-loop x 100))

  (local (in-theory (enable vl-modulelist-clean-params)))

  (defthm vl-modulelist-p-of-vl-modulelist-clean-params
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-clean-params x))))

  (defthm vl-modulelist->names-of-vl-modulelist-clean-params
    (equal (vl-modulelist->names (vl-modulelist-clean-params x))
           (vl-modulelist->names x))))

