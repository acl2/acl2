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

(local (xdoc::set-default-parents clean-params))

(defaggregate vl-useless-params
  :short "Records which parameters are useless for a module."
  ((names     string-listp
              "Names of the irrelevant parameters.")
   (positions integer-listp
              "Zero-indexed positions of these names in the parameter
              declaration order."))
  :tag :vl-useless-params
  :long "<p>We can apply these structures to module instances to eliminate any
useless parameters.</p>")

(defalist vl-useless-params-map-p (x)
  :key (stringp x)
  :val (vl-useless-params-p x)
  :keyp-of-nil nil
  :valp-of-nil nil
  :short "Alist mapping module names to their @(see vl-useless-params-p) entries.")

(define vl-paramvaluelist-elim-useless-params
  ((current-place natp)
   (positions     integer-listp)
   (plainargs     vl-paramvaluelist-p))
  :returns (cleaned vl-paramvaluelist-p :hyp (force (vl-paramvaluelist-p plainargs))
                    "What's left of @('plainargs') after removing the
                     irrelevant arguments.")
  :measure (len plainargs)
  (cond ((atom plainargs)
         nil)
        ((member current-place positions)
         ;; Skip it.
         (vl-paramvaluelist-elim-useless-params (+ 1 current-place)
                                                positions
                                                (cdr plainargs)))
        (t
         ;; Keep it.
         (cons (car plainargs)
               (vl-paramvaluelist-elim-useless-params (+ 1 current-place)
                                                      positions
                                                      (cdr plainargs))))))

(define vl-namedparamvaluelist-elim-useless-params
  ((names     string-listp)
   (namedargs vl-namedparamvaluelist-p))
  :returns (cleaned vl-namedparamvaluelist-p :hyp (force (vl-namedparamvaluelist-p namedargs))
                    "What's left of @('namedargs') after removing the
                     irrelevant arguments.")
  (cond ((atom namedargs)
         nil)
        ((member-equal (vl-namedparamvalue->name (car namedargs)) names)
         ;; Skip it.
         (vl-namedparamvaluelist-elim-useless-params names (cdr namedargs)))
        (t
         ;; Keep it.
         (cons (car namedargs)
               (vl-namedparamvaluelist-elim-useless-params names (cdr namedargs))))))

(define vl-paramargs-elim-useless-params
  :short "Apply a @(see vl-useless-params-p) to clean up an @(see vl-paramargs-p)
structure."
  ((useless   vl-useless-params-p)
   (arguments vl-paramargs-p))
  :returns (new-arguments vl-paramargs-p :hyp (force (vl-paramargs-p arguments)))
  (b* (((vl-useless-params useless) useless))
    (vl-paramargs-case arguments
      :vl-paramargs-named
      (change-vl-paramargs-named arguments
                                 :args (vl-namedparamvaluelist-elim-useless-params useless.names
                                                                                   arguments.args))
      :vl-paramargs-plain
      (change-vl-paramargs-plain arguments.args
                                 :args (vl-paramvaluelist-elim-useless-params 0
                                                                              useless.positions
                                                                              arguments.args)))))

(define vl-modinst-elim-useless-params ((x   vl-modinst-p)
                                        (map vl-useless-params-map-p))
  :short "Clean up a module instance, removing any useless parameters."
  :returns (new-x vl-modinst-p :hyp (force (vl-modinst-p x)))
  (b* (((vl-modinst x) x)
       ((when (vl-paramargs-empty-p x.paramargs))
        ;; Optimization.  No changes if no params.
        x)
       (entry (hons-get x.modname map))
       ((unless entry)
        x)
       (args-prime (vl-paramargs-elim-useless-params (cdr entry) x.paramargs))

;         (- (or (equal paramargs args-prime)
;                (cw "; instance of ~s0: ~s1 --> ~s2~%"
;                    modname
;                    (with-local-ps (vl-pp-arguments paramargs))
;                    (with-local-ps (vl-pp-arguments args-prime)))))
       )

    (change-vl-modinst x :paramargs args-prime)))

(defprojection vl-modinstlist-elim-useless-params (x map)
  (vl-modinst-elim-useless-params x map)
  :guard (and (vl-modinstlist-p x)
              (vl-useless-params-map-p map))
  :result-type vl-modinstlist-p)

(define vl-module-elim-useless-params
  ((x   vl-module-p)
   (map vl-useless-params-map-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (let* ((modinsts (vl-module->modinsts x))
         (modinsts (vl-modinstlist-elim-useless-params modinsts map)))
    (change-vl-module x :modinsts modinsts))
  ///
  (defthm vl-module->name-of-vl-module-elim-useless-params
    (equal (vl-module->name (vl-module-elim-useless-params x map))
           (vl-module->name x))))

(defprojection vl-modulelist-elim-useless-params (x map)
  (vl-module-elim-useless-params x map)
  :guard (and (vl-modulelist-p x)
              (vl-useless-params-map-p map))
  :result-type vl-modulelist-p)


(define vl-position-of-param
  :short "Determine the index of a useless parameter."
  ((name stringp)
   (paramdecls vl-paramdecllist-p))
  :guard (member-equal name (vl-paramdecllist->names paramdecls))
  :long "<p>We use this to construct the @(see vl-useless-params-p) structure
after identifying the names of the useless parameters.</p>"
  (cond ((atom paramdecls)
         (progn$ (impossible)
                 ;; Return zero for a nice base case.
                 0))
        ((equal name (vl-paramdecl->name (car paramdecls)))
         0)
        (t
         (+ 1 (vl-position-of-param name (cdr paramdecls))))))

(define vl-positions-of-params
  :short "Determine the indices of useless parameters."
  ((names string-listp)
   (paramdecls vl-paramdecllist-p))
  :guard (subsetp-equal names (vl-paramdecllist->names paramdecls))
  (if (atom names)
      nil
    (cons (vl-position-of-param (car names) paramdecls)
          (vl-positions-of-params (cdr names) paramdecls)))
  ///
  (defthm integer-listp-of-vl-positions-of-params
    (integer-listp (vl-positions-of-params names paramdecls))))

(define vl-module-clean-params ((x vl-module-p))
  :returns
  (mv (new-x "Updated module, with useless parameter declarations removed."
             vl-module-p :hyp :fguard)
      (useless "Structure recording which parameters were useless, if applicable."
               (equal (vl-useless-params-p useless)
                      (if useless t nil))
               :hyp :fguard))
  :short "Identify and remove useless parameters from a module."

  :long "<p>This is only one part of parameter cleaning.  To safely remove the
parameters, we must not only delete them from the module itself, but also
eliminate the appropriate parameters from all instances of the module
throughout the module list.</p>"

  :verify-guards nil

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
       ;;(- (cw "; Removing ~x0 unused parameters from ~s1: ~x2~%"
       ;;       (len useless-param-names)
       ;;       (vl-module->name x)
       ;;       (mergesort useless-param-names)))

       (useless-param-pos (vl-positions-of-params useless-param-names paramdecls))
;         (- (cw "; ~s0: eliminate ~&1 ~x2.~%"
;                (vl-module->name x) useless-param-names useless-param-pos))


       (useless-struct    (make-vl-useless-params :positions useless-param-pos
                                                  :names useless-param-names))
       (new-paramdecls    (vl-delete-paramdecls useless-param-names paramdecls))
       (x-prime           (change-vl-module x :paramdecls new-paramdecls)))

    (mv x-prime useless-struct))
  ///
  (verify-guards vl-module-clean-params
    :hints ((set-reasoning))))


(define vl-modulelist-clean-params-aux ((x vl-modulelist-p))
  :short "Eliminate param decls for useless params from each module, and build
a map that explains what has been eliminated (i.e., what needs to be cleaned
up from each module instance.)"
  :returns (mv (x-prime vl-modulelist-p :hyp :fguard)
               (map     vl-useless-params-map-p :hyp :fguard))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv car-prime car-entry)
        (vl-module-clean-params (car x)))
       ((mv cdr-prime map)
        (vl-modulelist-clean-params-aux (cdr x)))
       (map
        (if car-entry
            (hons-acons (vl-module->name (car x)) car-entry map)
          map)))
    (mv (cons car-prime cdr-prime) map)))


(define vl-modulelist-clean-params-loop ((x vl-modulelist-p)
                                         (n natp))
  :measure (nfix n)
  :returns (new-x vl-modulelist-p :hyp :fguard)
  (b* (((when (zp n))
        (cw "Warning: ran out of passes in vl-modulelist-clean-params-loop.~%")
        x)

       ((mv x-prime map)
        (vl-modulelist-clean-params-aux x))

       ((unless map)
        ;; Reached a fixed point.  Nothing more to do.  No fast-alist to free.
        x)

;         (- (cw "; Eliminated useless params from ~x0 modules: ~&1.~%"
;                (len map) (strip-cars map)))

       (x-prime (vl-modulelist-elim-useless-params x-prime map))
       (- (fast-alist-free map)))

    (vl-modulelist-clean-params-loop x-prime (- n 1))))

(define vl-modulelist-clean-params ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p :hyp :fguard)
  (vl-modulelist-clean-params-loop x 100))

(define vl-design-clean-params
  :short "Top-level @(see clean-params) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-clean-params x.mods))))

