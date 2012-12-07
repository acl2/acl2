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
(include-book "find-module")
(include-book "../transforms/xf-resolve-ranges")
(include-book "../transforms/xf-subst")
(include-book "../transforms/xf-unparameterize")
(local (include-book "../util/arithmetic"))


; sub-counts.lisp
;
; In this file we introduce a mechanism for transitively counting the number of
; submodule instances beneath a module.  The basic idea is that we want to be
; able to build a report that says how many times each kind of module occurs.
; Some possible uses include counting up how many registers are within a
; certain module, etc.
;
; This seems easy, but there are some subtle things to consider.
;
; For one, there may be good reasons to want to count before or after certain
; transforms.  For instance:
;
;   - You might want to count before occforming so that you don't see modules
;     like VL_3_BIT_AND, or maybe you want to count after occforming because
;     these numbers are interesting.
;
;   - You might want to count before unparameterization because you don't want
;     to see things like basic_reg$width=5, or maybe you want to count after
;     unparameterization because these are exactly the stats you want.
;
; We try to be flexible and do something sensible no matter what kind of
; modules we are given as inputs.  But that makes things a little tricky.  It
; is especially tricky to handle modules that still have parameters and that
; instantiate arrays of modules using those parameters.
;
; Because of this flexibility, we expect that in certain cases we could run
; into problems.  What should we do if we run into an instance of a module that
; doesn't exist?  What should we do if we run into an array of instances and we
; can't tell how wide it is?
;
; Well, my general feeling is that getting a partial count is more useful than
; getting no count at all.  So, in these hard cases I'm willing to fudge the
; answer and undercount.

(defaggregate vl-subcount
  (count warnings)
  :tag :vl-subcount
  :require ((natp-of-vl-subcount->count
             (natp count)
             :rule-classes :type-prescription)
            (vl-warninglist-p-of-vl-subcount->warnings
             (vl-warninglist-p warnings))))

(deflist vl-subcountlist-p (x)
  (vl-subcount-p x)
  :guard t
  :elementp-of-nil nil)

(defalist vl-subcountalist-p (x)
  :key (stringp x)
  :val (vl-subcount-p x)
  :keyp-of-nil nil
  :valp-of-nil nil)


(defmapappend vl-subcountlist-all-warnings (x)
  (vl-subcount->warnings x)
  :guard (vl-subcountlist-p x)
  :transform-true-list-p nil
  :rest
  ((defthm vl-warninglist-p-of-vl-subcountlist-all-warnings
     (implies (force (vl-subcountlist-p x))
              (vl-warninglist-p (vl-subcountlist-all-warnings x))))))


; Notes about how we handle modules with parameters.
;
; There are a couple of things to note.  Of course, a module can have its own
; parameters and instances can give values to some of these.  Take for
; instance:
;
;    module sub (...) ;
;      parameter size = 1;
;      ...
;       sub2 #(size + 1) foo (...);
;       sub3 foo [size-1:0] bar (...);
;    endmodule
;
;    module main (...);
;      parameter delay = 1;
;      parameter mode = 3;
;      ...
;      sub #(7) baz (...);
;    endmodule
;
; Our top-level submodule counting procedure is (vl-subcount-mod mod sigma).
; This omits certain other constant arguments like the modalist.
;
; The SIGMA it takes should give the values for some of the parameters of MOD.
; We make sure the SIGMA is honsed so memoization can hit for two different
; module instances that use the same parameters.
;
; We explicitly do NOT require that:
;
;  - The SIGMA is complete and gives a value for every parameter, or
;  - The SIGMA contains only resolved expressions for values
;
; But we do assume that the SIGMA only binds module parameters.  For instance,
; we should not see "delay" in the SIGMA for SUB, because SUB doesn't have a
; parameter named delay and it might have other wires named delay, etc.
;
; In ordinary unparameterization, we would use the sigma to rewrite the module.
; But that's considerably overkill for what we're trying to do here: The only
; things we really care about are module instance parameter lists and ranges.
;
; The function (vl-subcount-modinsts modinsts sigma) is a trivial wrapper that
; just iterates over the module instances, calling at each step the main
; function (vl-subcount-modinst modinst sigma).
;
; Here there are a couple of things to do.
;
;   1. We rewrite the parameters and range of modinst (if any) with the
;      current sigma.
;
;      For instance, if we were processing the modinsts of "sub" above, using
;      a sigma where size=7, then as a first step we'd rewrite foo and bar to:
;
;          sub2 #(6) foo (...);
;          sub3 bar [6:0] (...);
;
;      This simplification is done by just substituting in the sigma and
;      then rewrititing with vl-rangeexpr-reduce.
;
;   2. We then try to construct a new sigma to use for the submodule, e.g.,
;      we would bind foo's parameter to 6; but bar has no parameters so its
;      sigma is just NIL.
;
;   3. We then recursively process the submodule under the new sigma.
;
; If the arguments or range don't become resolved, that's fine: we just use an
; empty sigma, so uses of the affected parameters are just left alone, and we
; fudge things all the way down.



(defsection vl-merge-subcounts

; This is the main function for merging together the results we've collected.
;
; Suppose we're marching along and counting up submodule occurrences.  ANS is
; the answer we have so far, derived from the module instances we've already
; processed so far.
;
; Now suppose we've just run into an instance like this:
;
;     foo #(3, 5) my_foo [7:0] (...)
;
; We assume we've already counted up all of the submodule instances within
; module FOO under the parameter list #(3, 5).  We assume that SUB is the
; counts alist we've obtained from FOO under this parameter list.  We assume
; that SUB has already been shrunk, so we can recur over it without hitting
; shadowed pairs!
;
; The basic goal is to extend ANS with the information we've just learned from
; SUB.  This is basically straightforward: for each count entry in SUB, we look
; up the corresponding entry in ANS and increment its count by the right
; amount.
;
; The COUNT argument lets us efficiently account for instance ranges.  For
; instance, in my_foo above, COUNT would be 8.  Suppose that according to SUB,
; there are 3 occurrences of MYREG inside of FOO.  Then we really want to do
; something like ANS[MYREG].COUNT += 24 instead of ANS[MYREG].COUNT += 3.
;
; The WARNINGS argument lets us mark any entries that have been affected by
; fudging.  Basically, we'll set ANS[mod].WARNINGS @= WARNINGS for all modules
; in SUB.

  (defund vl-merge-subcounts (sub count warnings ans)
    (declare (xargs :guard (and (vl-subcountalist-p sub)
                                (natp count)
                                (vl-warninglist-p warnings)
                                (vl-subcountalist-p ans))
                    :verify-guards nil))
    (b* (((when (atom sub))
          ans)
         (name     (caar sub))
         (sub-elem (cdar sub))
         (ans-elem (or (cdr (hons-get name ans))
                       (make-vl-subcount :count 0 :warnings nil)))
         ((vl-subcount sub-elem) sub-elem)
         ((vl-subcount ans-elem) ans-elem)
         (new-count (+ (* count sub-elem.count) ans-elem.count))
         (new-warns (append-without-guard warnings
                                          sub-elem.warnings
                                          ans-elem.warnings))
         (new-elem (make-vl-subcount :count new-count
                                     :warnings new-warns))
         (ans (hons-acons name new-elem ans)))
      (vl-merge-subcounts (cdr sub) count warnings ans)))

  (local (in-theory (enable vl-merge-subcounts)))

  (defthm vl-subcountalist-p-of-vl-merge-subcounts
    (implies (and (force (vl-subcountalist-p sub))
                  (force (natp count))
                  (force (vl-warninglist-p warnings))
                  (force (vl-subcountalist-p ans)))
             (vl-subcountalist-p (vl-merge-subcounts sub count warnings ans))))

  (verify-guards vl-merge-subcounts))




(mutual-recursion

 (defun vl-subcount-mod (x sigma modalist)
   ;; Returns a slow alist with no shadowed keys
   (declare (xargs :guard (and (vl-module-p x)
                               (vl-sigma-p sigma)
                               (vl-modalist-p modalist))
                   :mode :program
                   :verify-guards nil))
   (b* (((vl-module x) x)
        ((unless (subsetp-equal (alist-keys sigma)
                                (vl-paramdecllist->names x.paramdecls)))
         (er hard? 'vl-subcount-mod "Bad sigma!"))

        (ans (vl-subcount-modinstlist x.modinsts x.name sigma modalist nil))

        ;; Stick the module itself in the subcounts, so if you ask for the
        ;; counts of some module M, it always says that M occurs once.
        ((when (hons-get x.name ans))
         ;; Probably unnecessary, if this happened we'd get into an infinite
         ;; loop before we ever checked for it.
         (er hard? 'vl-subcount-mod "Circular dependencies for ~x0?" x.name)
         ans)
        (ans (hons-acons x.name (make-vl-subcount :count 1 :warnings nil) ans))
        (ret (hons-shrink-alist ans nil)))
     (fast-alist-free ans)
     (fast-alist-free ret)
     ret))

 (defun vl-subcount-modinstlist (x within sigma modalist ans)
   ;; Do not call directly
   (declare (xargs :guard (and (vl-modinstlist-p x)
                               (stringp within)
                               (vl-sigma-p sigma)
                               (vl-modalist-p modalist)
                               (vl-subcountalist-p ans))))
   (b* (((when (atom x))
         ans)
        (ans (vl-subcount-modinst (car x) within sigma modalist ans)))
     (vl-subcount-modinstlist (cdr x) within sigma modalist ans)))

 (defun vl-subcount-modinst (x within sigma modalist ans)
   ;; Do not call directly
   (declare (xargs :guard (and (vl-modinst-p x)
                               (stringp within)
                               (vl-sigma-p sigma)
                               (vl-modalist-p modalist)
                               (vl-subcountalist-p ans))))
   (b* ((modname   (vl-modinst->modname x))
        (submod    (let ((tmp (cdr (hons-get modname modalist))))
                     (and tmp
                          (or (equal (vl-module->name tmp) modname)
                              (er hard? 'vl-subcount-modinst "Malformed modalist"))
                          tmp)))
        (range     (vl-maybe-range-subst (vl-modinst->range x) sigma))
        (paramargs (vl-arguments-subst (vl-modinst->paramargs x) sigma))

        ;; Error checking to make sure everything is okay.

        ((mv count warnings)
         (if (vl-maybe-range-resolved-p range)
             (mv (vl-maybe-range-size range) nil)
           (mv 1
               (list (make-vl-warning
                      :type :vl-subcount-fudging
                      :msg "In module ~m0, ~a1: could not determine how many ~
                      instances are in this instance array.  Fudging to say ~
                      there is just one instance.  Debugging details: ~
                      original range: ~a2.  Simplified range: ~a3.  Sigma: ~
                      ~x4."
                      :args (list within x (vl-modinst->range x) range sigma)
                      :fatalp nil
                      :fn 'vl-subcount-modinst)))))

        (warnings
         (if submod
             warnings
           (cons (make-vl-warning
                  :type :vl-subcount-fudging
                  :msg "In module ~m0, ~a1 refers to undefined module ~m2. ~
                       Fudging and assuming that ~m2 has no submodules!"
                  :args (list within x modname)
                  :fatalp nil
                  :fn 'vl-subcount-modinst)
                 warnings)))

        ((mv warnings new-sigma)
         (b* (((unless (and submod
                            (vl-good-paramdecllist-p (vl-module->paramdecls submod))))
               (mv (cons (make-vl-warning
                          :type :vl-subcount-fudging
                          :msg "In module ~m0, ~a1 refers to module ~m2, which ~
                               has unsupported parameter declarations, so we ~
                               are fudging and providing no parameter ~
                               bindings!"
                          :args (list within x modname)
                          :fatalp nil
                          :fn 'vl-subcount-modinst)
                         warnings)
                   nil))
              ;; Hack to work around the bad interface of vl-match-paramargs-with-decls
              (hacked-x (change-vl-modinst x :paramargs paramargs))
              ((mv okp warnings new-sigma)
               (vl-match-paramargs-with-decls hacked-x submod warnings))
              ((unless okp)
               (mv (cons (make-vl-warning
                          :type :vl-subcount-fudging
                          :msg "In module ~m0, ~a1 has parameter arguments ~
                               that did not unify correctly with the ~
                               parameters of ~m2, so we are fudging and ~
                               providing no parameter bindings!"
                          :args (list within x modname)
                          :fatalp nil
                          :fn 'vl-subcount-modinst)
                         warnings)
                   nil)))
           (mv warnings new-sigma)))

        (sub-counts (and submod
                         (vl-subcount-mod submod new-sigma modalist)))
        (ans (vl-merge-subcounts sub-counts count warnings ans)))
     ans)))


(local
 (defsection guard-check

; The function doesn't necessarily terminate, but we can still trick ACL2 into
; checking its guards by skipping some proofs.  We do all of this locally to
; make sure we don't introduce unsoundness.

   (skip-proofs
    (verify-termination (vl-subcount-mod
                         (declare (xargs :measure (len x))))
                        (vl-subcount-modinst
                         (declare (xargs :measure (len x))))
                        (vl-subcount-modinstlist
                         (declare (xargs :measure (len x))))))

   (skip-proofs
    (flag::make-flag flag-vl-subcount-mod
                     vl-subcount-mod
                     :flag-mapping ((vl-subcount-mod . mod)
                                    (vl-subcount-modinst . inst)
                                    (vl-subcount-modinstlist . instlist))))

   (defthm-flag-vl-subcount-mod
     (defthm vl-subcountalist-p-of-vl-subcount-mod
       (implies (and (force (vl-module-p x))
                     (force (vl-sigma-p sigma))
                     (force (vl-modalist-p modalist)))
                (vl-subcountalist-p (vl-subcount-mod x sigma modalist)))
       :flag mod)

     (defthm vl-subcountalist-p-of-vl-subcount-modinst
       (implies (and (force (vl-modinst-p x))
                     (force (stringp within))
                     (force (vl-sigma-p sigma))
                     (force (vl-modalist-p modalist))
                     (force (vl-subcountalist-p ans)))
                (vl-subcountalist-p (vl-subcount-modinst x within sigma modalist ans)))
       :flag inst)

     (defthm vl-subcountalist-p-of-vl-subcount-modinstlist
       (implies (and (force (vl-modinstlist-p x))
                     (force (stringp within))
                     (force (vl-sigma-p sigma))
                     (force (vl-modalist-p modalist))
                     (force (vl-subcountalist-p ans)))
                (vl-subcountalist-p (vl-subcount-modinstlist x within sigma modalist ans)))
       :flag instlist))

   (verify-guards vl-subcount-mod
     :guard-debug t)))

(defun invert-alist (x)
  (declare (xargs :guard t))
  (b* ((keys (alist-keys x))
       (vals (alist-vals x)))
    (pairlis$ vals keys)))

(defund vl-sort-subcounts (x)
  (declare (xargs :guard (vl-subcountalist-p x)))
  (invert-alist
   (mergesort (invert-alist x))))

(defthm vl-subcountalist-p-of-pairlis$
  (implies (and (string-listp keys)
                (vl-subcountlist-p vals)
                (equal (len keys) (len vals)))
           (vl-subcountalist-p (pairlis$ keys vals)))
  :hints(("Goal" :in-theory (enable pairlis$))))

(skip-proofs (defthm vl-subcountalist-p-of-vl-sort-subcounts
               (implies (vl-subcountalist-p x)
                        (vl-subcountalist-p (vl-sort-subcounts x)))
               :hints(("Goal" :in-theory (enable vl-sort-subcounts)))))



(defpp vl-pp-subcounts-aux (x)
  :guard (vl-subcountalist-p x)
  :body
  (b* (((when (atom x))
        ps)
       (name (caar x))
       (info (cdar x))
       ((vl-subcount info) info))
    (vl-ps-seq
     (vl-when-html (vl-print-markup "<li>"))
     (vl-print-modname name)
     (vl-print ": ")
     (vl-print info.count)
     (if (consp info.warnings)
         (vl-ps-seq
          (vl-when-html (vl-print-markup "<sup>"))
          (vl-print "*")
          (vl-when-html (vl-print-markup "</sup>")))
       ps)
     (if (vl-ps->htmlp)
         (vl-println-markup "</li>")
       (vl-println ""))
     (vl-pp-subcounts-aux (cdr x)))))

(defpp vl-pp-subcounts (x)
  :guard (vl-subcountalist-p x)
  :body
  (vl-ps-seq
   (vl-when-html (vl-println-markup "<ul>"))
   (vl-pp-subcounts-aux x)
   (vl-when-html (vl-println-markup "</ul>"))))






