; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "lhs")
(include-book "centaur/misc/dag-measure" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "std/util/defenum" :dir :system)
(local (include-book "std/strings/eqv" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defxdoc svmods
  :parents (sv)
  :short "An svex-based format for expressing a module hierarchy."
  :long "<p>See the subtopics for a description of the format.  The top-level
description of a design is a @(see design) object.</p>")

(local (xdoc::set-default-parents svmods))

(defines svex-addr-p
  :verify-guards nil
  :flag nil
  (define svex-addr-p ((x svex-p))
    :measure (svex-count x)
    :enabled t
    (mbe :logic (svarlist-addr-p (svex-vars x))
         :exec (svex-case x
                 :var (svar-addr-p x.name)
                 :quote t
                 :call (svexlist-addr-p x.args))))
  (define svexlist-addr-p ((x svexlist-p))
    :measure (svexlist-count x)
    :enabled t
    (mbe :logic (svarlist-addr-p (svexlist-vars x))
         :exec (if (atom x)
                   t
                 (and (svex-addr-p (car x))
                      (svexlist-addr-p (cdr x))))))
  ///
  (verify-guards svex-addr-p)

  (memoize 'svex-addr-p :condition '(eq (svex-kind x) :call)))


(define lhatom-addr-p ((x lhatom-p))
  :verify-guards nil
  :enabled t
  (mbe :logic (svarlist-addr-p (lhatom-vars x))
       :exec (lhatom-case x
               :z t
               :var (svar-addr-p x.name)))
  ///
  (verify-guards lhatom-addr-p
    :hints(("Goal" :in-theory (enable lhatom-vars)))))

(define lhs-addr-p ((x lhs-p))
  :verify-guards nil
  :enabled t
  (mbe :logic (svarlist-addr-p (lhs-vars x))
       :exec  (if (atom x)
                  t
                (and (lhatom-addr-p (lhrange->atom (car x)))
                     (lhs-addr-p (cdr x)))))
  ///
  (verify-guards lhs-addr-p
    :hints(("Goal" :in-theory (enable lhs-vars)))))


(define assigns-addr-p ((x assigns-p))
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (len (assigns-fix x))
  :verify-guards nil
  :enabled t
  (mbe :logic (svarlist-addr-p (assigns-vars x))
       :exec  (b* ((x (assigns-fix x))
                   ((when (atom x)) t))
                (and (lhs-addr-p (caar x))
                     (svex-addr-p (driver->value (cdar x)))
                     (assigns-addr-p (cdr x)))))
  ///
  (verify-guards assigns-addr-p
    :hints(("Goal" :in-theory (enable assigns-vars)))))

(define lhspairs-addr-p ((x lhspairs-p))
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (len (lhspairs-fix x))
  :verify-guards nil
  :enabled t
  (mbe :logic (svarlist-addr-p (lhspairs-vars x))
       :exec  (b* ((x (lhspairs-fix x))
                   ((when (atom x)) t))
                (and (lhs-addr-p (caar x))
                     (lhs-addr-p (cdar x))
                     (lhspairs-addr-p (cdr x)))))
  ///
  (verify-guards lhspairs-addr-p
    :hints(("Goal" :in-theory (enable lhspairs-vars)))))

(define svar-map-addr-p ((x svar-map-p))
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (len (svar-map-fix x))
  :verify-guards nil
  :enabled t
  (mbe :logic (svarlist-addr-p (svar-map-vars x))
       :exec  (b* ((x (svar-map-fix x))
                   ((when (atom x)) t))
                (and (svar-addr-p (caar x))
                     (svar-addr-p (cdar x))
                     (svar-map-addr-p (cdr x)))))
  ///
  (verify-guards svar-map-addr-p
    :hints(("Goal" :in-theory (enable svar-map-vars)))))

(define svex-alist-addr-p ((x svex-alist-p))
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (len (svex-alist-fix x))
  :verify-guards nil
  :enabled t
  (mbe :logic (and (svarlist-addr-p (svex-alist-vars x))
                   (svarlist-addr-p (svex-alist-keys x)))
       :exec  (b* ((x (svex-alist-fix x))
                   ((when (atom x)) t))
                (and (svar-addr-p (caar x))
                     (svex-addr-p (cdar x))
                     (svex-alist-addr-p (cdr x)))))
  ///
  (verify-guards svex-alist-addr-p
    :hints(("Goal" :in-theory (enable svex-alist-vars
                                      svex-alist-keys)))))







(define svar-add-namespace ((namespace name-p) (x svar-p))
  :short "Add a namespace to a variable so that it can be referenced from a lower
          hierarchy level."
  :long "<p>If the scope modifier of the address is @(':root'), then we don't
add the namespace.  If the scope modifier is positive, we decrement it instead
of adding the namespace.</p>"
  :guard (svar-addr-p x)
  :guard-hints (("goal" :in-theory (enable svar-addr-p)))
  :returns (x (and (svar-p x) (svar-addr-p x))
              :hints(("Goal" :in-theory (enable svar-addr-p))))
  (b* (((svar x))
       ((address x.name))
       ((when (eq x.name.scope :root))
        (mbe :logic (change-svar x :name (change-address x.name)
                                 :override-test nil :override-val nil)
             :exec x))
       (new-addr (if (eql 0 x.name.scope)
                     (change-address
                      x.name :path (make-path-scope :namespace namespace
                                                    :subpath x.name.path))
                   (change-address x.name :scope (1- x.name.scope)))))
    (change-svar x :name new-addr :override-test nil :override-val nil)))
(defines svex-add-namespace
  (define svex-add-namespace ((namespace name-p) (x svex-p))
    :verify-guards nil
    :guard (svarlist-addr-p (svex-vars x))
    :measure (svex-count x)
    :returns (x (and (svex-p x)
                     (svarlist-addr-p (svex-vars x))))
    (svex-case x
      :var (make-svex-var :name (svar-add-namespace namespace x.name))
      :quote (svex-fix x)
      :call (make-svex-call :fn x.fn
                            :args (svexlist-add-namespace namespace x.args))))
  (define svexlist-add-namespace ((namespace name-p) (x svexlist-p))
    :guard (svarlist-addr-p (svexlist-vars x))
    :measure (svexlist-count x)
    :returns (x (and (svexlist-p x)
                     (svarlist-addr-p (svexlist-vars x))))
    (if (atom x)
        nil
      (cons (svex-add-namespace namespace (car x))
            (svexlist-add-namespace namespace (cdr x)))))
  ///
  (verify-guards svex-add-namespace
    :hints (("goal" :expand ((svex-vars x)
                             (svexlist-vars x)
                             (:free (a b) (svexlist-vars (cons a b))))))))

(define lhs-add-namespace ((namespace name-p) (x lhs-p))
  :guard (svarlist-addr-p (lhs-vars x))
  :returns (xx (and (lhs-p xx)
                    (svarlist-addr-p (lhs-vars xx))))
  :prepwork ((local (in-theory (enable lhatom-vars))))
  (b* (((when (atom x)) nil)
       ((lhrange first) (lhrange-fix (car x))))
    (cons (lhatom-case first.atom
            :z first
            :var (change-lhrange
                  first
                  :atom
                  (change-lhatom-var
                   first.atom
                   :name (svar-add-namespace namespace first.atom.name))))
          (lhs-add-namespace namespace (cdr x)))))


;; (fty::defflexsum hid
;;   (:base :cond (atom x)
;;    :fields ((name :type stringp :acc-body x))
;;    :ctor-body name)
;;   (:index :cond (integerp (car x))
;;    :fields ((sub :type hid :acc-body (cdr x))
;;             (index :type integerp :acc-body (car x)))
;;    :ctor-body (cons index sub))
;;   (:dot
;;    :fields ((sub :type hid :acc-body (cdr x))
;;             (field :type stringp :acc-body (car x)))
;;    :ctor-body (cons field sub)))

;; (define hid->svar ((x hid-p))
;;   :returns (svar svar-p
;;                  :hints(("Goal" :in-theory (enable svar-p))))
;;   (let ((x (hid-fix x)))
;;     (if (stringp x) x (cons :var x))))

;; (define hid-add-namespace ((namespace hid-p) (x hid-p))
;;   :returns (newx hid-p)
;;   :measure (hid-count x)
;;   :verify-guards nil
;;   (hid-case x
;;     :base (make-hid-dot :sub namespace
;;                         :field x.name)
;;     :dot (make-hid-dot :sub (hid-add-namespace namespace x.sub)
;;                        :field x.field)
;;     :index (make-hid-index :sub (hid-add-namespace namespace x.sub)
;;                            :index x.index))
;;   ///
;;   (verify-guards hid-add-namespace))


(define path-add-namespace ((namespace name-p) (x path-p))
  :enabled t :inline t
  (make-path-scope :namespace namespace :subpath x))



(defenum wiretype
  (nil ;; :wire
   :supply0
   :supply1
   :wand
   :wor
   :tri0
   :tri1
   :trireg)
  :parents (wire))

(fty::defalist attributes :key-type stringp :val-type maybe-svex :true-listp t)


(fty::defprod wire
  :short "Wire info as stored in an svex module."
  ((name name-p)
   (width posp :rule-classes :type-prescription
          "The declared width of the wire")
   (low-idx integerp :rule-classes :type-prescription
            "The declared lower index of the wire's range.  This may be the MSB
             or the LSB (depending on revp), or both if the wire is only 1
             bit.")
   (delay acl2::maybe-posp :rule-classes :type-prescription)
   (revp    "If true, the range was declared as [low:high] rather than [high:low],
             so the low-idx is the MSB rather than the LSB.")
   (type wiretype)
   (atts attributes))
  :layout :tree)

(fty::deflist wirelist
  :elt-type wire
  :true-listp t
  :parents (wire))

(fty::deflist namelist
  :elt-type name
  :true-listp t
  :parents (name))


(defprojection wirelist->names ((x wirelist-p))
  (wire->name x)
  :returns (names namelist-p)
  :parents (wirelist)
  ///
  (deffixequiv wirelist->names :args ((x wirelist))))

(define wirelist-find ((name name-p) (x wirelist-p))
  :parents (wirelist)
  :short "@(call wirelist-find) searches for a @(see name) in a @(see wirelist)."
  :returns (wire (iff (wire-p wire) wire))
  (cond ((atom x)
         nil)
        ((equal (wire->name (car x)) (name-fix name))
         (wire-fix (car x)))
        (t
         (wirelist-find name (cdr x)))))

;; (defprojection wirelist-from-strings (x)
;;   (wire x )
;;   :guard (stringlist-p x))

;; (defthm wirelist-p-of-wirelist-from-strings
;;   (wirelist-p (wirelist-from-strings x))
;;   :hints(("Goal" :in-theory (enable wirelist-from-strings))))



(defxdoc modname
  :short "A type for names of modules and other hierarchical scopes.")

(define modname-p (x)
  :parents (modname)
  (declare (ignorable x))
  (not (eq x nil))
  ///
  (defthm modname-p-booleanp
    (booleanp (modname-p x))
    :rule-classes :type-prescription)
  (defthm modname-p-compound-recognizer
    (implies (modname-p x) x)
    :rule-classes :compound-recognizer)
  (in-theory (disable (:t modname-p))))

(define modname-fix ((x modname-p))
  :parents (modname)
  :returns (x-fix modname-p)
  :hooks nil
  (mbe :logic (if (modname-p x) x "default-modname")
       :exec x)
  ///
  (defthm modname-fix-when-modname-p
    (implies (modname-p x)
             (equal (modname-fix x) x))))

(defsection modname-equiv
  :parents (modname)
  (fty::deffixtype modname
    :pred modname-p
    :fix modname-fix
    :equiv modname-equiv
    :define t
    :forward t))

(fty::deflist modnamelist
  :elt-type modname
  :true-listp t
  :elementp-of-nil nil
  :parents (modname))


(fty::defprod modinst
  :layout :tree
  ((instname name-p)
   (modname modname-p))
  :parents (svmods))

(fty::deflist modinstlist
  :elt-type modinst
  :true-listp t
  :parents (modinst))

(defprojection modinstlist->modnames ((x modinstlist-p))
  (modinst->modname x)
  :returns (names modnamelist-p)
  :parents (modinstlist))

(defprojection modinstlist->instnames ((x modinstlist-p))
  (modinst->instname x)
  :returns (names namelist-p)
  :parents (modinstlist))

(define constraintlist-addr-p ((x constraintlist-p))
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (len (constraintlist-fix x))
  :verify-guards nil
  :enabled t
  (mbe :logic (svarlist-addr-p (constraintlist-vars x))
       :exec  (b* (((when (atom x)) t))
                (and (svex-addr-p (constraint->cond (car x)))
                     (constraintlist-addr-p (cdr x)))))
  ///
  (verify-guards constraintlist-addr-p
    :hints(("Goal" :in-theory (enable constraintlist-vars)))))



(fty::defprod module
  ((wires      wirelist)
   (insts      modinstlist)
   (assigns    assigns)
   (fixups     assigns)
   (constraints constraintlist)
   ;; (delays svar-map)
   (aliaspairs lhspairs)))

(define module-vars ((x module-p))
  :parents (module)
  :returns (vars svarlist-p)
  (b* (((module x)))
    (append (assigns-vars x.assigns)
            (constraintlist-vars x.constraints)
            (assigns-vars x.fixups)
            ;; (svar-map-vars x.delays)
            (lhspairs-vars x.aliaspairs)))
  ///
  (defthm vars-of-module->assigns
    (implies (not (member v (module-vars x)))
             (not (member v (assigns-vars (module->assigns x)))))
    :hints(("Goal" :in-theory (enable module-vars))))

  (defthm vars-of-module->constraints
    (implies (not (member v (module-vars x)))
             (not (member v (constraintlist-vars (module->constraints x)))))
    :hints(("Goal" :in-theory (enable module-vars))))

  (defthm vars-of-module->fixups
    (implies (not (member v (module-vars x)))
             (not (member v (assigns-vars (module->fixups x)))))
    :hints(("Goal" :in-theory (enable module-vars))))

  ;; (defthm vars-of-module->delays
  ;;   (implies (not (member v (module-vars x)))
  ;;            (not (member v (svar-map-vars (module->delays x)))))
  ;;   :hints(("Goal" :in-theory (enable module-vars))))

  (defthm vars-of-module->aliaspairs
    (implies (not (member v (module-vars x)))
             (not (member v (lhspairs-vars (module->aliaspairs x)))))
    :hints(("Goal" :in-theory (enable module-vars))))

  (defthm vars-of-module
    (implies (and (not (member v (lhspairs-vars aliases)))
                  (not (member v (assigns-vars assigns)))
                  (not (member v (constraintlist-vars constraints)))
                  (not (member v (assigns-vars fixups)))
                  ;; (not (member v (svar-map-vars delays)))
                  )
             (not (member v (module-vars
                             (module wires insts assigns fixups constraints aliases)))))
    :hints(("Goal" :in-theory (enable module-vars)))))

(define module-addr-p ((x module-p))
  :parents (module)
  :enabled t
  :verify-guards nil
  (mbe :logic (svarlist-addr-p (module-vars x))
       :exec (b* (((module x)))
               (and (assigns-addr-p x.assigns)
                    (assigns-addr-p x.fixups)
                    (constraintlist-addr-p x.constraints)
                    (lhspairs-addr-p x.aliaspairs))))
  ///
  (verify-guards module-addr-p
    :hints(("Goal" :in-theory (e/d (module-vars)
                                   (acl2::member-equal-append
                                    sv::svarlist-addr-p-by-badguy))))))


(fty::defmap modalist
  :key-type modname
  :val-type module
  ///
  (defcong modalist-equiv modalist-equiv (append a b) 1)
  (defcong modalist-equiv modalist-equiv (append a b) 2))

(define modalist-lookup (modname (modalist modalist-p))
  :parents (modalist)
  :returns (mod (iff (module-p mod) mod)
                :hints(("Goal" :in-theory (enable modalist-fix))))
  (cdr (hons-get modname
                 (mbe :logic (modalist-fix modalist) :exec modalist)))
  ///
  (fty::deffixequiv modalist-lookup))

(define modalist->modnames ((modalist modalist-p))
  :parents (modalist)
  :returns (modnames modnamelist-p
                     :hints(("Goal" :in-theory (enable alist-keys modalist-fix))))
  (alist-keys (mbe :logic (modalist-fix modalist) :exec modalist))
  ///
  (defthm member-modalist->modnames
    (iff (member x (modalist->modnames modalist))
         (modalist-lookup x modalist))
    :hints(("Goal" :in-theory (enable modalist-lookup modalist-fix alist-keys)
            :induct (len modalist)))))

(define modname->submodnames (x (modalist modalist-p))
  :returns (modnames modnamelist-p)
  (b* ((mod (modalist-lookup x modalist))
       ((unless mod) nil))
    (modinstlist->modnames (module->insts mod)))
  ///
  (defthm modname->submodnames-implies-lookup
    (implies (modname->submodnames x modalist)
             (modalist-lookup x modalist))))

(define modalist-vars ((x modalist-p))
  :parents (modalist)
  :returns (vars svarlist-p)
  :measure (len (modalist-fix x))
  (b* ((x (modalist-fix x)))
    (if (atom x)
        nil
      (append (module-vars (cdar x))
              (modalist-vars (cdr x)))))
  ///
  (defthm modalist-vars-of-append
    (equal (modalist-vars (append a b))
           (append (modalist-vars a)
                   (modalist-vars b)))
    :hints (("goal" :induct (modalist-vars a)
             :in-theory (enable modalist-fix)
             :expand ((:free (a b) (modalist-vars (cons a b)))
                      (append a b))))))

(define modalist-addr-p ((x modalist-p))
  :parents (modalist)
  :enabled t
  :verify-guards nil
  (mbe :logic (svarlist-addr-p (modalist-vars x))
       :exec (b* ((x (modalist-fix x)))
               (if (atom x)
                   t
                 (and (module-addr-p (cdar x))
                      (modalist-addr-p (cdr x))))))
  ///
  (verify-guards modalist-addr-p
    :hints(("Goal" :in-theory (enable modalist-vars)))))

(acl2::def-dag-measure modhier
  :graph-formals (modalist)
  :successors-expr (modname->submodnames x modalist)
  :nodes-expr (modalist->modnames modalist)
  :guard (modalist-p modalist))


(defthm modhier-loopfreelist-p-of-cons
  (implies (modhier-loopfreelist-p (cons a b) modalist)
           (and (modhier-loopfree-p a modalist)
                (modhier-loopfreelist-p b modalist)))
  :hints (("goal" :use ((:instance modhier-loopfree-p-of-car
                         (x (cons a b)))
                        (:instance modhier-loopfreelist-p-of-cdr
                         (x (cons a b))))))
  :rule-classes :forward-chaining)

(defthm modhier-loopfreelist-p-of-lookup-modnames
  (implies (and (modhier-loopfree-p x modalist)
                (modalist-lookup x modalist))
           (modhier-loopfreelist-p
            (modinstlist->modnames (module->insts (modalist-lookup x modalist)))
            modalist))
  :hints (("goal" :use ((:instance modhier-loopfreelist-p-of-successors))
           :in-theory (enable modname->submodnames))))

(defines mod-meas
  (define mod-meas (modname
                    (modalist modalist-p))
    :guard (modhier-loopfree-p modname modalist)
    :returns (count natp :rule-classes :type-prescription)
    :measure (nat-list-measure
              (list (modhier-count modname
                                   (modalist-fix modalist)) 0 0))
    :hints (("goal" :expand ((modhier-count modname (modalist-fix modalist)))
             :in-theory (enable modname->submodnames)))
    :verify-guards nil
    (b* ((modalist (mbe :logic (modalist-fix modalist) :exec modalist))
         (mod (modalist-lookup modname modalist))
         ((unless (and mod
                       (mbt (modhier-loopfree-p modname modalist))))
          0))
      (+ 1 (modinstlist-meas (module->insts mod) modalist))))

  (define modinstlist-meas ((modinsts modinstlist-p)
                             (modalist modalist-p))
    :guard (modhier-loopfreelist-p (modinstlist->modnames modinsts) modalist)
    :returns (count natp :rule-classes :type-prescription)
    :measure (nat-list-measure
              (list (modhier-count-list
                     (modinstlist->modnames modinsts)
                     (modalist-fix modalist))
                    (len modinsts) 2))
    (if (atom modinsts)
        1
      (+ 1
         (modinst-meas (car modinsts) modalist)
         (modinstlist-meas (cdr modinsts) modalist))))

  (define modinst-meas ((inst modinst-p) (modalist modalist-p))
    :guard (modhier-loopfree-p (modinst->modname inst) modalist)
    :returns (count natp :rule-classes :type-prescription)
    :measure (nat-list-measure
              (list (modhier-count (modinst->modname inst)
                                   (modalist-fix modalist))
                    0 1))
    (+ 1 (mod-meas (modinst->modname inst) modalist)))
  ///

  (verify-guards mod-meas)

  (fty::deffixequiv-mutual mod-meas)

  (defthm modinstlist-meas-of-insts-of-lookup
    (implies (and (modalist-lookup x modalist)
                  (modhier-loopfree-p x (modalist-fix modalist)))
             (< (modinstlist-meas (module->insts (modalist-lookup x modalist)) modalist)
                (mod-meas x modalist)))
    :rule-classes :linear)

  (defthm mod-meas-of-modinst
    (< (mod-meas (modinst->modname x) modalist)
       (modinst-meas x modalist))
    :rule-classes :linear)

  (defthm modinst-meas-of-car
    (implies (consp x)
             (< (modinst-meas (car x) modalist)
                (modinstlist-meas x modalist)))
    :rule-classes :linear)

  (defthm modinst-meas-of-cdr
    (implies (consp x)
             (< (modinstlist-meas (cdr x) modalist)
                (modinstlist-meas x modalist)))
    :rule-classes :linear)

  (defthm modinst-meas-of-cdr-weak
    (<= (modinstlist-meas (cdr x) modalist)
        (modinstlist-meas x modalist))
    :rule-classes :linear))



(defines mod-wirecount
  (define mod-wirecount (modname
                         (modalist modalist-p))
    :guard (modhier-loopfree-p modname modalist)
    :returns (count natp :rule-classes :type-prescription)
    :measure (mod-meas modname modalist)
    :verify-guards nil
    (b* ((modalist (mbe :logic (modalist-fix modalist) :exec modalist))
         (mod (modalist-lookup modname modalist))
         ((unless (and mod
                       (mbt (modhier-loopfree-p modname modalist))))
          0)
         (selfcount (len (module->wires mod))))
      (+ selfcount (modinstlist-wirecount (module->insts mod) modalist))))

  (define modinstlist-wirecount ((modinsts modinstlist-p)
                                 (modalist modalist-p))
    :guard (modhier-loopfreelist-p (modinstlist->modnames modinsts) modalist)
    :returns (count natp :rule-classes :type-prescription)
    :measure (modinstlist-meas modinsts modalist)
    (if (atom modinsts)
        0
      (+ (mod-wirecount (modinst->modname (car modinsts)) modalist)
         (modinstlist-wirecount (cdr modinsts) modalist))))
  ///

  (verify-guards mod-wirecount)

  (fty::deffixequiv-mutual mod-wirecount)

  (memoize 'mod-wirecount))


(defines mod-instcount
  (define mod-instcount (modname
                         (modalist modalist-p))
    :guard (modhier-loopfree-p modname modalist)
    :returns (count natp :rule-classes :type-prescription)
    :measure (mod-meas modname modalist)
    :verify-guards nil
    (b* ((modalist (mbe :logic (modalist-fix modalist) :exec modalist))
         (mod (modalist-lookup modname modalist))
         ((unless (and mod
                       (mbt (modhier-loopfree-p modname modalist))))
          0))
      (modinstlist-instcount (module->insts mod) modalist)))

  (define modinstlist-instcount ((modinsts modinstlist-p)
                                 (modalist modalist-p))
    :guard (modhier-loopfreelist-p (modinstlist->modnames modinsts) modalist)
    :returns (count natp :rule-classes :type-prescription)
    :measure (modinstlist-meas modinsts modalist)
    (if (atom modinsts)
        0
      (+ 1
         (mod-instcount (modinst->modname (car modinsts)) modalist)
         (modinstlist-instcount (cdr modinsts) modalist))))
  ///

  (verify-guards mod-instcount)

  (fty::deffixequiv-mutual mod-instcount)

  (memoize 'mod-instcount))

(defprod design
  ((modalist modalist-p)
   (top      modname-p)))
