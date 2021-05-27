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
(include-book "../svex/vars")
(include-book "std/osets/top" :dir :system)
(include-book "std/util/defprojection" :dir :System)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/osets/under-set-equiv" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defxdoc name
  :parents (svmods)
  :short "Type of the names of wires, module instances, and namespaces (such as
          datatype fields).")

(define name-p (x)
  :parents (name)
  (or (stringp x)    ;; normal wire/instance/field names
      (integerp x)   ;; array indices
      (eq x :self)   ;; special name for a datatype's self wire -- see vl-datatype->mods
      (and (consp x)
           (eq (car x) :anonymous))))

(define name-fix ((x name-p))
  :parents (name)
  :returns (xx name-p)
  :hooks nil
  (mbe :logic (if (name-p x) x '(:anonymous))
       :exec x)
  ///
  (defthm name-fix-when-name-p
    (implies (name-p x)
             (equal (name-fix x) x))))

(defsection name-equiv
  :parents (name)
  (fty::deffixtype name
    :pred name-p
    :fix name-fix
    :equiv name-equiv
    :define t
    :forward t))


(fty::defflexsum path
  :parents (svmods)
  :short "Type of a path to a wire in svex modules, expressed relative to the local scope."
  ;; :prepwork ((local (defthm car-of-name-fix
  ;;                     (implies (consp (name-fix x))
  ;;                              (equal (car (name-fix x)) :anonymous))
  ;;                     :hints(("Goal" :in-theory (enable name-fix name-p)))))
  ;;            (local (defthm car-when-name-p
  ;;                     (implies (and (name-p x)
  ;;                                   (consp x))
  ;;                              (equal (car x) :anonymous))
  ;;                     :hints(("Goal" :in-theory (enable name-p)))
  ;;                     :rule-classes :forward-chaining)))
  ;; :enable-rules (car-when-name-p)
  :prepwork ((local (defthm not-name-p-when-name-p-car
                      (implies (name-p x)
                               (not (name-p (cons x y))))
                      :hints(("Goal" :in-theory (enable name-p))))))
  (:wire :cond (or (atom x)
                   (name-p x)) ;; bozo
   :short "Path to a wire in the local scope"
   :fields ((name :type name :acc-body x))
   :ctor-body name)
  (:scope
   :short "Path into a subscope, e.g., @('a.b.c')"
   :fields ((subpath :type path :acc-body (cdr x)
                     :doc "The rest of the path inside the subscope, e.g. @('b.c')")
            (namespace :type name :acc-body (car x)
                       :doc "The name of the subscope, e.g. @('a')"))
   :ctor-body (cons namespace subpath)))


(define path-append ((x path-p) (y path-p))
  :parents (path)
  :returns (new-path path-p)
  :measure (path-count x)
  :verify-guards nil
  (path-case x
    :wire (make-path-scope :subpath y :namespace x.name)
    :scope (make-path-scope :subpath (path-append x.subpath y) :namespace x.namespace))
  ///
  (verify-guards path-append))


(defxdoc addr-scope
  :parents (address)
  :short "Scope for an @(see address-p).")

(define addr-scope-p (x)
  :parents (addr-scope)
  (or (natp x)
      (eq x :root))
  ///
  (defthm addr-scope-possibilities
    (implies (addr-scope-p x)
             (or (equal x :root)
                 (natp x)))
    :rule-classes :forward-chaining)

  (defthm addr-scope-p-when-natp
    (implies (natp x)
             (addr-scope-p x))))

(define addr-scope-fix ((x addr-scope-p))
  :parents (addr-scope)
  :returns (xx addr-scope-p)
  :hooks nil
  (mbe :logic (if (eq x :root) x (nfix x))
       :exec x)
  ///
  (defthm addr-scope-fix-when-addr-scope-p
    (implies (addr-scope-p x)
             (equal (addr-scope-fix x) x))))

(defsection addr-scope-equiv
  :parents (addr-scope)
  (fty::deffixtype addr-scope
    :pred addr-scope-p
    :fix addr-scope-fix
    :equiv addr-scope-equiv
    :define t
    :forward t))



;; (fty::defprod address
;;   :short "Convention for referring to wires in expressions and lvalues."
;;   ((path path-p)
;;    (index maybe-nat :rule-classes :type-prescription)
;;    (scope addr-scope-p)
;;    (delay integerp :rule-classes :type-prescription))
;;   ///
;;   (defthm type-of-address->scope
;;     (or (equal (address->scope x) :root)
;;         (natp (address->scope x)))
;;     :hints (("goal" :use ((:instance addr-scope-possibilities
;;                            (x (address->scope x))))))
;;     :rule-classes ((:forward-chaining :trigger-terms ((address->scope x))))))


(fty::defflexsum address
  :parents (svmods)
  :short "Convention for referring to wires in expressions and lvalues."
  :long "<p>This is a product type containing a path, scope qualifier, and
index.  The scope qualifier is either a natural number (indicating that
the path is relative to the Nth scope up from the local context) or @(':root'),
indicating the path is relative to the global scope.  The formulation of the
product is a bit complicated because we want to allow a path by itself to be an
address with empty index and scope qualifier 0.</p>"

  :kind nil
  (:address
   ;; layout: either just a path, or (:address path index delay scope).
   :shape (b* (((when (or (atom x)
                          (not (eq (car X) :address))))
                (path-p x)))
            (and (eq (car x) :address)
                 (true-listp x)
                 (eql (len x) 4)
                 (not (and (eq (nth 2 x) nil)
                           (equal (nth 3 x) 0)))))
   :fields ((path :type path :acc-body (if (or (atom x)
                                               (not (eq (car x) :address)))
                                           x
                                         (nth 1 x)))
            (index :type maybe-natp :acc-body (if (or (atom x)
                                                      (not (eq (car x) :address)))
                                                  nil
                                                (nth 2 x))
                   :rule-classes (:rewrite :type-prescription))
            (scope :type addr-scope :acc-body (if (or (atom x)
                                                      (not (eq (car x) :address)))
                                                  0
                                                (nth 3 x))
                   :default 0))
   :ctor-body (if (and (eql scope 0)
                       (eq index nil))
                  path
                (list :address path index scope))
   :type-name address)
  :prepwork ((local (defthm car-when-path-p
                      (implies (path-p x)
                               (not (equal (car x) :address)))
                      :hints(("Goal" :in-theory (enable path-p name-p)))))
             (local (in-theory (disable (:t addr-scope-fix)
                                        (:t path-fix)
                                        (:t acl2::maybe-natp-fix)
                                        (:t acl2::maybe-natp-of-maybe-natp-fix)
                                        (:t path-p)
                                        (:t addr-scope-p)
                                        (:t maybe-natp)
                                        acl2::maybe-natp-when-natp
                                        default-car default-cdr
                                        not))))
  ///
  (defthm type-of-address->scope
    (or (equal (address->scope x) :root)
        (natp (address->scope x)))
    :hints (("goal" :use ((:instance addr-scope-possibilities
                           (x (address->scope x))))))
    :rule-classes ((:forward-chaining :trigger-terms ((address->scope x))))))


(local (xdoc::set-default-parents address))

(define address->svar ((x address-p))
  :short "Turn an address into a variable name."
  :returns (xvar svar-p)
  (make-svar :name (address-fix x)))

(define svar-addr-p ((x svar-p))
  :short "An svar containing an address."
  (b* (((svar x)))
    (and (address-p x.name)
         (not x.override-test)
         (not x.override-val)))
  ///
  (defthm svar-addr-p-of-address->svar
    (svar-addr-p (address->svar x))
    :hints(("Goal" :in-theory (enable address->svar svar-p)))))

(define svar->address ((x svar-p))
  :guard (svar-addr-p x)
  :guard-hints (("goal" :in-theory (enable svar-addr-p)))
  :returns (address (address-p address))
  (address-fix (svar->name x))
  ///
  (local (defthm var-not-car-of-address
           (implies (address-p x)
                    (not (equal (car x) :var)))
           :hints(("Goal" :in-theory (enable address-p path-p name-p)))))
  (defthm svar->address-of-address->svar
    (equal (svar->address (address->svar x))
           (address-fix x))
    :hints(("Goal" :in-theory (enable address->svar svar-p)))))

(define svar-addr-fix ((x svar-p))
  :guard (svar-addr-p x)
  :returns (x (and (svar-p x)
                   (svar-addr-p x))
              :hints(("Goal" :in-theory (enable svar-addr-p))))
  (mbe :logic (if (svar-addr-p x)
                  (svar-fix x)
                (change-svar x :name (svar->address x)
                             :override-test nil
                             :override-val nil))
       :exec x)
  ///
  (defthm svar-addr-fix-when-svar-addr-p
    (implies (svar-addr-p x)
             (equal (svar-addr-fix x)
                    (Svar-fix x)))
    :hints(("Goal" :in-theory (enable svar->address))))

  (defthm svar->address-of-svar-addr-fix
    (equal (svar->address (svar-addr-fix x))
           (svar->address x))
    :hints(("Goal" :in-theory (enable svar->address)))))


(encapsulate nil
  (local (include-book "std/osets/element-list" :dir :system))
  (local (include-book "std/lists/sets" :dir :system))
  (std::deflist svarlist-addr-p (x)
    :guard (svarlist-p x)
    (svar-addr-p x)
    ///
    (deffixequiv svarlist-addr-p :args ((x svarlist)))))


(define svarlist-addr-p-badguy ((x svarlist-p))
  :returns (badguy (iff (svar-p badguy) badguy)
                   :hints (("goaL" :induct t)
                           (and stable-under-simplificationp
                                '(:in-theory (enable svar-p)))))
  (if (atom x)
      (make-svar :name :not-an-address)
    (if (svar-addr-p (car x))
        (svarlist-addr-p-badguy (cdr x))
      (svar-fix (car x))))
  ///
  (defthm svarlist-addr-p-badguy-not-addr-p
    (not (svar-addr-p (svarlist-addr-p-badguy x)))
    :hints (("goal" :induct t)))


  (defthm svarlist-addr-p-by-badguy
    (implies (not (member (svarlist-addr-p-badguy x) (svarlist-fix x)))
             (svarlist-addr-p x))
    :hints (("goal" :induct (svarlist-fix x)
             :expand ((svarlist-addr-p x)
                      (svarlist-addr-p-badguy x)
                      (svarlist-fix x))
             :in-theory (enable (:i svarlist-fix)))))

  (defthm svarlist-addr-p-badguy-not-member-when-addr-p
    (implies (and (svarlist-addr-p x)
                  (svarlist-p x))
             (not (member (svarlist-addr-p-badguy y) x))))

  (defthm svarlist-addr-p-badguy-not-equal-svar-addr
    (implies (svar-addr-p y)
             (not (equal (svarlist-addr-p-badguy x) y)))
    :hints (("goal" :use svarlist-addr-p-badguy-not-addr-p
             :in-theory (disable svarlist-addr-p-badguy-not-addr-p
                                 svarlist-addr-p-badguy)))))


(define svar-add-delay ((x svar-p) (delay natp))
  :returns (xx (and (svar-p xx)
                    (implies (svar-addr-p x)
                             (svar-addr-p xx)))
               :hints(("Goal" :in-theory (enable svar-addr-p))))
  (change-svar x :delay (+ (lnfix delay) (svar->delay x)))
  ///
  (defthm svar-add-delay-when-zero
    (equal (svar-add-delay x 0) (svar-fix x))))

(std::defprojection svarlist-add-delay ((x svarlist-p) (delay natp))
  :returns (xx (and (svarlist-p xx)
                    (implies (svarlist-addr-p x)
                             (svarlist-addr-p xx))))
  (svar-add-delay x delay)
  ///
  (defthm svarlist-add-delay-when-0
    (equal (svarlist-add-delay x 0)
           (svarlist-fix x))))

(defines svex-add-delay
  (define svex-add-delay ((x svex-p) (delay natp))
    :verify-guards nil
    :measure (svex-count x)
    :returns (xx (and (svex-p xx)
                     (implies (svarlist-addr-p (svex-vars x))
                              (svarlist-addr-p (svex-vars xx)))))
    (svex-case x
      :var (make-svex-var :name (svar-add-delay x.name delay))
      :quote (svex-fix x)
      :call (make-svex-call :fn x.fn
                            :args (svexlist-add-delay x.args delay))))
  (define svexlist-add-delay ((x svexlist-p) (delay natp))
    :measure (svexlist-count x)
    :returns (xx (and (svexlist-p xx)
                      (implies (svarlist-addr-p (svexlist-vars x))
                               (svarlist-addr-p (svexlist-vars xx)))))

    (if (atom x)
        nil
      (cons (svex-add-delay (car x) delay)
            (svexlist-add-delay (cdr x) delay))))
  ///
  (verify-guards svex-add-delay
    :hints (("goal" :expand ((svex-vars x)
                             (svexlist-vars x)
                             (:free (a b) (svexlist-vars (cons a b)))))))

  (deffixequiv-mutual svex-add-delay)

  (defthm len-of-svexlist-add-delay
    (equal (len (svexlist-add-delay x delay))
           (len x))
    :hints (("Goal" :induct (len x)
             :expand ((svexlist-add-delay x delay)))))

  ;; probably actually equal rather than set-equiv
  (defthm-svex-add-delay-flag
    (defthm svex-vars-of-svex-add-delay
      (set-equiv (svex-vars (svex-add-delay x delay))
                 (svarlist-add-delay (svex-vars x) delay))
      :flag svex-add-delay)
    (defthm svexlist-vars-of-svexlist-add-delay
      (set-equiv (svexlist-vars (svexlist-add-delay x delay))
                 (svarlist-add-delay (svexlist-vars x) delay))
      :hints('(:in-theory (enable svexlist-vars))
             (and stable-under-simplificationp
                  '(:in-theory (enable))))
      :flag svexlist-add-delay))

  (defthm-svex-add-delay-flag
    (defthm svex-add-delay-when-0
      (equal (svex-add-delay x 0)
             (svex-fix x))
      :flag svex-add-delay)
    (defthm svexlist-add-delay-when-0
      (equal (svexlist-add-delay x 0)
             (svexlist-fix x))
      :flag svexlist-add-delay))

  (memoize 'svex-add-delay :condition '(eq (svex-kind x) :call)))

(define svex-add-delay-top ((x svex-p)
                            (delay natp))
  :enabled t
  :hooks nil
  (mbe :logic (svex-add-delay x delay)
       :exec (if (zp delay)
                 x
               (svex-add-delay x delay))))


(define svex-alist-add-delay ((x svex-alist-p) (delay natp))
  :prepwork ((local (Defthm svex-alist-p-of-pairlis
                      (implies (and (svarlist-p keys)
                                    (svexlist-p vals)
                                    (Equal (len keys) (len vals)))
                               (svex-alist-p (pairlis$ keys vals)))))
             (local (defthm svex-alist-vars-of-pairlis$
                      (implies (and (equal (len keys) (len vals))
                                    (svarlist-p keys))
                               (set-equiv (svex-alist-vars (pairlis$ keys vals))
                                          (svexlist-vars vals)))
                      :hints(("Goal" :in-theory (enable svex-alist-vars
                                                        pairlis$
                                                        svexlist-vars)))))
             (local (defthm svexlist-vars-of-svex-alist-vals
                      (equal (svexlist-vars (svex-alist-vals x))
                             (svex-alist-vars x))
                      :hints(("Goal" :in-theory (enable svex-alist-vars svexlist-vars
                                                        svex-alist-vals)))))
             (local (defthm svex-lookup-of-pairlis$
                      (iff (svex-lookup v (pairlis$ x y))
                           (member (svar-fix v) x))
                      :hints(("Goal" :in-theory (enable svex-lookup svarlist-fix
                                                        pairlis$))))))
  :returns (new-x svex-alist-p)
  (b* ((ans (pairlis$ (svex-alist-keys x)
                      (svexlist-add-delay (svex-alist-vals x) delay))))
    (clear-memoize-table 'svex-add-delay)
    ans)
  ///
  (more-returns
   (new-x :name keys-of-svex-alist-add-delay
          (iff (svex-lookup v new-x)
               (svex-lookup v x)))

   (new-x :name vars-of-svex-alist-add-delay
          (implies (svarlist-addr-p (svex-alist-vars x))
                   (svarlist-addr-p (svex-alist-vars new-x))))))


(define make-simple-svar ((name name-p))
  :returns (var (and (svar-p var)
                     (svar-addr-p var)))
  (sv::address->svar (make-address :path (make-path-wire :name name))))

(define make-scoped-svar ((scope name-p)
                          (name name-p))
  :short "Make an svar for a name under a single scope level, e.g. foo.bar"
  :returns (var (and (svar-p var)
                     (svar-addr-p var)))
  (sv::address->svar (make-address :path (make-path-scope :namespace scope :subpath (make-path-wire :name name)))))
