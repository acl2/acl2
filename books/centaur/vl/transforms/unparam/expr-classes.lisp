; VL Verilog Toolkit
; Copyright (C) 2022 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "VL")

(include-book "centaur/vl/mlib/scopestack" :dir :system)
(include-book "centaur/fty/visitor" :Dir :system)


(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system)
                           nfix natp)))

;; TO DO:

;; - Provide some context for the classname/params produced so vl-unparam-class
;;   can make better warnings
;; - Skip collecting/replacing in places where we shouldn't.  Fundecls??


(defprod classname/params
  ((name stringp)
   (params vl-maybe-paramargs-p))
  :hons t
  :layout :fulltree)

(fty::deflist classname/paramslist :elt-type classname/params :true-listp t)


(local (include-book "centaur/meta/resolve-flag-cp" :dir :system))
(local (defun big-mutrec-default-hint
           #!acl2 (fnname id wait-til-stablep world)
           (declare (xargs :mode :program))
           ;; copied mostly from just-expand.lisp, just-expand-mrec-default-hint,
           ;; added resolve-flags-cp and do-not-induct before expanding
           #!acl2
           (and (eql 0 (acl2::access acl2::clause-id id :forcing-round))
                (equal '(1) (acl2::access acl2::clause-id id :pool-lst))
                (let* ((fns (acl2::recursivep fnname t world))
                       (flags (strip-cdrs (acl2::flag-alist fnname world)))
                       (expand-hints (just-expand-cp-parse-hints
                                      (just-expand-mrec-expanders fns world)
                                      world)))
                  `(:computed-hint-replacement
                    ('(:clause-processor (mark-expands-cp clause '(t t ,expand-hints)))
                     ;; (cmr::call-urewrite-clause-proc)
                     ;; '(:clause-processor cmr::dumb-flatten-clause-proc)
                     ;; '(:clause-processor (cmr::let-abstract-lits-clause-proc clause 'xxx))
                     (and (or (not ',wait-til-stablep) stable-under-simplificationp)
                          (expand-marked)))
                    :in-theory (disable . ,fns)
                    :do-not-induct t
                    :clause-processor (cmr::resolve-flags-cp
                                       clause
                                       ',(cons 'vl::flag flags)))))))

(local (table std::default-hints-table
              'fty::deffixequiv-mutual
              '((big-mutrec-default-hint 'fty::fnname id nil world))))



;; This visitor will collect all the (parameterized) static classes referenced by function
;; calls in this class, e.g. myclass#(
(fty::defvisitor-template expr-collect-classes ((x :object) (ss vl-scopestack-p))
  :returns (classname/params (:join (append-without-guard classname/params1 classname/params)
                              :initial nil
                              :tmp-var classname/params1)
                             classname/paramslist-p)
  :renames ((vl-expr vl-expr-collect-classes-aux))
  :type-fns ((vl-expr vl-expr-collect-classes))
  :prod-fns (;; these all need different scopes
             (vl-genloop (continue :skip)
                         (nextval :skip)
                         (body :skip))
             (vl-genif   (then :skip)
                         (else :skip))
             (vl-gencase (default :skip))
             (vl-genblock (elems :skip))
             (vl-genarray (blocks :skip))
             (vl-gencaselist (:val :skip)))
  :fnname-template <type>-collect-classes)


(define vl-scopename-is-regular-name ((x vl-scopename-p))
  :enabled t
  :Guard-hints (("goal" :in-theory (enable vl-scopename-p)))
  (mbe :logic (stringp (vl-scopename-fix x))
       :exec (and (not (eq x :vl-local))
                  (not (eq x :vl-$unit)))))

(define vl-classname-p ((x stringp) (ss vl-scopestack-p))
  (b* ((def (vl-scopestack-find-definition x ss)))
    (and def (eq (tag def) :vl-class))))



(local (defthm len-of-cons
         (equal (len (cons x y))
                (+ 1 (len y)))))

(local (in-theory (disable classname/paramslist-p-when-subsetp-equal
                           acl2::true-listp-append
                           append
                           len not o-p
                           (:t append)
                           (:t append-without-guard))))

(fty::defvisitor-multi vl-expr-collect-classes
  :defines-args (:flag-hints ((big-mutrec-default-hint 'vl-expr-collect-classes id nil world))
                 :returns-hints ((big-mutrec-default-hint 'vl-expr-collect-classes id nil world)))


  (fty::defvisitor :template expr-collect-classes
    :type expressions-and-datatypes
    :measure (acl2::nat-list-measure (list :count 0)))


  (define vl-expr-collect-classes ((x vl-expr-p)
                                   (ss vl-scopestack-p))
    :measure (acl2::nat-list-measure (list (vl-expr-count x) 10))
    :returns (classname/params classname/paramslist-p)
    (b* ((rest (vl-expr-collect-classes-aux x ss)))
    (vl-expr-case x
      :vl-call (vl-scopeexpr-case x.name
                 :colon (b* (((unless (and (vl-scopename-is-regular-name x.name.first)
                                           (vl-classname-p x.name.first ss)))
                              rest))
                          (cons (make-classname/params :name x.name.first :params x.name.paramargs)
                                rest))
                 :otherwise rest)
      :otherwise rest))))

(set-bogus-measure-ok t)
(local (defthm o-p-when-natp
         (implies (natp x) (o-p x))
         :hints(("Goal" :in-theory (enable o-p)))))

(fty::defvisitors vl-genblob-collect-classes
  :template expr-collect-classes
  :types (vl-genblob))




(fty::defmap classname/params-unparam-map :key-type classname/params-p :val-type stringp :true-listp t)


;; This visitor will replace the (parameterized) static classes with the names
;; of the unparameterized classes to be generated, given by the alist.
(fty::defvisitor-template expr-replace-classes ((x :object)
                                                (map classname/params-unparam-map-p)
                                                (ss vl-scopestack-p))
  :returns (mv (changedp (:join (or changedp1 changedp)
                          :initial nil
                          :tmp-var changedp1))
               (new-x (:update (if changedp :update (:fix x)))))
  :renames ((vl-expr vl-expr-replace-classes-aux))
  :type-fns ((vl-expr vl-expr-replace-classes))
  :prod-fns (;; these all need different scopes
             (vl-genloop (continue :skip)
                         (nextval :skip)
                         (body :skip))
             (vl-genif   (then :skip)
                         (else :skip))
             (vl-gencase (default :skip))
             (vl-genblock (elems :skip))
             (vl-genarray (blocks :skip))
             (vl-gencaselist (:val :skip)))
  :fnname-template <type>-replace-classes)


(local (defthm vl-scopeexpr-count-of-change
         (implies (vl-scopeexpr-case x :colon)
                  (<= (vl-scopeexpr-count
                       (change-vl-scopeexpr-colon
                        x
                        :first new-first
                        :paramargs nil))
                      (vl-scopeexpr-count x)))
         :hints(("Goal" :in-theory (enable vl-scopeexpr-count)
                 :expand ((Vl-scopeexpr-count x))))
         :rule-classes (:rewrite :linear)))

(local (defthm vl-expr-count-of-change-call-fnname
         (implies (and (vl-expr-case x :vl-call)
                       (<= (vl-scopeexpr-count new-name) (vl-scopeexpr-count (vl-call->name x))))
                  (<= (vl-expr-count (change-vl-call x :name new-name
                                                     :atts (vl-expr->atts x)))
                      (vl-expr-count x)))
         :hints(("Goal" :in-theory (enable vl-expr-count)
                 :expand ((vl-expr-count x))))
         :rule-classes :linear))


(fty::defvisitor-multi vl-expr-replace-classes
  :defines-args (:flag-hints ((big-mutrec-default-hint 'vl-expr-replace-classes id nil world))
                 :returns-hints ((big-mutrec-default-hint 'vl-expr-replace-classes id nil world)))


  (fty::defvisitor :template expr-replace-classes
    :type expressions-and-datatypes
    :measure (acl2::nat-list-measure (list :count 0)))


  (define vl-expr-replace-classes ((x vl-expr-p)
                                   (map classname/params-unparam-map-p)
                                   (ss vl-scopestack-p))
    :measure (acl2::nat-list-measure (list (vl-expr-count x) 10))
    :returns (mv changedp (new-x vl-expr-p))
    (vl-expr-case x
      :vl-call (vl-scopeexpr-case x.name
                 :colon (b* (((unless (and (vl-scopename-is-regular-name x.name.first)
                                           (vl-classname-p x.name.first ss)))
                              (vl-expr-replace-classes-aux x map ss))
                             (key (make-classname/params :name x.name.first :params x.name.paramargs))
                             (new-name (cdr (hons-get key (classname/params-unparam-map-fix map))))
                             ((unless new-name)
                              (vl-expr-replace-classes-aux x map ss))
                             ((mv ?changedp new-x)
                              (vl-expr-replace-classes-aux
                               (change-vl-call x :name (change-vl-scopeexpr-colon x.name
                                                                                  :first new-name
                                                                                  :paramargs nil))
                               map ss)))
                          (mv t new-x))
                 :otherwise (vl-expr-replace-classes-aux x map ss))
      :otherwise (vl-expr-replace-classes-aux x map ss))))

(fty::defvisitors vl-genblob-replace-classes
  :template expr-replace-classes
  :types (vl-genblob))
