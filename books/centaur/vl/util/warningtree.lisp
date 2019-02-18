; VL Verilog Toolkit
; Copyright (C) 2019 Centaur Technology
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
; Original author (this file): Sol Swords <sswords@centtech.com>

(in-package "VL")

(include-book "warnings")
(local (in-theory (disable (tau-system))))
(local (std::add-default-post-define-hook :fix))

(local (defthm car-when-vl-warning-p
         (implies (vl-warning-p x)
                  (equal (car x) :vl-warning))
         :hints(("Goal" :in-theory (enable vl-warning-p)))))

;; (define atom-fix ((x atom))
;;   :returns (new-x atom :rule-classes :type-prescription)
;;   (mbe :logic (and (atom x) X)
;;        :exec x)
;;   ///
;;   (defthm atom-fix-when-atom
;;     (implies (atom x)
;;              (equal (atom-fix x) x)))

;;   (fty::deffixtype atom :pred atom :fix atom-fix :equiv atom-equiv :define t))

(fty::defflexsum vl-warningtree
  (:null
   :cond (atom x)
   :shape (eq x nil)
   :fields nil
   :ctor-body nil)
  (:warning
   :cond (eq (car x) :vl-warning)
   :fields ((warning :acc-body x :type vl-warning
                     :acc-name vl-warningtree->warning))
   :ctor-body warning)
  (:context
   :cond (eq (car x) :vl-warningtree-context)
   :shape (consp (cdr x))
   :fields ((context :acc-body (cadr x)
                     :acc-name vl-warningtree->context)
            (subtree :acc-body (cddr x) :type vl-warningtree
                     :acc-name vl-warningtree->subtree))
   :ctor-body (cons :vl-warningtree-context
                    (cons context subtree)))
   
  (:pair
   :fields ((left :acc-body (car x) :type vl-warningtree
                  :acc-name vl-warningtree->left)
            (right :acc-body (cdr x) :type vl-warningtree
                   :acc-name vl-warningtree->right))
   :ctor-body (cons left right))
  
  :post-pred-events ((defthm vl-warningtree-p-when-vl-warning-p
                       (implies (vl-warning-p x)
                                (vl-warningtree-p x))
                       :hints (("goal" :expand ((vl-warningtree-p x))))))
  ///
  (defthm vl-warningtree-p-when-vl-warninglist-p
    (implies (and (vl-warninglist-p x) (true-listp x))
             (vl-warningtree-p x))
    :hints(("Goal" :in-theory (enable vl-warningtree-p vl-warninglist-p)))))

(define vl-warningtree-flatten-aux ((x vl-warningtree-p)
                                    (context)
                                    (acc vl-warninglist-p))
  :returns (list vl-warninglist-p)
  :measure (vl-warningtree-count x)
  :verify-guards nil
  (vl-warningtree-case x
    :null (vl-warninglist-fix acc)
    :warning (cons (vl-warning-add-ctx x.warning context)
                   (vl-warninglist-fix acc))
    :context (vl-warningtree-flatten-aux x.subtree x.context acc)
    :pair (vl-warningtree-flatten-aux x.left context (vl-warningtree-flatten-aux x.right context acc)))
  ///
  (verify-guards vl-warningtree-flatten-aux))

(define vl-warningtree-flatten ((x vl-warningtree-p)
                                (context))
  :returns (list vl-warninglist-p)
  :verify-guards nil
  :measure (vl-warningtree-count x)
  (mbe :logic (vl-warningtree-case x
                :null nil
                :warning (list (vl-warning-add-ctx x.warning context))
                :context (vl-warningtree-flatten x.subtree x.context)
                :pair (append (vl-warningtree-flatten x.left context)
                              (vl-warningtree-flatten x.right context)))
       :exec (vl-warningtree-flatten-aux x context nil))
  ///
  (local (defthm vl-warningtree-flatten-aux-elim
           (equal (vl-warningtree-flatten-aux x context acc)
                  (append (vl-warningtree-flatten x context)
                          (vl-warninglist-fix acc)))
           :hints(("Goal" :in-theory (enable vl-warningtree-flatten-aux)))))

  (verify-guards vl-warningtree-flatten))


(define vl-warningtree-cons ((x vl-warningtree-p)
                             (y vl-warningtree-p))
  :returns (cons vl-warningtree-p)
  (cond ((vl-warningtree-case x :null) (vl-warningtree-fix y))
        ((vl-warningtree-case y :null) (vl-warningtree-fix x))
        (t (vl-warningtree-pair x y)))
  ///
  (defret vl-warningtree-flatten-of-cons
    (equal (vl-warningtree-flatten cons context)
           (append (vl-warningtree-flatten x context)
                   (vl-warningtree-flatten y context)))
    :hints(("Goal" :expand ((vl-warningtree-flatten x context)
                            (vl-warningtree-flatten y context)
                            (vl-warningtree-flatten (vl-warningtree-pair x y) context))))))

    

#!acl2
(def-b*-binder vl::wtmv
  :parents (warnings)
  :short "B* binder to automatically cons together returned warningtrees"
  :body
  (b* (((mv ctx args)
        (b* ((mem (member :ctx args)))
          (if mem
              (mv (cadr mem)
                  (append (take (- (len args) (len mem)) args)
                          (cddr mem)))
            (mv nil args)))))
    `(b* (,(if (equal args '(vl::warnings))
               `(vl::__tmp__warnings . ,forms)
             `((mv . ,(subst 'vl::__tmp__warnings 'vl::warnings args)) . ,forms))
          (vl::warnings (vl-warningtree-cons
                         ,(if ctx
                              `(vl::vl-warningtree-context ,ctx
                                                           vl::__tmp__warnings)
                            'vl::__tmp__warnings)
                         vl::warnings)))
       ,rest-expr)))




