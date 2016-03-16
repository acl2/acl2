; FTY Performance Tests
; Copyright (C) 2014 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "FTY")
(include-book "../visitor")
(include-book "../basetypes")
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(local (std::add-default-post-define-hook :fix))
(acl2::set-bogus-mutual-recursion-ok t)

(deftagsum simple-tree
  ;; Some simple kind of structure
  (:leaf ((name  stringp)
          (value natp)
          (cost  integerp)))
  (:branch ((left   simple-tree)
            (right  simple-tree)
            (hint   booleanp)
            (family stringp)
            (size   natp))))


(deftypes mrec-tree
  (deftagsum mrec-tree-node
     (:leaf ((name stringp)
             (value natp)
             (cost integerp)))
     (:branch ((children mrec-treelist)
               (family stringp)
               (size natp))))
  (deflist mrec-treelist :elt-type mrec-tree-node))

; Example 1: Let's visit every LEAF and collect up the names.

;; First try: this is very simple but collects all the strings, even
;; the "family" strings, instead of just the leaf names.
(defvisitor-template collect-strings ((x :object))
  :returns (names (:join (append names1 names)
                   :tmp-var names1
                   :initial nil)
                  string-listp)
  :type-fns ((string list))
  :fnname-template collect-strings-in-<type>)

(defvisitor collect-strings-in-simple-tree :type simple-tree :template collect-strings)


;; Second try: this targets exactly the LEAF structure and says what to do
;; there, but we don't have to write any code for the BRANCH structures.
(defvisitor-template collect-names ((x :object))
  :returns (names (:join (append names1 names)
                   :tmp-var names1
                   :initial nil)
                  string-listp)
  :prod-fns ((simple-tree-leaf (name list)))
  ;; :field-fns ((name list))
  :fnname-template collect-names<<type>> ;; C++ style
  )

(defvisitor collect-names<simple-tree> :type simple-tree :template collect-names)

(defvisitor-template collect-names-acc ((x :object)
                                        (names string-listp))
  :returns (names-out (:acc names)
                      string-listp :hyp (string-listp names))
  :prod-fns ((simple-tree-leaf (name cons)))
  :fnname-template collect-names-<type>-acc
  ;; :field-fns ((name list))
  )

(defvisitor :type simple-tree :template collect-names-acc)

; Example 2: Let's visit every LEAF and increment every value.

(defvisitor-template incr-val ((x :object))
  :returns (new-x :update)
  :prod-fns ((simple-tree-leaf (value 1+))))

(defvisitor incr-val-of-simple-tree :type simple-tree :template incr-val)


(defprod three-trees
  ((a simple-tree)
   (b simple-tree)
   (c simple-tree)))

(defvisitor :type three-trees :template collect-names-acc)






(local
 (progn

   (define double-sum-nat ((x natp)
                           (incr natp)
                           (acc natp))
     :returns (mv (sum natp :rule-classes :type-prescription)
                  (new-x natp :rule-classes :type-prescription)
                  (new-acc natp :rule-classes :type-prescription))
     (b* ((x (acl2::lnfix x))
          (incr (acl2::lnfix incr))
          (acc (acl2::lnfix acc)))
       (mv x
           (+ (* 2 x) incr)
           (+ (* 2 x) acc))))


   (defvisitor-template double-sum-nats ((x :object)
                                         (incr natp)
                                         (acc natp))
     :returns (mv (sum (:join (+ sum sum1)
                        :tmp-var sum1
                        :initial 0)
                       natp :rule-classes :type-prescription)
                  (new-x :update)
                  (new-acc (:acc acc :fix (acl2::lnfix acc))
                           natp :rule-classes :type-prescription))
     :type-fns ((natp double-sum-nat)
                ;; (integerp double-sum-int)
                ))


   (defprod my-prod
     ((str stringp)
      (nat natp)
      (nat2 natp)))

   (defvisitor :type my-prod :template double-sum-nats)


   (local (in-theory (disable nfix natp)))

   (deftagsum nat-tree
     (:leaf ((first natp)
             (second natp)))
     (:branch ((left nat-tree)
               (right nat-tree)
               (content natp))))

   (defvisitor :type nat-tree :template double-sum-nats)

   (deftypes bunch-of-stuff
     (deftagsum foosum
       (:prod1  ((a my-prod-p)
                 (b natp)
                 (c nat-tree)))
       (:prod2 ((lst foosumlist)
                (lst2 unusedlist)))
       (:empty ())
       (:prod3 ((alst1 foosum-alist)
                (alst2 foosum-alist2)
                (alst3 foosum-alist3)
                (alst4 unused-alist)))
       :measure (two-nats-measure (acl2-count x) 0))
     (deftagsum unused-sum
       (:proda ((sum1 foosum-p)))
       (:prodb ((sum2 foosum-p)))
       :base-case-override :proda
       :measure (two-nats-measure (acl2-count x) 1))
     (deflist foosumlist :elt-type foosum :measure (two-nats-measure (acl2-count x) 1))
     (deflist unusedlist :elt-type unused-sum :measure (two-nats-measure (acl2-count x) 1))
     (defalist foosum-alist :key-type my-prod :val-type foosumlist :measure (two-nats-measure (acl2-count x) 1))
     (defalist foosum-alist2 :key-type foosum-p :val-type stringp :measure (two-nats-measure (acl2-count x) 1))
     (defalist foosum-alist3 :key-type integerp :val-type foosum-p :measure (two-nats-measure (acl2-count x) 1))
     (defalist unused-alist  :key-type stringp :val-type unused-sum :measure (two-nats-measure (acl2-count x) 1)))

   (defvisitor double-sum-nats-of-bunch-of-stuff
     :type  bunch-of-stuff :template double-sum-nats
     :type-fns ((unused-sum   :skip)
                (unused-alist :skip)
                (unusedlist   double-sum-nats-unusedlist))
     :omit-types (unused-alist unusedlist)
     (define double-sum-nats-unusedlist ((x unusedlist-p)
                                         (incr natp)
                                         (acc natp))
       :returns (mv (sum natp :rule-classes :type-prescription)
                    (new-x unusedlist-p)
                    (new-acc natp :rule-classes :type-prescription))
       :measure (unusedlist-count x)
       (declare (ignorable x incr acc))
       (mv 555
           (list (make-unused-sum-proda :sum1 (make-foosum-empty)))
           333)))

   ;; (defvisitor bunch-of-stuff double-sum-nats)
   ))





(deftagsum literal
  (:constant ((value natp)))
  (:variable ((name symbolp))))

(defprod product
  ((first  literal-p)
   (second literal-p)
   (third  literal-p)))

(defprod sum
  :tag :sum
  ((left  product-p)
   (right product-p)))

;; Lookup table mapping each variable to a sum-of-products.
(defalist sop-env :key-type symbolp :val-type sum-p)

;; Suppose we have a lookup table and we want to collect all the dependencies
;; of some expression -- i.e., when we get to a variable we want to collect
;; it, then look up its formula and collect its dependencies too.  If the
;; table doesn't have some strict dependency order, then we might not
;; terminate, so we'll use a recursion limit.

(defvisitor-template collect-deps ((x :object)
                                   (env sop-env-p)
                                   (rec-limit natp))
  :returns (deps (:join (append deps1 deps)
                  :tmp-var deps1 :initial nil)
                 symbol-listp)

  ;; We'll call the function to apply to variable names
  ;; collect-and-recur-on-var.  Note that this hasn't been defined yet -- it
  ;; needs to be mutually recursive with the other functions in the clique.
  :prod-fns ((literal-variable (name collect-and-recur-on-var)))

  :fnname-template <type>-collect-deps)

;; A defvisitor-multi form binds together some defvisitor and defvisitors
;; forms into a mutual recursion with some other functions.  Here, we'll just have
;; the one defvisitors form inside.
(defvisitor-multi sum-collect-deps

  (defvisitors :template collect-deps :types (sum)
    ;; Normally this defvisitors form would create a visitor for a literal,
    ;; then product, then sum.  Inside a defvisitor-multi, it instead puts
    ;; all of those definitions into one mutual recursion.

    ;; We have to do something special with the measure.  Defvisitors
    ;; assigns an order to each of the types so that calling from one
    ;; visitor to another can generally reduce the measure.  Therefore, we
    ;; only need to decrease the rec-limit when calling from a lower-level
    ;; type to a higher-level one -- e.g. when we reach a variable and will
    ;; recur on a sum.
    :measure (two-nats-measure rec-limit :order)

    ;; Since our lowest-level visitor (literal-collect-deps) is going to
    ;; call an intermediate function (collect-and-recur-on-var) which then
    ;; calls our highest-level visitor (sum-collect-deps), it's convenient
    ;; to set the order of the lowest-level to 1 so that
    ;; collect-and-recur-on-var can use 0 as the order in its measure.
    :order-base 1)

  ;; This function goes in the mutual recursion with the others.
  (define collect-and-recur-on-var ((x symbolp)
                                    (env sop-env-p)
                                    (rec-limit natp))
    :returns (deps symbol-listp)
    :measure (two-nats-measure rec-limit 0)
    (b* ((x (mbe :logic (acl2::symbol-fix x) :exec x))
         (lookup (hons-get x (sop-env-fix env)))
         ((unless lookup) (list x))
         ((when (zp rec-limit))
          (cw "Recursion limit ran out on ~x0~%" x)
          (list x)))
      (cons x (sum-collect-deps (cdr lookup) env (- rec-limit 1))))))


;; (let ((al (make-fast-alist
;;            `((x . ,(sum (product (literal-constant 5)
;;                                  (literal-variable 'y)
;;                                  (literal-constant 3))
;;                         (product (literal-variable 'z)
;;                                  (literal-constant 4)
;;                                  (literal-variable 'a))))
;;              (y . ,(sum (product (literal-constant 1)
;;                                  (literal-variable 'b)
;;                                  (literal-constant 3))
;;                         (product (literal-variable 'z)
;;                                  (literal-constant 4)
;;                                  (literal-variable 'a))))
;;              (z . ,(sum (product (literal-constant 1)
;;                                  (literal-constant 2)
;;                                  (literal-constant 3))
;;                         (product (literal-variable 'b)
;;                                  (literal-constant 4)
;;                                  (literal-variable 'a))))))))
;;   (list (literal-collect-deps (literal-variable 'x) al 100)
;;         (literal-collect-deps (literal-variable 'y) al 100)
;;         (literal-collect-deps (literal-variable 'z) al 100)))

; Added by Matt K. 2/20/2016, pending possible mod by Sol to defvisitor.
(set-bogus-measure-ok t)

(local
 (progn

(deftranssum tstest
  (literal
   sum))

(local (in-theory (enable* std::tag-reasoning)))

(defvisitors double-tstest
  :types (tstest)
  :template double-sum-nats)

))
