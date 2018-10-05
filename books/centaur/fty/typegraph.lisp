; Centaur Miscellaneous Books
; Copyright (C) 2018 Centaur Technology
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

(in-package "FTY")
(include-book "centaur/misc/graphviz" :dir :system)
(include-book "baselists")
(include-book "visitor")       

(fty::defalist typegraph-atts-alist :key-type symbol :val-type viz::att-list :true-listp t)


(defconst *typegraph-edge-atts*
  `((:constructor . ,(list (viz::make-att :lhs "weight" :rhs "1")))
    (:sum . ,(list (viz::make-att :lhs "weight" :rhs "2")))
    (:transsum . ,(list (viz::make-att :lhs "weight" :rhs "1")))
    (:product . ,(list (viz::make-att :lhs "weight" :rhs "1")))
    (:list . ,(list (viz::make-att :lhs "weight" :rhs "2")))
    (:alist . ,(list (viz::make-att :lhs "weight" :rhs "1")))
    (:option . ,(list (viz::make-att :lhs "weight" :rhs "2")))))

(defconst *typegraph-node-atts*
  `((:constructor . ,(list (viz::make-att :lhs "shape" :rhs "diamond")))
    (:sum . ,(list (viz::make-att :lhs "shape" :rhs "invhouse")))
    (:transsum . ,(list (viz::make-att :lhs "shape" :rhs "invhouse") (viz::make-att :lhs "style" :rhs "dotted")))
    (:product . ,(list (viz::make-att :lhs "shape" :rhs "house")))
    (:list . ,(list (viz::make-att :lhs "shape" :rhs "box")))
    (:alist . ,(list (viz::make-att :lhs "shape" :rhs "trapezium")))
    (:option . ,(list (viz::make-att :lhs "shape" :rhs "oval") (viz::make-att :lhs "style" :rhs "dotted")))))

(defprod typegraph-props
  ((omits symbol-listp)
   (leaves symbol-listp)
   (types symbol-listp)
   (graphname stringp)
   (edge-atts typegraph-atts-alist :default *typegraph-edge-atts*)
   (node-atts typegraph-atts-alist :default *typegraph-node-atts*)))


(program)

(table std::define 'std::default-post-hooks nil)


(define typegraph-membertype-collect-member-types (type x wrld)
  (b* (((typegraph-props x))
       (type (fty::visitor-normalize-fixtype type wrld))
       (omit (member type x.omits))
       ((when omit) nil))
    (list type)))

(define typegraph-membertypes-collect-member-types (types x wrld)
  :mode :program :hooks nil
  (b* (((when (atom types)) nil))
    (union-eq (typegraph-membertype-collect-member-types (car types) x wrld)
              (typegraph-membertypes-collect-member-types (cdr types) x wrld))))

(define typegraph-field-collect-member-types (field x wrld)
  (b* (((fty::flexprod-field field)))
    (typegraph-membertype-collect-member-types field.type x wrld)))

(define typegraph-fields-collect-member-types (fields x wrld)
  (b* (((when (atom fields)) nil)
       (subtypes1
        (typegraph-field-collect-member-types (car fields) x wrld))
       (subtypes2
        (typegraph-fields-collect-member-types (cdr fields) x wrld)))
    (union-eq subtypes1 subtypes2)))



;; (defmacro typegraph-edge-stmt (node1 node2 kind)
;;   `(make-edge-stmt
;;     :nodes (list ,node1 ,node2)
;;     :atts (list (cdr (assoc ,kind *typegraph-edge-atts*)))))

(logic)

(define typegraph-edges-from-node-aux ((node viz::node-or-subgraph-p)
                                       (children symbol-listp)
                                       (atts viz::att-list-p))
  :mode :logic :hooks (:fix)
  :returns (edges viz::stmtlist-p)
  (if (atom children)
      nil
    (cons (viz::make-edge-stmt :nodes
                               (list node
                                     (viz::make-node-or-subgraph-node
                                      :id (viz::make-node-id :name (symbol-name (car children)))))
                               :atts (list atts))
          (typegraph-edges-from-node-aux node (cdr children) atts))))

(local (defthm alistp-when-typegraph-atts-alist-p-rw
         (implies (typegraph-atts-alist-p x)
                  (alistp x))))

(local (defthm assoc-when-alistp
         (implies (alistp x)
                  (equal (assoc k x)
                         (hons-assoc-equal k x)))))

(define typegraph-edges-from-node ((node viz::node-id-p)
                                   (children symbol-listp)
                                   (kind symbolp)
                                   (props typegraph-props-p))
  :mode :logic :hooks (:fix)
  :returns (edges viz::stmtlist-p)
  (typegraph-edges-from-node-aux (viz::make-node-or-subgraph-node :id node)
                                 children
                                 (cdr (assoc (mbe :logic (acl2::symbol-fix kind) :exec kind)
                                             (typegraph-props->edge-atts props)))))





(defmacro typegraph-node-stmt (node kind props)
  `(viz::make-node-stmt
    :id ,node
    :atts (list (cdr (assoc ,kind (typegraph-props->node-atts ,props))))))


(program)

(define typegraph-prods-collect-member-types (prods x wrld)
  :returns (mv viz-stmts member-types)
  (b* (((when (atom prods)) (mv nil nil))
       ((fty::flexprod prod1) (car prods))
       (node (viz::make-node-id :name (symbol-name prod1.type-name)))
       (node-stmt (typegraph-node-stmt node :constructor x))
       (subtypes1 (typegraph-fields-collect-member-types prod1.fields x wrld))
       (edge-stmts (typegraph-edges-from-node node subtypes1 :constructor x))
       ((mv stmts subtypes2) (typegraph-prods-collect-member-types (cdr prods) x wrld)))
    (mv (cons node-stmt (append edge-stmts stmts))
        (union-eq subtypes1 subtypes2))))


(define typegraph-sumtype-collect-member-types (type x wrld)
  :returns (mv viz-stmts member-types)
  (b* (((fty::flexsum type))
       (node (viz::make-node-id :name (symbol-name type.name)))
       (productp (eql (len type.prods) 1))
       (optionp (eq type.typemacro 'fty::defoption))
       (node-stmt (cond (productp (typegraph-node-stmt node :product x))
                        (optionp (typegraph-node-stmt node :option x))
                        (t (typegraph-node-stmt node :sum x))))
       ((typegraph-props x))
       ((when (member type.name x.leaves)) (mv (list node-stmt) nil))
       ((when productp)
        (b* (((fty::flexprod prod) (car type.prods))
             (subtypes (typegraph-fields-collect-member-types prod.fields x wrld))
             (edge-stmts (typegraph-edges-from-node node subtypes :product x)))
          (mv (cons node-stmt edge-stmts) subtypes)))
       ((when optionp)
        (b* (((fty::flexprod prod) (cadr type.prods))
             (subtypes (typegraph-fields-collect-member-types prod.fields x wrld))
             (edge-stmts (typegraph-edges-from-node node subtypes :option x)))
          (mv (cons node-stmt edge-stmts) subtypes)))
       (prod-types (fty::flexprodlist->type-names type.prods))
       (edge-stmts (typegraph-edges-from-node node prod-types :sum x))
       ((mv stmts member-types) (typegraph-prods-collect-member-types type.prods x wrld)))
    (mv (cons node-stmt (append edge-stmts stmts))
        member-types)))
       

(define typegraph-listtype-collect-member-types (type x wrld)
  :returns (mv viz-stmts member-types)
  (b* (((fty::flexlist type))
       (node (viz::make-node-id :name (symbol-name type.name)))
       (node-stmt (typegraph-node-stmt node :list x))
       ((typegraph-props x))
       ((when (member type.name x.leaves)) (mv (list node-stmt) nil))
       (member-types (typegraph-membertype-collect-member-types type.elt-type x wrld))
       (edge-stmts (typegraph-edges-from-node node member-types :list x)))
    (mv (cons node-stmt edge-stmts) member-types)))
       

(define typegraph-alisttype-collect-member-types (type x wrld)
  :returns (mv viz-stmts member-types)
  (b* (((fty::flexalist type))
       (node (viz::make-node-id :name (symbol-name type.name)))
       (node-stmt (typegraph-node-stmt node :alist x))
       (member-types1 (typegraph-membertype-collect-member-types type.key-type x wrld))
       (member-types2 (typegraph-membertype-collect-member-types type.val-type x wrld))
       (member-types (union-eq member-types1 member-types2))
       (edge-stmts (typegraph-edges-from-node node member-types :alist x)))
    (mv (cons node-stmt edge-stmts) member-types)))

;; (define typegraph-transsum-members-without-actions (typenames x)
;;   ;; Which member types of a transsum should we recur through when we are marking
;;   ;; types to be visited?  Only the ones where the action is NONE.
;;   (b* (((when (atom typenames))
;;         nil)
;;        ((typegraph-props x))
;;        (type-entry (assoc (car typenames) x.type-fns))
;;        ((when (cdr type-entry))
;;         ;; The action is not NONE.
;;         (typegraph-transsum-members-without-actions (cdr typenames) x)))
;;     (cons (car typenames)
;;           (typegraph-transsum-members-without-actions (cdr typenames) x))))

;; (define typegraph-transsum-is-leaf (typenames x)
;;   ;; When should the transsum be considered a leaf?  When it has any member that
;;   ;; has an action that is not SKIP and not NONE.
;;   (b* (((when (atom typenames)) nil)
;;        ((typegraph-props x))
;;        (type (car typenames))
;;        (type-entry (assoc type x.type-fns))
;;        ((when (and (cdr type-entry)
;;                    (not (eq (cdr type-entry) :skip))))
;;         t))
;;     (typegraph-transsum-is-leaf (cdr typenames) x)))

(define typegraph-transsumtype-collect-member-types (type x wrld)
  :returns (mv viz-stmts member-types)
  (b* (((fty::flextranssum type))
       (node (viz::make-node-id :name (symbol-name type.name)))
       (node-stmt (typegraph-node-stmt node :transsum x))
       (subtypes (typegraph-membertypes-collect-member-types
                  (fty::flextranssum-memberlist->typenames type.members)
                  x wrld))
       (edge-stmts (typegraph-edges-from-node node subtypes :transsum x)))
    (mv (cons node-stmt edge-stmts) subtypes)))

(define typegraph-type-collect-member-types ((typename)
                                           (x "The typegraph-props object.")
                                           wrld)
  (b* (((mv ?fty type-obj)
        (fty::search-deftypes-table typename (table-alist 'fty::flextypes-table wrld)))
       ((unless type-obj)
        (mv nil nil)))
    (case (tag type-obj)
      ;; bozo should be using with-flextype-bindings eh?
      (:sum      (typegraph-sumtype-collect-member-types type-obj x wrld))
      (:list     (typegraph-listtype-collect-member-types type-obj x wrld))
      (:alist    (typegraph-alisttype-collect-member-types type-obj x wrld))
      (:transsum (typegraph-transsumtype-collect-member-types type-obj x wrld))
      (otherwise (mv nil nil)))))


(mutual-recursion
 (defun typegraph-type-make-type-graph (typename
                                      x           ;; typegraph-props template
                                      wrld
                                      type-graph
                                      seen)
   (b* (((when (hons-get typename seen))
         ;; already seen
         (mv type-graph seen))
        (seen (hons-acons typename nil seen))
        ((mv graph-stmts subtypes) (typegraph-type-collect-member-types typename x wrld))
        (type-graph (revappend graph-stmts type-graph)))
     (typegraph-types-make-type-graph subtypes x wrld type-graph seen)))

 (defun typegraph-types-make-type-graph (types x wrld type-graph seen)
   (b* (((when (atom types)) (mv type-graph seen))
        ((mv type-graph seen)
         (typegraph-type-make-type-graph (car types) x wrld type-graph seen)))
     (typegraph-types-make-type-graph (cdr types) x wrld type-graph seen))))

(define make-typegraph (typegraph-props
                        state)
  (b* (((typegraph-props typegraph-props))
       ((mv stmts seen)
        (typegraph-types-make-type-graph typegraph-props.types typegraph-props  (w state) nil nil))
       (- (fast-alist-free seen)))
    (viz::make-graph :directedp t :name typegraph-props.graphname :stmts (reverse stmts))))

(define typegraph-string (typegraph-props
                          state)
  (b* ((stmts (make-typegraph typegraph-props state)))
    (viz::graph-to-string stmts)))


(define print-typegraph-to-channel (typegraph-props
                                    channel
                                    state)
  :guard (open-output-channel-p channel :character state)
  (princ$ (typegraph-string typegraph-props state) channel state))
                          

(define print-typegraph (typegraph-props
                         state)
  (print-typegraph-to-channel typegraph-props (standard-co state) state))

(define print-typegraph-to-file (typegraph-props
                                 filename
                                 state)
  (b* (((mv channel state) (open-output-channel filename :character state))
       ((unless channel)
        (er hard? 'print-typgegraph-to-file "Couldn't open output file: ~s0~%" filename)
        state)
       (state (print-typegraph-to-channel typegraph-props channel state)))
    (close-output-channel channel state)))

;; Render for presentation:
;; dot filename.dot -Tjpeg -Gratio=0.55 -Gsize=8.0 -Gdpi=150 -Epenwidth=3.0 -Npenwidth=4.0 > filename.jpg

;; Render as PDF:
;; dot filename.dot -Tpdf -Gratio=0.55 -Gsize=8.0 -Gdpi=150 -Epenwidth=3.0 -Npenwidth=4.0 > filename.pdf

;; View in x11:
;; dot filename.dot -Tx11 -Gratio=0.55 -Gsize=8.0 -Gdpi=150 -Epenwidth=3.0 -Npenwidth=4.0






                 
