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

(in-package "VIZ")

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/util/defenum" :dir :System)
(include-book "centaur/vl/util/defs" :dir :System) ;; bozo, just for maybe-string-fix
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "centaur/vl/util/printedlist" :dir :system)

(local (std::add-default-post-define-hook :fix))

;; graph 	: 	[ strict ] (graph | digraph) [ ID ] '{' stmt_list '}'
;; stmt_list 	: 	[ stmt [ ';' ] stmt_list ]
;; stmt 	: 	node_stmt
;; 	| 	edge_stmt
;; 	| 	attr_stmt
;; 	| 	ID '=' ID
;; 	| 	subgraph
;; attr_stmt 	: 	(graph | node | edge) attr_list
;; attr_list 	: 	'[' [ a_list ] ']' [ attr_list ]
;; a_list 	: 	ID '=' ID [ (';' | ',') ] [ a_list ]
;; edge_stmt 	: 	(node_id | subgraph) edgeRHS [ attr_list ]
;; edgeRHS 	: 	edgeop (node_id | subgraph) [ edgeRHS ]
;; node_stmt 	: 	node_id [ attr_list ]
;; node_id 	: 	ID [ port ]
;; port 	: 	':' ID [ ':' compass_pt ]
;; 	| 	':' compass_pt
;; subgraph 	: 	[ subgraph [ ID ] ] '{' stmt_list '}'
;; compass_pt 	: 	(n | ne | e | se | s | sw | w | nw | c | _)


(defenum compass-pt-p (:n :ne :e :se :s :sw :w :nw :c :_))

(define print-compass-pt ((x compass-pt-p) &key ((print-acc vl::vl-printedlist-p) 'print-acc))
  :returns (new-print-acc vl::vl-printedlist-p)
  (b* ((print-acc (vl::vl-printedlist-fix print-acc)))
    (cons (str::downcase-string (symbol-name (compass-pt-fix x))) print-acc)))

(fty::defoption maybe-compass-pt compass-pt-p)

(defprod port
  ((name acl2::maybe-stringp :rule-classes :type-prescription)
   (dir maybe-compass-pt-p)))

(define print-id ((x stringp) &key ((print-acc vl::vl-printedlist-p) 'print-acc))
  :returns (new-print-acc vl::vl-printedlist-p)
  (list* #\" (mbe :logic (acl2::str-fix x) :exec x) #\" (vl::vl-printedlist-fix print-acc)))


(define print-port ((x port-p) &key ((print-acc vl::vl-printedlist-p) 'print-acc))
  :returns (new-print-acc vl::vl-printedlist-p)
  (b* ((print-acc (vl::vl-printedlist-fix print-acc))
       ((port x))
       (print-acc (if x.name
                      (print-id x.name :print-acc (cons ":" print-acc))
                    print-acc)))
    (if x.dir
        (print-compass-pt x.dir :print-acc (cons ":" print-acc))
      print-acc)))

(fty::defoption maybe-port port)

(defprod node-id
  ((name stringp :rule-classes :type-prescription)
   (port maybe-port-p)))

(define print-node-id ((x node-id-p) &key ((print-acc vl::vl-printedlist-p) 'print-acc))
  :returns (new-print-acc vl::vl-printedlist-p)
  (b* ((print-acc (vl::vl-printedlist-fix print-acc))
       ((node-id x))
       (print-acc (print-id x.name))
       (print-acc (if x.port
                      (print-port x.port)
                    print-acc)))
    (cons " " print-acc)))

(defprod att ;; element of an a_list
  ((lhs stringp :rule-classes :type-prescription)
   (rhs stringp :rule-classes :type-prescription)))

(define print-att ((x att-p) &key ((print-acc vl::vl-printedlist-p) 'print-acc))
  :returns (new-print-acc vl::vl-printedlist-p)
  (b* ((print-acc (vl::vl-printedlist-fix print-acc))
       ((att x))
       (print-acc (print-id x.lhs))
       (print-acc (cons "=" print-acc)))
    (print-id x.rhs)))

(fty::deflist att-list ;; a_list
  :elt-type att :true-listp t)

(define print-att-list ((x att-list-p) &key ((print-acc vl::vl-printedlist-p) 'print-acc))
  :returns (new-print-acc vl::vl-printedlist-p)
  (b* ((print-acc (vl::vl-printedlist-fix print-acc))
       ((when (atom x)) print-acc)
       (print-acc (print-att (car x)))
       ((when (atom (cdr x))) print-acc)
       (print-acc (cons "; " print-acc)))
    (print-att-list (cdr x))))

(fty::deflist attr-list ;; attr_list
  :elt-type att-list :true-listp t)

(define print-attr-list ((x attr-list-p) &key ((print-acc vl::vl-printedlist-p) 'print-acc))
  :returns (new-print-acc vl::vl-printedlist-p)
  (b* ((print-acc (vl::vl-printedlist-fix print-acc))
       ((when (atom x)) print-acc)
       (print-acc (cons "[ " print-acc))
       (print-acc (print-att-list (car x)))
       (print-acc (cons " ] " print-acc)))
    (print-attr-list (cdr x))))

(defenum graphnodeedge-p (:graph :node :edge))

(define print-graphnodeedge ((x graphnodeedge-p) &key ((print-acc vl::vl-printedlist-p) 'print-acc))
  :returns (new-print-acc vl::vl-printedlist-p)
  (b* ((print-acc (vl::vl-printedlist-fix print-acc)))
    (cons (str::downcase-string (symbol-name (graphnodeedge-fix x))) print-acc)))

(deftypes stmt
  (deftagsum stmt
    (:node-stmt ((id node-id-p)
                 (atts attr-list-p))
     :base-name node-stmt)
    (:edge-stmt ((nodes node-or-subgraphlist-p)
                 (atts attr-list-p))
     :base-name edge-stmt)
    (:attr-stmt ((type graphnodeedge-p)
                 (atts attr-list-p))
     :base-name attr-stmt)
    (:att-stmt  ((lhs stringp :rule-classes :type-prescription)
                 (rhs stringp :rule-classes :type-prescription))
     :base-name att-stmt)
    (:subgraph-stmt ((subgraph subgraph-p))
     :base-name subgraph-stmt)
    :measure (acl2::two-nats-measure (acl2-count x) 5))

  (fty::deflist stmtlist :elt-type stmt :true-listp t
    :measure (acl2::two-nats-measure (acl2-count x) 4))

  (defprod subgraph
    ((name acl2::maybe-stringp :rule-classes :type-prescription)
     (stmts stmtlist-p))
    :measure (acl2::two-nats-measure (acl2-count x) 8))

  (deftagsum node-or-subgraph
    (:node ((id node-id-p)))
    (:subgraph ((subgraph subgraph-p)))
    :measure (acl2::two-nats-measure (acl2-count x) 8))

  (fty::deflist node-or-subgraphlist :elt-type node-or-subgraph :true-listp t
    :non-emptyp t ;; used for edge lists which must be non-empty
    :measure (acl2::two-nats-measure (acl2-count x) 9)))

(defines print-stmt
  :verify-guards nil
  (define print-stmt ((x stmt-p)
                      (directedp booleanp)
                      &key ((print-acc vl::vl-printedlist-p) 'print-acc))
    :returns (new-print-acc vl::vl-printedlist-p)
    :measure (stmt-count x)
    (b* ((print-acc (vl::vl-printedlist-fix print-acc)))
      (stmt-case x
        :node-stmt (b* ((print-acc (print-node-id x.id)))
                     (print-attr-list x.atts))
        :edge-stmt (b* ((print-acc (print-edge-list x.nodes directedp)))
                     (print-attr-list x.atts))
        :attr-stmt (b* ((print-acc (print-graphnodeedge x.type))
                        (print-acc (cons " " print-acc)))
                     (print-attr-list x.atts))
        :att-stmt (b* ((print-acc (print-id x.lhs))
                       (print-acc (cons "=" print-acc)))
                    (print-id x.rhs))
        :subgraph-stmt (print-subgraph x.subgraph directedp))))
  (define print-subgraph ((x subgraph-p)
                          (directedp booleanp)
                          &key ((print-acc vl::vl-printedlist-p) 'print-acc))
    :returns (new-print-acc vl::vl-printedlist-p)
    :measure (subgraph-count x)
    (b* ((print-acc (vl::vl-printedlist-fix print-acc))
         ((subgraph x))
         (print-acc (cons "subgraph " print-acc))
         (print-acc (if x.name (cons " " (print-id x.name)) print-acc))
         (print-acc (cons "{ " print-acc))
         (print-acc (print-stmtlist x.stmts directedp)))
      (list* #\Newline "}" print-acc)))

  (define print-stmtlist ((x stmtlist-p)
                          (directedp booleanp)
                          &key ((print-acc vl::vl-printedlist-p) 'print-acc))
    :returns (new-print-acc vl::vl-printedlist-p)
    :measure (stmtlist-count x)
    (b* ((print-acc (vl::vl-printedlist-fix print-acc))
         ((when (atom x)) print-acc)
         (print-acc (print-stmt (car x) directedp))
         (print-acc (list* #\Newline ";" print-acc)))
      (print-stmtlist (cdr x) directedp)))

  (define print-node-or-subgraph ((x node-or-subgraph-p)
                                  (directedp booleanp)
                                  &key ((print-acc vl::vl-printedlist-p) 'print-acc))
    :returns (new-print-acc vl::vl-printedlist-p)
    :measure (node-or-subgraph-count x)
    (b* ((print-acc (vl::vl-printedlist-fix print-acc)))
      (node-or-subgraph-case x
        :node (print-node-id x.id)
        :subgraph (print-subgraph x.subgraph directedp))))

  (define print-edge-list ((x node-or-subgraphlist-p)
                          (directedp booleanp)
                          &key ((print-acc vl::vl-printedlist-p) 'print-acc))
    :returns (new-print-acc vl::vl-printedlist-p)
    :measure (node-or-subgraphlist-count x)
    (b* ((print-acc (vl::vl-printedlist-fix print-acc))
         (print-acc (print-node-or-subgraph (car x) directedp))
         ((when (atom (cdr x))) print-acc)
         (print-acc (cons (if directedp " -> " " -- ") print-acc)))
      (print-edge-list (cdr x) directedp)))
  ///
  (verify-guards print-stmt-fn))


(defprod graph
  ((strictp booleanp :rule-classes :type-prescription)
   (directedp booleanp :rule-classes :type-prescription)
   (name acl2::maybe-stringp :rule-classes :type-prescription)
   (stmts stmtlist-p)))

(define print-graph ((x graph-p)
                     &key ((print-acc vl::vl-printedlist-p) 'print-acc))
  :returns (new-print-acc vl::vl-printedlist-p)
  (b* ((print-acc (vl::vl-printedlist-fix print-acc))
       ((graph x))
       (print-acc (if x.strictp (cons "strict " print-acc) print-acc))
       (print-acc (cons (if x.directedp "digraph " "graph ") print-acc))
       (print-acc (if x.name (cons " " (print-id x.name)) print-acc))
       (print-acc (cons "{ " print-acc))
       (print-acc (print-stmtlist x.stmts x.directedp)))
    (list* #\Newline " }" print-acc)))

(define graph-to-string ((x graph-p))
  :returns (string stringp :rule-classes :type-prescription)
  (vl::vl-printedlist->string (print-graph x :print-acc nil)))


