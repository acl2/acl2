; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "../mlib/scopestack")
(include-book "../mlib/stmt-tools")
(include-book "../mlib/strip")
(include-book "../mlib/fmt")
(include-book "../mlib/print-warnings")
(include-book "../mlib/range-tools")
(include-book "../mlib/datatype-tools")
(include-book "../mlib/reportcard")
(include-book "../mlib/hid-tools")
(include-book "../util/cwtime")
(include-book "../util/sum-nats")
(include-book "../util/merge-indices")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defthm vl-scopestack->design-of-vl-scopestack-local
  (equal (vl-scopestack->design (vl-scopestack-local scope ss))
         (vl-scopestack->design ss))
  :hints(("Goal" :expand ((vl-scopestack->design (vl-scopestack-local scope ss))))))

(defthm vl-scopestack->design-of-vl-scopestack-push
  (equal (vl-scopestack->design (vl-scopestack-push scope ss))
         (vl-scopestack->design ss))
  :hints(("Goal" :in-theory (enable vl-scopestack-push))))


(defxdoc lucid
  :parents (lint)
  :short "Check for unused, unset, and spurious wires.")


; State Representation --------------------------------------------------------

(local (xdoc::set-default-parents vl-lucidstate))

(defprod vl-lucidkey
  :layout :tree
  :hons t
  :short "A single key in the lucid database."
  ((item       vl-scopeitem-p "The item we're dealing with.")
   (scopestack vl-scopestack  "The scopestack where this key was found."))
  :long "<p>Keys are honsed, even though this is expensive, so that they can be
used in fast alists.</p>")

(fty::deflist vl-lucidkeylist
  :elt-type vl-lucidkey)

(deftagsum vl-lucidocc
  :short "Record of an occurrence of an identifier."

  (:solo
   :short "A lone instance of an identifier."
   :long "<p>We use this to record occurrences of an identifier all by itself,
e.g., in an assignment like @('assign ... = b + c[3:0]'), we would record a
solo occurrence of @('b').</p>" nil)

  (:slice
   :short "An indexed occurrence of an identifier."
   :long "<p>We use this to record occurrences of an identifier with a bit- or
part-select.  For individual selects like @('foo[3]'), both left and right will
be the same.</p>"
   ((left  vl-expr-p)
    (right vl-expr-p)))

;;   (:member
;;    :short "An occurrence of a structure member."
;;    :long "<p>We use this to record occurrences of a particular field of a
;; structure.  For instance, of we have @('myinst') which is an @('instruction_t')
;; structure, then we might access fields like @('myinst.opcode') and
;; @('myinst.arg1').</p>"
;;    ((field stringp :rule-classes :type-prescription)))
)

(fty::deflist vl-lucidocclist
  :elt-type vl-lucidocc)

(defprod vl-lucidval
  :short "Use/set information about a single variable."
  ((used   vl-lucidocclist-p
           "List of occurrences where this variable is used.")
   (set    vl-lucidocclist-p
           "List of occurrences where this variable is set.")
   (errors true-listp
           "Information on any errors related to analyzing this key.")))

(defval *vl-empty-lucidval*
  :parents (vl-lucidval)
  (make-vl-lucidval :used nil
                    :set nil
                    :errors nil))

(fty::defalist vl-luciddb
  :short "The main @(see lucid) database.  Binds keys (scopestack/item pairs)
          to information about how they have been used."
  :key-type vl-lucidkey
  :val-type vl-lucidval
  :count vl-luciddb-count)

(fty::defprod vl-lucidstate
  :parents (lucid)
  :layout :tree
  :short "State for the lucid transform."
  ((db      vl-luciddb-p
            "Main database mapping keys to their use/set occurrences.")

   (paramsp booleanp :rule-classes :type-prescription
            "Should we issue warnings for parameters?  It generally will only
             make sense to do this <i>before</i> unparameterization has taken
             place, because unparameterization should generally get rid of any
             sensible parameters.")

   (warnings vl-warninglist-p)))


; State Initialization --------------------------------------------------------

(local (xdoc::set-default-parents vl-lucidstate-init))

(define vl-scope-luciddb-init-aux
  :parents (vl-luciddb-initialize-scope)
  ((locals vl-scopeitem-alist-p "The local variables declared in some scope.")
   (ss vl-scopestack-p          "Scopestack for our current location.")
   (db vl-luciddb-p             "Database we're initializing."))
  :returns
  (new-db vl-luciddb-p "Database extended with all the variables in @('locals').")
  :measure (vl-scopeitem-alist-count locals)
  (b* ((locals (vl-scopeitem-alist-fix locals))
       ((when (atom locals))
        (vl-luciddb-fix db))
       ((cons ?name item) (car locals))
       (key (make-vl-lucidkey :item item :scopestack ss))
       (db  (hons-acons key *vl-empty-lucidval* db)))
    (vl-scope-luciddb-init-aux (cdr locals) ss db)))

(define vl-scope-luciddb-init
  :short "Initialize variables for a scope."
  ((x  vl-scope-p      "Current scope we're processing, already added to the scopestack.")
   (ss vl-scopestack-p "Scopestack for our current location.")
   (db vl-luciddb-p    "Database we're initializing."))
  :returns
  (new-db vl-luciddb-p "Database extended with all variables from this scope.")

  :long "<p>The scopeinfo for @('x') has locals, imports, and star-packages,
but we only want the locals: any imports or star-packages are of course
relevant for looking up variables, but those variables will have their own keys
created when we process their packages, etc.</p>"

  (b* ((x      (vl-scope-fix x))
       (info   (vl-scope->scopeinfo x (vl-scopestack->design ss)))
       (locals (vl-scopeinfo->locals info)))
    (vl-scope-luciddb-init-aux locals ss db)))

(defines vl-stmt-luciddb-init

  (define vl-stmt-luciddb-init ((x  vl-stmt-p)
                                (ss vl-scopestack-p)
                                (db vl-luciddb-p))
    :returns (new-db vl-luciddb-p)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (b* ((x (vl-stmt-fix x))
         ((when (vl-atomicstmt-p x))
          (vl-luciddb-fix db))
         ((when
              ;; NOTE -- This must be kept in sync with vl-stmt-lucidcheck!!
              (and (eq (vl-stmt-kind x) :vl-blockstmt)
                   (consp (vl-blockstmt->decls x))))
          (b* ((blockscope (vl-blockstmt->blockscope x))
               (ss         (vl-scopestack-push blockscope ss))
               (db         (vl-scope-luciddb-init blockscope ss db)))
            (vl-stmtlist-luciddb-init (vl-blockstmt->stmts x) ss db))))
      (vl-stmtlist-luciddb-init (vl-compoundstmt->stmts x) ss db)))

  (define vl-stmtlist-luciddb-init ((x  vl-stmtlist-p)
                                    (ss vl-scopestack-p)
                                    (db vl-luciddb-p))
    :returns (new-db vl-luciddb-p)
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          (vl-luciddb-fix db))
         (db (vl-stmt-luciddb-init (car x) ss db)))
      (vl-stmtlist-luciddb-init (cdr x) ss db)))
  ///
  (verify-guards vl-stmt-luciddb-init)
  (deffixequiv-mutual vl-stmt-luciddb-init))

(define vl-always-luciddb-init ((x  vl-always-p)
                                (ss vl-scopestack-p)
                                (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (vl-stmt-luciddb-init (vl-always->stmt x) ss db))

(define vl-alwayslist-luciddb-init ((x  vl-alwayslist-p)
                                    (ss vl-scopestack-p)
                                    (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-always-luciddb-init (car x) ss db)))
    (vl-alwayslist-luciddb-init (cdr x) ss db)))

(define vl-initial-luciddb-init ((x  vl-initial-p)
                                 (ss vl-scopestack-p)
                                 (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (vl-stmt-luciddb-init (vl-initial->stmt x) ss db))

(define vl-initiallist-luciddb-init ((x  vl-initiallist-p)
                                     (ss vl-scopestack-p)
                                     (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-initial-luciddb-init (car x) ss db)))
    (vl-initiallist-luciddb-init (cdr x) ss db)))

(define vl-fundecl-luciddb-init ((x  vl-fundecl-p)
                                 (ss vl-scopestack-p)
                                 (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* ((scope (vl-fundecl->blockscope x))
       (ss    (vl-scopestack-push scope ss))
       (db    (vl-scope-luciddb-init scope ss db)))
    (vl-stmt-luciddb-init (vl-fundecl->body x) ss db)))

(define vl-fundecllist-luciddb-init ((x  vl-fundecllist-p)
                                     (ss vl-scopestack-p)
                                     (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-fundecl-luciddb-init (car x) ss db)))
    (vl-fundecllist-luciddb-init (cdr x) ss db)))

(define vl-taskdecl-luciddb-init ((x  vl-taskdecl-p)
                                  (ss vl-scopestack-p)
                                  (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* ((scope (vl-taskdecl->blockscope x))
       (ss    (vl-scopestack-push scope ss))
       (db    (vl-scope-luciddb-init scope ss db)))
    (vl-stmt-luciddb-init (vl-taskdecl->body x) ss db)))

(define vl-taskdecllist-luciddb-init ((x  vl-taskdecllist-p)
                                      (ss vl-scopestack-p)
                                      (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-taskdecl-luciddb-init (car x) ss db)))
    (vl-taskdecllist-luciddb-init (cdr x) ss db)))

(def-genblob-transform vl-genblob-luciddb-init ((ss vl-scopestack-p)
                                                (db vl-luciddb-p))
  ;; BOZO I don't really understand what this is doing or whether it's right.
  ;; For instance how does this handle arrays?
  :returns ((db vl-luciddb-p))
  (b* (((vl-genblob x) (vl-genblob-fix x))
       (ss                 (vl-scopestack-push x ss))
       (db                 (vl-scope-luciddb-init x ss db))
       ((mv db ?generates) (vl-generates-luciddb-init x.generates ss db))
       (db                 (vl-fundecllist-luciddb-init x.fundecls ss db))
       (db                 (vl-taskdecllist-luciddb-init x.taskdecls ss db))
       (db                 (vl-alwayslist-luciddb-init x.alwayses ss db))
       (db                 (vl-initiallist-luciddb-init x.initials ss db)))
    (mv db x))
  :apply-to-generates vl-generates-luciddb-init)

;; (defines vl-genblob-luciddb-init
;;   ;; Custom handler for generate blocks.  This is tricky.  Every IF and LOOP
;;   ;; gets its own scopes.

;;   (define vl-genblob-luciddb-init ((x  vl-genblob-p)
;;                                    (ss vl-scopestack-p)
;;                                    (db vl-luciddb-p))
;;     :returns (db vl-luciddb-p)
;;     :measure (vl-genblob-count x)
;;     :verify-guards nil
;;     (b* (((vl-genblob x) (vl-genblob-fix x))
;;          (ss (vl-scopestack-push x ss))
;;          (db (vl-scope-luciddb-init x ss db))
;;          ;; Portdecls, assigns, aliases, vardecls, paramdecls - no subscopes
;;          (db (vl-fundecllist-luciddb-init x.fundecls ss db))
;;          (db (vl-taskdecllist-luciddb-init x.taskdecls ss db))
;;          ;; Modinsts, gateinsts -- no subscopes
;;          (db (vl-alwayslist-luciddb-init x.alwayses ss db))
;;          (db (vl-initiallist-luciddb-init x.initials ss db))
;;          ;; Typedefs, imports, fwdtypedefs, modports -- no subscopes
;;          (db (vl-generates-luciddb-init x.generates ss db))
;;          ;; Ports, name -- no subscopes.
;;          )
;;       db))

;;   (define vl-generates-luciddb-init ((x  vl-genelementlist-p)
;;                                      (ss vl-scopestack-p)
;;                                      (db vl-luciddb-p))
;;     :returns (db vl-luciddb-p)
;;     :measure (vl-genblob-generates-count x)
;;     (b* (((when (atom x))
;;           (vl-luciddb-fix db))
;;          (db (vl-genblob-luciddb-init-generate (car x) ss db)))
;;       (vl-generates-luciddb-init (cdr x) ss db)))

;;   (define vl-genblob-luciddb-init-generate ((x  vl-genelement-p)
;;                                             (ss vl-scopestack-p)
;;                                             (db vl-luciddb-p))
;;     :returns (db vl-luciddb-p)
;;     :measure (vl-genblob-generate-count x)
;;     (vl-genelement-case
;;       x
;;       ;; BOZO lots to do here, genifs, genloops, etc.
;;       :vl-genblock (vl-genblob-luciddb-init-elementlist x.elems ss db)
;;       :vl-genarray
;;       (b* ((db (vl-genblob-luciddb-init-genarrayblocklist x.blocks ss db)))
;;         db)))

;;   (define vl-genblob-luciddb-init-elementlist ((x  vl-genelementlist-p)
;;                                                (ss vl-scopestack-p)
;;                                                (db vl-luciddb-p))
;;     :returns (db vl-luciddb-p)
;;     :measure (vl-genblob-elementlist-count x)
;;     (b* (((maybe-mv db new-blob)
;;           (vl-genblob-luciddb-init (vl-sort-genelements x)
;;                                    ss db)))
;;       (maybe-mv db (vl-genblob->elems new-blob x))))

;;  (define vl-genblob-luciddb-init-genarrayblocklist
;;          ((x vl-genarrayblocklist-p)
;;           (ss vl-scopestack-p)
;;           (db vl-luciddb-p))
;;          :returns
;;          (mv (db vl-luciddb-p)
;;              (new-x vl-genarrayblocklist-p))
;;          :measure
;;          (vl-genblob-genarrayblocklist-count x)
;;          (b* (((when (atom x))
;;                (b* ((db (vl-luciddb-fix db)))
;;                    (maybe-mv db nil)))
;;               ((maybe-mv db first)
;;                (vl-genblob-luciddb-init-genarrayblock (car x)
;;                                                       ss db))
;;               ((maybe-mv db rest)
;;                (vl-genblob-luciddb-init-genarrayblocklist (cdr x)
;;                                                           ss db)))
;;              (maybe-mv db (cons first rest))))

;;  (define vl-genblob-luciddb-init-genarrayblock ((x vl-genarrayblock-p)
;;                                                 (ss vl-scopestack-p)
;;                                                 (db vl-luciddb-p))
;;    :returns
;;    (mv (db vl-luciddb-p)
;;        (new-x vl-genarrayblock-p))
;;    :measure
;;    (vl-genblob-genarrayblock-count x)
;;    (b* (((vl-genarrayblock x))
;;         ((maybe-mv db new-elems)
;;          (vl-genblob-luciddb-init-elementlist x.elems ss db)))
;;      (maybe-mv db
;;                (change-vl-genarrayblock x
;;                                                 :elems new-elems))))
;;  ///
;;  (local (in-theory (disable vl-genblob-luciddb-init-genarrayblock
;;                             vl-genblob-luciddb-init-genarrayblocklist
;;                             vl-genblob-luciddb-init-elementlist
;;                             vl-genblob-luciddb-init-generate
;;                             vl-generates-luciddb-init
;;                             vl-genblob-luciddb-init)))
;;  (verify-guards vl-genblob-luciddb-init
;;                 :hints nil)
;;  (deffixequiv-mutual
;;       vl-genblob-luciddb-init
;;       :hints ((and stable-under-simplificationp
;;                    (std::expand-calls-computed-hint
;;                         clause
;;                         '(vl-genblob-luciddb-init-genarrayblock
;;                               vl-genblob-luciddb-init-genarrayblocklist
;;                               vl-genblob-luciddb-init-elementlist
;;                               vl-genblob-luciddb-init-generate
;;                               vl-generates-luciddb-init
;;                               vl-genblob-luciddb-init))))))

(define vl-module-luciddb-init ((x  vl-module-p)
                                (ss vl-scopestack-p)
                                (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* ((genblob (vl-module->genblob x))
       ((mv db ?new-genblob) (vl-genblob-luciddb-init genblob ss db)))
    db))

(define vl-modulelist-luciddb-init ((x  vl-modulelist-p)
                                    (ss vl-scopestack-p)
                                    (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-module-luciddb-init (car x) ss db)))
    (vl-modulelist-luciddb-init (cdr x) ss db)))

(define vl-package-luciddb-init ((x  vl-package-p)
                                 (ss vl-scopestack-p)
                                 (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((vl-package x) (vl-package-fix x))
       (ss (vl-scopestack-push x ss))
       (db (vl-scope-luciddb-init x ss db))
       (db (vl-fundecllist-luciddb-init x.fundecls ss db))
       (db (vl-taskdecllist-luciddb-init x.taskdecls ss db)))
    db))

(define vl-packagelist-luciddb-init ((x  vl-packagelist-p)
                                     (ss vl-scopestack-p)
                                     (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-package-luciddb-init (car x) ss db)))
    (vl-packagelist-luciddb-init (cdr x) ss db)))

(define vl-interface-luciddb-init ((x  vl-interface-p)
                                   (ss vl-scopestack-p)
                                   (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((vl-interface x) (vl-interface-fix x))
       (ss (vl-scopestack-push x ss))
       (db (vl-scope-luciddb-init x ss db))

       ;; BOZO I thought interfaces were supposed to be able to have
       ;; functions and tasks??
       ;(db (vl-fundecllist-luciddb-init x.fundecls ss db))
       ;(db (vl-taskdecllist-luciddb-init x.taskdecls ss db))
       )
    ;; BOZO missing generates
    db))

(define vl-interfacelist-luciddb-init ((x  vl-interfacelist-p)
                                     (ss vl-scopestack-p)
                                     (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* (((when (atom x))
        (vl-luciddb-fix db))
       (db (vl-interface-luciddb-init (car x) ss db)))
    (vl-interfacelist-luciddb-init (cdr x) ss db)))

(define vl-luciddb-init
  :short "Construct the initial @(see lucid) database for a design."
  ((x vl-design-p))
  :returns (db vl-luciddb-p)
  (b* (((vl-design x) (vl-design-fix x))
       (ss   (vl-scopestack-init x))
       (db   nil)
       (db   (vl-scope-luciddb-init x ss db))
       (db   (vl-modulelist-luciddb-init    x.mods        ss db))
       (db   (vl-fundecllist-luciddb-init   x.fundecls    ss db))
       (db   (vl-taskdecllist-luciddb-init  x.taskdecls   ss db))
       (db   (vl-packagelist-luciddb-init   x.packages    ss db))
       (db   (vl-interfacelist-luciddb-init x.interfaces  ss db)))
    db))

(define vl-lucidstate-init
  :parents (lucid)
  :short "Construct the initial @(see lucid) state for a design."
  ((x vl-design-p)
   &key
   ((paramsp booleanp) 't))
  :returns (st vl-lucidstate-p)
  (make-vl-lucidstate :db (vl-luciddb-init x)
                      :paramsp paramsp))


; State Debugging -------------------------------------------------------------

(local (xdoc::set-default-parents vl-pps-lucidstate))

(define vl-pp-scope-name ((x vl-scope-p) &key (ps 'ps))
  (b* ((x    (vl-scope-fix x))
       (name (vl-scope->name x)))
    (if name
        (vl-print-str name)
      (vl-ps-seq (vl-print "<unnamed ")
                 (vl-print-str (symbol-name (tag x)))
                 (vl-cw " : ~x0>" x)))))

(define vl-pp-scopestack-path ((x vl-scopestack-p) &key (ps 'ps))
  :measure (vl-scopestack-count x)
  (vl-scopestack-case x
    :null   (vl-print ":null")
    :global (vl-ps-seq (vl-print "$root"))
    :local  (vl-ps-seq (vl-pp-scopestack-path x.super)
                       (vl-print ".")
                       (vl-pp-scope-name x.top))))

(define vl-pps-scopestack-path ((x vl-scopestack-p))
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-scopestack-path x)))

(define vl-lucid-mash-tag ((x stringp))
  :returns (new-x stringp :rule-classes :type-prescription)
  (b* ((x (string-fix x))
       (x (str::strsubst "VL-" "" x))
       (x (str::strsubst "DECL" "" x))
       (x (str::downcase-string x)))
    x)
  ///
  (assert! (equal (vl-lucid-mash-tag "VL-VARDECL") "var"))
  (assert! (equal (vl-lucid-mash-tag "VL-PARAMDECL") "param"))
  (assert! (equal (vl-lucid-mash-tag "VL-FUNDECL") "fun"))
  (assert! (equal (vl-lucid-mash-tag "VL-TASKDECL") "task")))

(define vl-pp-lucidkey ((x vl-lucidkey-p) &key (ps 'ps))
  :prepwork ((local (defthm l0
                      (implies (vl-scopeitem-p x)
                               (symbolp (tag x)))
                      :hints(("Goal" :in-theory (enable vl-scopeitem-p
                                                        tag))))))
  (b* (((vl-lucidkey x) (vl-lucidkey-fix x))
       (name (vl-scopeitem->name x.item)))
    (vl-ps-seq (vl-pp-scopestack-path x.scopestack)
               (if name
                   (vl-ps-seq (vl-print ".")
                              (vl-print name))
                 (vl-ps-seq
                  (vl-print ".<unnamed ")
                  (vl-print-str (vl-lucid-mash-tag (symbol-name (tag x.item))))
                  (vl-cw " ~x0>" x)))
               (vl-print " (")
               (vl-print-str (vl-lucid-mash-tag (symbol-name (tag x.item))))
               (vl-print ")"))))

(define vl-pp-lucidocc ((x vl-lucidocc-p) &key (ps 'ps))
  (vl-lucidocc-case x
    (:solo   (vl-print ":solo"))
    (:slice  (vl-cw "(:slice ~a0 ~a1)" x.left x.right))
    ;(:member (vl-cw "(:field ~s0)"     x.field))
    ))

(define vl-pp-lucidocclist ((x vl-lucidocclist-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-lucidocc (car x))
               (vl-print " ")
               (vl-pp-lucidocclist (cdr x)))))

(define vl-pp-lucidval ((x vl-lucidval-p) &key (ps 'ps))
  (b* (((vl-lucidval x)))
    (vl-ps-seq (vl-print "Used: ")
               (if x.used
                   (vl-pp-lucidocclist (mergesort x.used))
                 (vl-print "never"))
               (vl-print "; Set: ")
               (if x.set
                   (vl-pp-lucidocclist (mergesort x.set))
                 (vl-print "never"))
               (if x.errors
                   (vl-cw "; Errors: ~x0~%" x.errors)
                 ps))))

(define vl-pp-luciddb-aux ((x vl-luciddb-p) &key (ps 'ps))
  :measure (vl-luciddb-count x)
  (b* ((x (vl-luciddb-fix x))
       ((when (atom x))
        ps)
       ((cons key val) (car x)))
    (vl-ps-seq (vl-print "  ")
               (vl-pp-lucidkey key)
               (vl-print ": ")
               (vl-indent 40)
               (vl-pp-lucidval val)
               (vl-println "")
               (vl-pp-luciddb-aux (cdr x)))))

(define vl-pp-luciddb ((x vl-luciddb-p) &key (ps 'ps))
  (b* ((x    (vl-luciddb-fix x))
       (copy (fast-alist-fork x nil))
       (-    (fast-alist-free copy)))
    (vl-pp-luciddb-aux copy)))

(define vl-pp-lucidstate ((x vl-lucidstate-p) &key (ps 'ps))
  (b* (((vl-lucidstate x)))
    (vl-ps-seq (vl-println "lucidstate {")
               (vl-pp-luciddb x.db)
               (vl-println "}"))))

(define vl-pps-lucidstate ((x vl-lucidstate-p))
  :parents (lucid)
  :short "Pretty-printer for debugging the lucid state."
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-lucidstate x)))


; State Mutators --------------------------------------------------------------

(local (xdoc::set-default-parents lucid))

(define vl-luciddb-mark ((mtype (member mtype '(:used :set)))
                         (key   vl-lucidkey-p)
                         (occ   vl-lucidocc-p)
                         (db    vl-luciddb-p)
                         (ctx   acl2::any-p))
  :parents (vl-lucidstate-mark-used)
  :returns (new-db vl-luciddb-p)
  (b* ((db   (vl-luciddb-fix db))
       (occ  (vl-lucidocc-fix occ))
       (key  (vl-lucidkey-fix key))

       (val (cdr (hons-get key db)))
       ((unless val)
        ;; BOZO we probably don't expect this to happen, but we'll go ahead and
        ;; mark it as an error.
        (let ((err (list __function__ ctx)))
          (hons-acons key
                      (change-vl-lucidval *vl-empty-lucidval*
                                          :used (list occ)
                                          :errors (list err))
                      db)))

       ((vl-lucidval val))
       (val (if (eq mtype :used)
                (change-vl-lucidval val :used (cons occ val.used))
              (change-vl-lucidval val :set (cons occ val.set))))
       (db  (hons-acons key val db)))
    db))

(define vl-lucidstate-mark ((mtype (member mtype '(:used :set)))
                            (key   vl-lucidkey-p)
                            (occ   vl-lucidocc-p)
                            (st    vl-lucidstate-p)
                            (ctx   acl2::any-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((vl-lucidstate st))
       (db (vl-luciddb-mark mtype key occ st.db ctx)))
    (change-vl-lucidstate st :db db)))

(define vl-lucid-mark-simple ((mtype (member mtype '(:used :set)))
                              (name  stringp)
                              (ss    vl-scopestack-p)
                              (st    vl-lucidstate-p)
                              (ctx   acl2::any-p))
  :returns (new-st vl-lucidstate-p)
  (b* ((st (vl-lucidstate-fix st))
       ((mv item item-ss)
        (vl-scopestack-find-item/ss name ss))
       ((unless item)
        ;; BOZO eventually turn into a proper bad-id warning
        (cw "Warning: missing item ~s0.~%" name)
        st)
       (key (make-vl-lucidkey :item item :scopestack item-ss))
       (occ (make-vl-lucidocc-solo)))
    (vl-lucidstate-mark mtype key occ st ctx)))

;; (define vl-lucid-mark-slice-used ((name  stringp)
;;                                   (left  vl-expr-p)
;;                                   (right vl-expr-p)
;;                                   (ss    vl-scopestack-p)
;;                                   (st    vl-lucidstate-p)
;;                                   (ctx   acl2::any-p))
;;   :returns (new-st vl-lucidstate-p)
;;   (b* ((st (vl-lucidstate-fix st))
;;        ((mv item item-ss)
;;         (vl-scopestack-find-item/ss name ss))
;;        ((unless item)
;;         ;; BOZO eventually turn into a proper bad-id warning
;;         (cw "Warning: missing item ~s0.~%" name)
;;         st)
;;        (key (make-vl-lucidkey :item item :scopestack item-ss))
;;        (occ (make-vl-lucidocc-slice :left (vl-expr-strip left)
;;                                     :right (vl-expr-strip right))))
;;     (vl-lucidstate-mark-used key occ st ctx)))

;; (define vl-lucid-mark-solo-set ((name stringp)
;;                                 (ss   vl-scopestack-p)
;;                                 (st   vl-lucidstate-p)
;;                                 (ctx  acl2::any-p))
;;   :returns (new-st vl-lucidstate-p)
;;   (b* ((st (vl-lucidstate-fix st))
;;        ((mv item item-ss)
;;         (vl-scopestack-find-item/ss name ss))
;;        ((unless item)
;;         ;; BOZO eventually turn into a proper bad-id warning
;;         (cw "Warning: missing item ~s0.~%" name)
;;         st)
;;        (key (make-vl-lucidkey :item item :scopestack item-ss))
;;        (occ (make-vl-lucidocc-solo)))
;;     (vl-lucidstate-mark-set key occ st ctx)))

;; (define vl-lucid-mark-slice-set ((name  stringp)
;;                                   (left  vl-expr-p)
;;                                   (right vl-expr-p)
;;                                   (ss    vl-scopestack-p)
;;                                   (st    vl-lucidstate-p)
;;                                   (ctx   acl2::any-p))
;;   :returns (new-st vl-lucidstate-p)
;;   (b* ((st (vl-lucidstate-fix st))
;;        ((mv item item-ss)
;;         (vl-scopestack-find-item/ss name ss))
;;        ((unless item)
;;         ;; BOZO eventually turn into a proper bad-id warning
;;         (cw "Warning: missing item ~s0.~%" name)
;;         st)
;;        (key (make-vl-lucidkey :item item :scopestack item-ss))
;;        (occ (make-vl-lucidocc-slice :left (vl-expr-strip left)
;;                                     :right (vl-expr-strip right))))
;;     (vl-lucidstate-mark-set key occ st ctx)))

; Marking Phase ---------------------------------------------------------------

; We're going to look up IDs with vl-follow-hidexpr.
; That will give us a trace.

(define vl-normalize-scopestack ((x vl-scopestack-p))
  :returns (new-x vl-scopestack-p)
  :measure (vl-scopestack-count x)
  :verify-guards nil
  (b* ((x (vl-scopestack-fix x)))
    (vl-scopestack-case x
      :null x
      :global x
      :local
      (vl-scopestack-push (if (eq (tag x.top) :vl-module)
                              (vl-module->genblob x.top)
                            x.top)
                          (vl-normalize-scopestack x.super))))
  ///
  (verify-guards vl-normalize-scopestack))

(define vl-hidstep-mark-interfaces ((mtype (member mtype '(:used :set)))
                                    (step  vl-hidstep-p)
                                    (st    vl-lucidstate-p)
                                    (ctx   acl2::any-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((vl-hidstep step))
       ((when (eq (tag step.item) :vl-interfaceport))
        (b* ((key (make-vl-lucidkey
                   :item step.item
                   :scopestack (vl-normalize-scopestack step.ss)))
             (occ (make-vl-lucidocc-solo)))
          (vl-lucidstate-mark mtype key occ st ctx))))
    (vl-lucidstate-fix st)))

(define vl-hidtrace-mark-interfaces ((mtype  (member mtype '(:used :set)))
                                     (trace  vl-hidtrace-p)
                                     (st     vl-lucidstate-p)
                                     (ctx    acl2::any-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((when (atom trace))
        (vl-lucidstate-fix st))
       (st (vl-hidstep-mark-interfaces mtype (car trace) st ctx)))
    (vl-hidtrace-mark-interfaces mtype (cdr trace) st ctx)))

(define vl-hidsolo-mark ((mtype (member mtype '(:used :set)))
                         (hid   vl-expr-p)
                         (ss    vl-scopestack-p)
                         (st    vl-lucidstate-p)
                         (ctx   acl2::any-p))
  :guard (vl-hidexpr-p hid)
  :returns (new-st vl-lucidstate-p)
  ;; BOZO this doesn't mark the indices used in the HID expression!!
  (b* (((mv err trace ?tail) (vl-follow-hidexpr hid ss ctx))
       ((when err)
        (b* (((vl-lucidstate st)))
          (change-vl-lucidstate st :warnings st.warnings)))
       ;; BOZO consider doing more with tail.  For instance:
       ;;   - Should we record the tail into the OCC that we create?  Could we
       ;;     analyze it in any meaningful way?
       ;;   - Should our state somehow record/track the fields of structs?
       ((cons (vl-hidstep step) rest) trace)
       (key (make-vl-lucidkey
             :item step.item
             :scopestack (vl-normalize-scopestack step.ss)))
       (occ (make-vl-lucidocc-solo))
       (st  (vl-hidtrace-mark-interfaces mtype rest st ctx))
       (st  (vl-lucidstate-mark mtype key occ st ctx)))
    st))

(define vl-hidslice-mark ((mtype  (member mtype '(:used :set)))
                          (hid    vl-expr-p)
                          (left   vl-expr-p)
                          (right  vl-expr-p)
                          (ss     vl-scopestack-p)
                          (st     vl-lucidstate-p)
                          (ctx    acl2::any-p))
  :guard (vl-hidexpr-p hid)
  :returns (new-st vl-lucidstate-p)
  ;; BOZO this doesn't mark the indices used in the HID expression!!
  (b* (((mv err trace ?tail) (vl-follow-hidexpr hid ss ctx))
       ((when err)
        (b* (((vl-lucidstate st)))
          (change-vl-lucidstate st :warnings st.warnings)))
       ;; BOZO consider doing more with tail, as in hidsolo-mark.
       ((cons (vl-hidstep step) rest) trace)
       (key (make-vl-lucidkey
             :item step.item
             :scopestack (vl-normalize-scopestack step.ss)))
       (occ (make-vl-lucidocc-slice :left left :right right))
       (st  (vl-hidtrace-mark-interfaces mtype rest st ctx))
       (st  (vl-lucidstate-mark mtype key occ st ctx)))
    st))

(define vl-rhsatom-lucidcheck ((x   vl-expr-p)
                               (ss  vl-scopestack-p)
                               (st  vl-lucidstate-p)
                               (ctx acl2::any-p))
  :guard-hints(("Goal"
                :in-theory (disable tag-when-vl-atomguts-p-forward)
                :use ((:instance tag-when-vl-atomguts-p-forward
                       (x (vl-atom->guts (vl-expr-fix x)))))))
  :guard (vl-atom-p x)
  :returns (new-st vl-lucidstate-p)
  (b* ((x    (vl-expr-fix x))
       (guts (vl-atom->guts x))
       (st   (vl-lucidstate-fix st)))
    (case (tag guts)
      (:vl-funname  (vl-lucid-mark-simple :used (vl-funname->name guts) ss st ctx))
      (:vl-typename (vl-lucid-mark-simple :used (vl-typename->name guts) ss st ctx))
      (:vl-tagname
       ;; BOZO eventually think about how to handle tags.
       st)
      ((:vl-id :vl-hidpiece)
       (progn$ (raise "Should never get here because we should check for hidexpr-p first.")
               st))
      ((:vl-constint :vl-weirdint :vl-extint :vl-string
        :vl-real :vl-keyguts :vl-time :vl-basictype
        :vl-sysfunname)
       ;; Nothing at all to do for any of these
       st)
      (otherwise
       (progn$ (impossible)
               st)))))

(defines vl-rhsexpr-lucidcheck

  (define vl-rhsexpr-lucidcheck ((x   vl-expr-p)
                                 (ss  vl-scopestack-p)
                                 (st  vl-lucidstate-p)
                                 (ctx acl2::any-p))
    :measure (vl-expr-count x)
    :returns (new-st vl-lucidstate-p)
    :verify-guards nil
    :inline nil
    (b* (((when (vl-hidexpr-p x))
          (b* ((st (vl-hidsolo-mark :used x ss st ctx))
               ;; If there are any indices in this expression, then we need to
               ;; perhaps mark identifiers in them as used as well.
               (indices (vl-hidexpr-collect-indices x))
               ((when indices)
                (vl-rhsexprlist-lucidcheck indices ss st ctx)))
            st))

         ((when (vl-atom-p x))
          (vl-rhsatom-lucidcheck x ss st ctx))

         ((vl-nonatom x))
         ((when (and (or (eq x.op :vl-index)
                         (eq x.op :vl-bitselect))
                     ;; BOZO this probably isn't really general enough, i.e.,
                     ;; we might ideally want to deal with things like
                     ;; foo[3][4][5] in some different way.  For now, this
                     ;; should at least mark foo[3].
                     (vl-hidexpr-p (first x.args))))
          (b* (((list from idx) x.args)
               ;; Previous bug: we didn't notice that expressions that were
               ;; only used in index positions were being used.  So, now be
               ;; sure to mark identifiers in the index expression as used.
               (st (vl-hidslice-mark :used from idx idx ss st ctx))
               (st (vl-rhsexpr-lucidcheck idx ss st ctx))
               (st (vl-rhsexprlist-lucidcheck (vl-hidexpr-collect-indices from) ss st ctx)))
            st))

         ((when (and (or (eq x.op :vl-select-colon)
                         (eq x.op :vl-partselect-colon))
                     ;; BOZO as with individual indices, this probably isn't
                     ;; general enough, i.e., we won't deal with foo[5][4:3]
                     ;; or foo[6:5][4:3] in a very sensible way.
                     (vl-hidexpr-p (first x.args))))
          (b* (((list from left right) x.args)
               ;; As in the index case, be sure to mark expressions used in
               ;; the indices.
               (st (vl-hidslice-mark :used from left right ss st ctx))
               (st (vl-rhsexpr-lucidcheck left ss st ctx))
               (st (vl-rhsexpr-lucidcheck right ss st ctx))
               (st (vl-rhsexprlist-lucidcheck (vl-hidexpr-collect-indices from) ss st ctx)))
            st))

         ;; BOZO may eventually wish to specially handle many other operators:
         ;;  - pluscolon, minuscolon, etc.
         ;;  - assignment pattern stuff
         ;;  - tagged operators (recording which tags are used)
         ;;  - streaming concatenation and with operators
         )
      (vl-rhsexprlist-lucidcheck x.args ss st ctx)))

  (define vl-rhsexprlist-lucidcheck ((x   vl-exprlist-p)
                                     (ss  vl-scopestack-p)
                                     (st  vl-lucidstate-p)
                                     (ctx acl2::any-p))
    :measure (vl-exprlist-count x)
    :returns (new-st vl-lucidstate-p)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-rhsexpr-lucidcheck (car x) ss st ctx)))
      (vl-rhsexprlist-lucidcheck (cdr x) ss st ctx)))

  ///
  (verify-guards vl-rhsexpr-lucidcheck$notinline)
  (deffixequiv-mutual vl-rhsexpr-lucidcheck))

(define vl-maybe-rhsexpr-lucidcheck ((x   vl-maybe-expr-p)
                                     (ss  vl-scopestack-p)
                                     (st  vl-lucidstate-p)
                                     (ctx acl2::any-p))
  :returns (new-st vl-lucidstate-p)
  (if x
      (vl-rhsexpr-lucidcheck x ss st ctx)
    (vl-lucidstate-fix st)))


(defines vl-lhsexpr-lucidcheck

  (define vl-lhsexpr-lucidcheck ((x   vl-expr-p)
                                 (ss  vl-scopestack-p)
                                 (st  vl-lucidstate-p)
                                 (ctx acl2::any-p))
    :measure (vl-expr-count x)
    :returns (new-st vl-lucidstate-p)
    :verify-guards nil
    :inline nil
    (b* (((when (vl-hidexpr-p x))
          (b* ((st (vl-hidsolo-mark :set x ss st ctx))
               ;; Subtle.  If there are any indices in this expression, then we
               ;; need to perhaps mark identifiers in them as USED as well.
               ;; For instance, we might be looking at:
               ;;    foo[width-1:0].bar = 0;
               ;; Above we have just marked the declaration for BAR as being set.
               ;; But we also want to mark WIDTH as being USED (not SET) because
               ;; it is being used to choose where to do the write, etc.
               (indices (vl-hidexpr-collect-indices x))
               (st      (vl-rhsexprlist-lucidcheck indices ss st ctx)))
            st))

         ((when (vl-atom-p x))
          ;; ATOM that isn't an identifier in an LHS context?  Probably
          ;; doesn't make sense.  Not going to mark this.
          (vl-lucidstate-fix st))

         ((vl-nonatom x))
         ((when (and (or (eq x.op :vl-index)
                         (eq x.op :vl-bitselect))
                     ;; BOZO this probably isn't really general enough, i.e.,
                     ;; we might ideally want to deal with things like
                     ;; foo[3][4][5] in some different way.  For now, this
                     ;; should at least mark foo[3].
                     (vl-hidexpr-p (first x.args))))
          (b* (((list from idx) x.args)
               ;; We mark FROM as being SET, but we also need to mark anything
               ;; that is used in index expressions as USED.
               (st (vl-hidslice-mark :set from idx idx ss st ctx))
               (st (vl-rhsexpr-lucidcheck idx ss st ctx))
               (st (vl-rhsexprlist-lucidcheck (vl-hidexpr-collect-indices from) ss st ctx)))
            st))

         ((when (and (or (eq x.op :vl-select-colon)
                         (eq x.op :vl-partselect-colon))
                     ;; BOZO as with individual indices, this probably isn't
                     ;; general enough, i.e., we won't deal with foo[5][4:3]
                     ;; or foo[6:5][4:3] in a very sensible way.
                     (vl-hidexpr-p (first x.args))))
          (b* (((list from left right) x.args)
               ;; As above, mark the HID as set but mark the indices as USED.
               (st (vl-hidslice-mark :set from left right ss st ctx))
               (st (vl-rhsexpr-lucidcheck left ss st ctx))
               (st (vl-rhsexpr-lucidcheck right ss st ctx))
               (st (vl-rhsexprlist-lucidcheck (vl-hidexpr-collect-indices from) ss st ctx)))
            st))

         ;; BOZO may wish to specially handle many other operators:
         ;;  - pluscolon, minuscolon, etc.
         ;;  - assignment pattern stuff
         ;;  - tagged operators (recording which tags are used)
         ;;  - streaming concatenation and with operators
         )
      (vl-lhsexprlist-lucidcheck x.args ss st ctx)))

  (define vl-lhsexprlist-lucidcheck ((x   vl-exprlist-p)
                                     (ss  vl-scopestack-p)
                                     (st  vl-lucidstate-p)
                                     (ctx acl2::any-p))
    :measure (vl-exprlist-count x)
    :returns (new-st vl-lucidstate-p)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-lhsexpr-lucidcheck (car x) ss st ctx)))
      (vl-lhsexprlist-lucidcheck (cdr x) ss st ctx)))

  ///
  (verify-guards vl-lhsexpr-lucidcheck$notinline)
  (deffixequiv-mutual vl-lhsexpr-lucidcheck))

(defmacro def-vl-lucidcheck (name &key body (guard 't) takes-ctx)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (type     (mksym 'vl- name '-p))
       (fn       (mksym 'vl- name '-lucidcheck))
       (fix      (mksym 'vl- name '-fix)))
    `(define ,fn ((x ,type)
                  (ss vl-scopestack-p)
                  (st vl-lucidstate-p)
                  ,@(and takes-ctx '((ctx acl2::any-p))))
       :returns (new-st vl-lucidstate-p)
       :guard ,guard
       (b* ((x  (,fix x))
            (ss (vl-scopestack-fix ss))
            (st (vl-lucidstate-fix st)))
         ,body))))

(defmacro def-vl-lucidcheck-list (name &key element takes-ctx)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (type     (mksym 'vl- name '-p))
       (fn       (mksym 'vl- name '-lucidcheck))
       (elem-fn  (mksym 'vl- element '-lucidcheck)))
    `(define ,fn ((x ,type)
                  (ss vl-scopestack-p)
                  (st vl-lucidstate-p)
                  ,@(and takes-ctx '((ctx acl2::any-p))))
       :returns (new-st vl-lucidstate-p)
       (b* (((when (atom x))
             (vl-lucidstate-fix st))
            (st (,elem-fn (car x) ss st ,@(and takes-ctx '(ctx)))))
         (,fn (cdr x) ss st ,@(and takes-ctx '(ctx)))))))

(def-vl-lucidcheck range
  :takes-ctx t
  :body
  (b* (((vl-range x))
       (st (vl-rhsexpr-lucidcheck x.msb ss st ctx))
       (st (vl-rhsexpr-lucidcheck x.lsb ss st ctx)))
    st))

(def-vl-lucidcheck-list rangelist :element range :takes-ctx t)

(def-vl-lucidcheck maybe-range
  :takes-ctx t
  :body
  (if x
      (vl-range-lucidcheck x ss st ctx)
    st))

(def-vl-lucidcheck packeddimension
  :takes-ctx t
  :body
  (if (eq x :vl-unsized-dimension)
      st
    (vl-range-lucidcheck x ss st ctx)))

(def-vl-lucidcheck-list packeddimensionlist :element packeddimension :takes-ctx t)

(def-vl-lucidcheck maybe-packeddimension
  :takes-ctx t
  :body
  (if x
      (vl-packeddimension-lucidcheck x ss st ctx)
    st))

(def-vl-lucidcheck enumbasekind
  :takes-ctx t
  :body
  (if (stringp x)
      ;; Type name like foo_t, so mark foo_t as a used type.
      (vl-lucid-mark-simple :used x ss st ctx)
    st))

(def-vl-lucidcheck enumbasetype
  :takes-ctx t
  :body
  (b* (((vl-enumbasetype x))
       (st (vl-enumbasekind-lucidcheck x.kind ss st ctx))
       (st (vl-maybe-packeddimension-lucidcheck x.dim ss st ctx)))
    st))

(def-vl-lucidcheck enumitem
  :takes-ctx t
  :body
  (b* (((vl-enumitem x))
       ;; BOZO what are the scoping rules for enum items?  We may need to mark
       ;; their names as set.  But probably for any of this to work we would
       ;; need scopestack to understand enum items, etc...
       (st (vl-maybe-range-lucidcheck x.range ss st ctx))
       (st (vl-maybe-rhsexpr-lucidcheck x.value ss st ctx)))
    st))

(def-vl-lucidcheck-list enumitemlist :element enumitem :takes-ctx t)

(defines vl-datatype-lucidcheck

  (define vl-datatype-lucidcheck ((x vl-datatype-p)
                                  (ss  vl-scopestack-p)
                                  (st  vl-lucidstate-p)
                                  (ctx acl2::any-p))
    :returns (st vl-lucidstate-p)
    :measure (vl-datatype-count x)
    :verify-guards nil
    (b* ((st (vl-lucidstate-fix st)))
      (vl-datatype-case x
        :vl-coretype
        (b* ((st (vl-packeddimensionlist-lucidcheck x.pdims ss st ctx))
             (st (vl-packeddimensionlist-lucidcheck x.udims ss st ctx)))
          st)

        :vl-struct
        (b* ((st (vl-packeddimensionlist-lucidcheck x.pdims ss st ctx))
             (st (vl-packeddimensionlist-lucidcheck x.udims ss st ctx)))
          (vl-structmemberlist-lucidcheck x.members ss st ctx))

        :vl-union
        (b* ((st (vl-packeddimensionlist-lucidcheck x.pdims ss st ctx))
             (st (vl-packeddimensionlist-lucidcheck x.udims ss st ctx)))
          (vl-structmemberlist-lucidcheck x.members ss st ctx))

        :vl-enum
        (b* ((st (vl-enumbasetype-lucidcheck x.basetype ss st ctx))
             (st (vl-enumitemlist-lucidcheck x.items ss st ctx))
             (st (vl-packeddimensionlist-lucidcheck x.pdims ss st ctx))
             (st (vl-packeddimensionlist-lucidcheck x.udims ss st ctx)))
          st)

        :vl-usertype
        (b* ((st (vl-rhsexpr-lucidcheck x.kind ss st ctx))
             (st (vl-packeddimensionlist-lucidcheck x.pdims ss st ctx))
             (st (vl-packeddimensionlist-lucidcheck x.udims ss st ctx)))
          st))))

  (define vl-structmember-lucidcheck ((x   vl-structmember-p)
                                      (ss  vl-scopestack-p)
                                      (st  vl-lucidstate-p)
                                      (ctx acl2::any-p))
    :returns (st vl-lucidstate-p)
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x))
         (st (vl-lucidstate-fix st))
         (st (vl-datatype-lucidcheck x.type ss st ctx))
         (st (vl-maybe-rhsexpr-lucidcheck x.rhs ss st ctx)))
      st))

  (define vl-structmemberlist-lucidcheck ((x   vl-structmemberlist-p)
                                          (ss  vl-scopestack-p)
                                          (st  vl-lucidstate-p)
                                          (ctx acl2::any-p))
    :returns (st vl-lucidstate-p)
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-structmember-lucidcheck (car x) ss st ctx)))
      (vl-structmemberlist-lucidcheck (cdr x) ss st ctx)))

  ///
  (verify-guards vl-datatype-lucidcheck)
  (deffixequiv-mutual vl-datatype-lucidcheck))

(def-vl-lucidcheck delaycontrol
  :takes-ctx t
  :body
  (b* (((vl-delaycontrol x)))
    (vl-rhsexpr-lucidcheck x.value ss st ctx)))

(def-vl-lucidcheck evatom
  :takes-ctx t
  :body
  (b* (((vl-evatom x)))
    (vl-rhsexpr-lucidcheck x.expr ss st ctx)))

(def-vl-lucidcheck-list evatomlist :element evatom :takes-ctx t)

(def-vl-lucidcheck eventcontrol
  :takes-ctx t
  :body
  (b* (((vl-eventcontrol x)))
    (vl-evatomlist-lucidcheck x.atoms ss st ctx)))

(def-vl-lucidcheck repeateventcontrol
  :takes-ctx t
  :body
  (b* (((vl-repeateventcontrol x))
       (st (vl-rhsexpr-lucidcheck x.expr ss st ctx))
       (st (vl-eventcontrol-lucidcheck x.ctrl ss st ctx)))
    st))

(def-vl-lucidcheck delayoreventcontrol
  :takes-ctx t
  :body
  (case (tag x)
    (:vl-delaycontrol (vl-delaycontrol-lucidcheck x ss st ctx))
    (:vl-eventcontrol (vl-eventcontrol-lucidcheck x ss st ctx))
    (otherwise        (vl-repeateventcontrol-lucidcheck x ss st ctx))))

(def-vl-lucidcheck maybe-delayoreventcontrol
  :takes-ctx t
  :body
  (if x
      (vl-delayoreventcontrol-lucidcheck x ss st ctx)
    st))

(def-vl-lucidcheck gatedelay
  :takes-ctx t
  :body
  (b* (((vl-gatedelay x))
       (st (vl-rhsexpr-lucidcheck x.rise ss st ctx))
       (st (vl-rhsexpr-lucidcheck x.fall ss st ctx))
       (st (vl-maybe-rhsexpr-lucidcheck x.rise ss st ctx)))
    st))

(def-vl-lucidcheck maybe-gatedelay
  :takes-ctx t
  :body
  (if x
      (vl-gatedelay-lucidcheck x ss st ctx)
    st))

(def-vl-lucidcheck paramdecl
  :body
  (b* (((vl-paramdecl x)))
    (vl-paramtype-case x.type
      (:vl-implicitvalueparam
       (b* (((unless x.type.default)
             ;; No initial value, nothing to do.
             st)
            ;; Initial value, so the parameter itself is set.
            ;; Furthermore, we also need to mark the variables that are
            ;; used in the initial value expression as being used.
            (st (vl-lucid-mark-simple :set x.name ss st x))
            (st (vl-rhsexpr-lucidcheck x.type.default ss st x)))
         st))
      (:vl-explicitvalueparam
       (b* ((st (vl-datatype-lucidcheck x.type.type ss st x))
            ((unless x.type.default)
             st)
            (st (vl-lucid-mark-simple :set x.name ss st x))
            (st (vl-rhsexpr-lucidcheck x.type.default ss st x)))
         st))
      (:vl-typeparam
       (b* (((unless x.type.default)
             st)
            (st (vl-lucid-mark-simple :set x.name ss st x))
            (st (vl-datatype-lucidcheck x.type.default ss st x)))
         st)))))

(def-vl-lucidcheck-list paramdecllist :element paramdecl)

(def-vl-lucidcheck vardecl
  :body
  (b* (((vl-vardecl x))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st x))
       (st (vl-datatype-lucidcheck x.type ss st x))
       (st (if x.initval
               ;; Initial value, so this variable is set and we also need to
               ;; mark all variables used in the rhs as being used.
               (b* ((st (vl-rhsexpr-lucidcheck x.initval ss st x))
                    (st (vl-lucid-mark-simple :set x.name ss st x)))
                 st)
             st)))
    st))

(def-vl-lucidcheck-list vardecllist :element vardecl)

(def-vl-lucidcheck blockitem
  :body
  (case (tag x)
    (:vl-vardecl (vl-vardecl-lucidcheck x ss st))
    (otherwise   (vl-paramdecl-lucidcheck x ss st))))

(def-vl-lucidcheck-list blockitemlist :element blockitem)

(defines vl-stmt-lucidcheck

  (define vl-stmt-lucidcheck ((x   vl-stmt-p)
                              (ss  vl-scopestack-p)
                              (st  vl-lucidstate-p)
                              (ctx acl2::any-p))
    :returns (new-st vl-lucidstate-p)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (b* ((x  (vl-stmt-fix x))
         (st (vl-lucidstate-fix st)))
      (vl-stmt-case x

        :vl-nullstmt
        st

        :vl-assignstmt
        (b* ((st (vl-lhsexpr-lucidcheck x.lvalue ss st ctx))
             (st (vl-rhsexpr-lucidcheck x.expr ss st ctx))
             (st (vl-maybe-delayoreventcontrol-lucidcheck x.ctrl ss st ctx)))
          st)

        :vl-deassignstmt
        ;; It isn't really clear what to do here.  In some sense, the
        ;; expression being deassigned ought to sort of be an lvalue.  But it
        ;; doesn't really make sense to regard a deassignment as "setting" the
        ;; variable.  It also doesn't really make sense to regard it as "using"
        ;; the variable.  I think for now I'm just not going to do anything at
        ;; all with deassignment statements.
        st

        :vl-enablestmt
        ;; Typically this should be naming an task.  We'll treat the is as a
        ;; right hand side so that it gets marked as "used".  Arguments to the
        ;; task will also be marked as used.  BOZO this maybe isn't quite right
        ;; -- if the task has outputs then maybe we need to be marking them as
        ;; set instead of used??
        (b* ((st (vl-rhsexpr-lucidcheck x.id ss st ctx))
             (st (vl-rhsexprlist-lucidcheck x.args ss st ctx)))
          st)

        :vl-disablestmt
        ;; This is a little bit like the deassignment case.  It isn't really
        ;; clear whether we should regard tasks that are being disabled as
        ;; used.  I think for now we'll just ignore them.
        st

        :vl-eventtriggerstmt
        ;; I think this is similar to the enable case?
        (b* ((st (vl-rhsexpr-lucidcheck x.id ss st ctx)))
          st)

        :vl-casestmt
        (b* ((st (vl-rhsexpr-lucidcheck x.test ss st ctx))
             (st (vl-caselist-lucidcheck x.caselist ss st ctx))
             (st (vl-stmt-lucidcheck x.default ss st ctx)))
          st)

        :vl-ifstmt
        (b* ((st (vl-rhsexpr-lucidcheck x.condition ss st ctx))
             (st (vl-stmt-lucidcheck x.truebranch ss st ctx))
             (st (vl-stmt-lucidcheck x.falsebranch ss st ctx)))
          st)

        :vl-foreverstmt
        (b* ((st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-waitstmt
        (b* ((st (vl-rhsexpr-lucidcheck x.condition ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-whilestmt
        (b* ((st (vl-rhsexpr-lucidcheck x.condition ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-forstmt
        (b* ((st (vl-vardecllist-lucidcheck x.initdecls ss st))
             (st (vl-stmtlist-lucidcheck x.initassigns ss st ctx))
             (st (vl-rhsexpr-lucidcheck x.test ss st ctx))
             (st (vl-stmtlist-lucidcheck x.stepforms ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-repeatstmt
        (b* ((st (vl-rhsexpr-lucidcheck x.condition ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-timingstmt
        (b* ((st (vl-delayoreventcontrol-lucidcheck x.ctrl ss st ctx))
             (st (vl-stmt-lucidcheck x.body ss st ctx)))
          st)

        :vl-blockstmt
        (b* ((ss
              ;; NOTE -- this must be kept in sync with vl-stmt-luciddb-init!
              (if (consp (vl-blockstmt->decls x))
                  (vl-scopestack-push (vl-blockstmt->blockscope x) ss)
                ss))
             (st (vl-blockitemlist-lucidcheck x.decls ss st))
             (st (vl-stmtlist-lucidcheck x.stmts ss st ctx)))
          st))))

  (define vl-stmtlist-lucidcheck ((x   vl-stmtlist-p)
                                  (ss  vl-scopestack-p)
                                  (st  vl-lucidstate-p)
                                  (ctx acl2::any-p))
    :returns (new-st vl-lucidstate-p)
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-stmt-lucidcheck (car x) ss st ctx)))
      (vl-stmtlist-lucidcheck (cdr x) ss st ctx)))

  (define vl-caselist-lucidcheck ((x  vl-caselist-p)
                                  (ss vl-scopestack-p)
                                  (st vl-lucidstate-p)
                                  (ctx acl2::any-p))
    :returns (new-st vl-lucidstate-p)
    :measure (vl-caselist-count x)
    (b* ((x (vl-caselist-fix x))
         ((when (atom x))
          (vl-lucidstate-fix st))
         ((cons exprs stmt) (car x))
         ;; Treat the match expressions like right-hand sides because they are
         ;; being read but not assigned to.
         (st (vl-rhsexprlist-lucidcheck exprs ss st ctx))
         (st (vl-stmt-lucidcheck stmt ss st ctx)))
      (vl-caselist-lucidcheck (cdr x) ss st ctx)))
  ///
  (verify-guards vl-stmt-lucidcheck)
  (deffixequiv-mutual vl-stmt-lucidcheck))

(def-vl-lucidcheck always
  :body
  (b* (((vl-always x)))
    (vl-stmt-lucidcheck x.stmt ss st x)))

(def-vl-lucidcheck-list alwayslist :element always)

(def-vl-lucidcheck initial
  :body
  (b* (((vl-initial x)))
    (vl-stmt-lucidcheck x.stmt ss st x)))

(def-vl-lucidcheck-list initiallist :element initial)

(def-vl-lucidcheck portdecl
  :body
  (b* (((vl-portdecl x))
       (st (vl-datatype-lucidcheck x.type ss st x)))
    (case x.dir
      (:vl-input
       ;; We "pretend" that input ports are set because they ought to be set by
       ;; the superior module, function call, or task invocation.
       (vl-lucid-mark-simple :set x.name ss st x))
      (:vl-output
       ;; We "pretend" that output ports are used because they ought to be used
       ;; the superior module, function call, or task invocation.
       (vl-lucid-mark-simple :used x.name ss st x))
      (:vl-inout
       ;; We don't pretend that inout ports are used or set, because they ought
       ;; to be both used and set within the submodule at some point in time.
       ;; (Otherwise they may as well be just an input or just an output.)
       st))))

(def-vl-lucidcheck-list portdecllist :element portdecl)

(def-vl-lucidcheck interfaceport
  ;; Unlike regular ports, I think we want to not mark an interface port as
  ;; being used or set.  The smarts for an interface port will mostly be in our
  ;; reporting code.  If the thing is never used or set anywhere at all, we'll
  ;; not report it as an error.  But it's perfectly OK for a module to only
  ;; read from an interface, or to only write to it.
  :body
  (b* (((vl-interfaceport x))
       (st (vl-packeddimensionlist-lucidcheck x.udims ss st x))
       ;; BOZO maybe mark the IFNAME as used?
       )
    st))

(def-vl-lucidcheck-list interfaceportlist :element interfaceport)

(def-vl-lucidcheck fundecl
  ;; We mark input ports as SET and output ports as USED since otherwise we
  ;; could end up thinking that inputs aren't set, which would be silly.  We
  ;; also mark the return value as being USED, since it is "used" by whoever
  ;; calls the function.
  :body
  (b* (((vl-fundecl x))
       (st (vl-datatype-lucidcheck x.rettype ss st x))
       ;; Subtle.  Before pushing the function's scope, we mark it as "set".
       ;; This doesn't make a whole lot of sense: what does it mean for a
       ;; function to be set?  But if we regard it as meaning, "it has a
       ;; defined value", then the very act of defining the function is kind of
       ;; like setting it.
       (st    (vl-lucid-mark-simple :set x.name ss st x))
       (scope (vl-fundecl->blockscope x))
       (ss    (vl-scopestack-push scope ss))
       ;; Now that we've pushed the function scope, mark the function's name
       ;; (i.e., the return value) as used, because we're imagining that it
       ;; is "used" by whoever calls the function.
       (st    (vl-lucid-mark-simple :used x.name ss st x))
       ;; Mark all inputs to the function as set, because we're imagining
       ;; that they're set by the caller.
       (st    (vl-portdecllist-lucidcheck x.portdecls ss st))
       (st    (vl-blockitemlist-lucidcheck x.decls ss st)))
    (vl-stmt-lucidcheck x.body ss st x)))

(def-vl-lucidcheck-list fundecllist :element fundecl)

(def-vl-lucidcheck taskdecl
  :body
  (b* (((vl-taskdecl x))
       ;; Subtle.  Mark the task itself as set.  See comments in fundecl
       ;; handling for an explanation.
       (st    (vl-lucid-mark-simple :set x.name ss st x))
       (scope (vl-taskdecl->blockscope x))
       (ss    (vl-scopestack-push scope ss))
       (st    (vl-portdecllist-lucidcheck x.portdecls ss st))
       (st    (vl-blockitemlist-lucidcheck x.decls ss st)))
    (vl-stmt-lucidcheck x.body ss st x)))

(def-vl-lucidcheck-list taskdecllist :element taskdecl)

(def-vl-lucidcheck assign
  :body
  (b* (((vl-assign x))
       (st (vl-lhsexpr-lucidcheck x.lvalue ss st x))
       (st (vl-rhsexpr-lucidcheck x.expr ss st x))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st x)))
    st))

(def-vl-lucidcheck-list assignlist :element assign)

(def-vl-lucidcheck typedef
  :body
  (b* (((vl-typedef x))
       (st (vl-lucid-mark-simple :set x.name ss st x))
       (st (vl-datatype-lucidcheck x.type ss st x)))
    st))

(def-vl-lucidcheck-list typedeflist :element typedef)

(def-vl-lucidcheck plainarg
  :takes-ctx t
  :body
  (b* (((vl-plainarg x))
       ((unless x.expr)
        st))
    (case x.dir
      (:vl-input
       ;; Inputs are like RHSes, they're used not set.
       (vl-rhsexpr-lucidcheck x.expr ss st ctx))
      (:vl-output
       ;; Outputs are like LHSes, they're set not used.
       (vl-lhsexpr-lucidcheck x.expr ss st ctx))
      (otherwise
       ;; INOUT or interface port or error computing direction: treat it as if
       ;; it were both used and set.  BOZO maybe we should cause an error if
       ;; not determined?
       (b* ((st (vl-rhsexpr-lucidcheck x.expr ss st ctx))
            (st (vl-lhsexpr-lucidcheck x.expr ss st ctx)))
         st)))))

(def-vl-lucidcheck-list plainarglist :element plainarg :takes-ctx t)

(def-vl-lucidcheck gateinst
  :body
  (b* (((vl-gateinst x))
       (st (vl-maybe-range-lucidcheck x.range ss st x))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st x))
       (st (vl-plainarglist-lucidcheck x.args ss st x)))
    st))

(def-vl-lucidcheck-list gateinstlist :element gateinst)


; Parameter value lists like #(width = 1).  These are all like right-hand side uses.

(def-vl-lucidcheck paramvalue
  :takes-ctx t
  :body (if (vl-paramvalue-expr-p x)
            (vl-rhsexpr-lucidcheck x ss st ctx)
          (vl-datatype-lucidcheck x ss st ctx)))

(def-vl-lucidcheck-list paramvaluelist :element paramvalue :takes-ctx t)

(def-vl-lucidcheck maybe-paramvalue
  :takes-ctx t
  :body (if x
            (vl-paramvalue-lucidcheck x ss st ctx)
          st))

(def-vl-lucidcheck namedparamvalue
  :takes-ctx t
  :body (b* (((vl-namedparamvalue x)))
          (vl-maybe-paramvalue-lucidcheck x.value ss st ctx)))

(def-vl-lucidcheck-list namedparamvaluelist :element namedparamvalue :takes-ctx t)

(def-vl-lucidcheck paramargs
  :takes-ctx t
  :body
  (vl-paramargs-case x
    (:vl-paramargs-named
     (vl-namedparamvaluelist-lucidcheck x.args ss st ctx))
    (:vl-paramargs-plain
     (vl-paramvaluelist-lucidcheck x.args ss st ctx))))


; Port lists.  These are tricky because they can be inputs or outputs or undetermined.

(def-vl-lucidcheck namedarg
  ;; HACK.  We treat named args as if they were inouts, which will possibly
  ;; under-report things but shouldn't cause spurious warnings.
  :takes-ctx t
  :body
  (b* (((vl-namedarg x))
       ((unless x.expr)
        st)
       (st (vl-rhsexpr-lucidcheck x.expr ss st ctx))
       (st (vl-lhsexpr-lucidcheck x.expr ss st ctx)))
    st))

(def-vl-lucidcheck-list namedarglist :element namedarg :takes-ctx t)

(def-vl-lucidcheck arguments
  :takes-ctx t
  :body
  (vl-arguments-case x
    :vl-arguments-plain
    (vl-plainarglist-lucidcheck x.args ss st ctx)
    :vl-arguments-named
    (vl-namedarglist-lucidcheck x.args ss st ctx)))

(def-vl-lucidcheck modinst
  :body
  (b* (((vl-modinst x))
       (st (vl-maybe-range-lucidcheck x.range ss st x))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st x))
       (st (vl-paramargs-lucidcheck x.paramargs ss st x))
       (st (vl-arguments-lucidcheck x.portargs ss st x)))
    st))

(def-vl-lucidcheck-list modinstlist :element modinst)




;; (defines vl-genblob-lucidcheck
;;   ;; I had originally tried to use vl-genblob-transform here.  However, that
;;   ;; doesn't seem sufficient to deal with things like, e.g.,
;;   ;;
;;   ;;    if (condition)
;;   ;;    assign foo = bar;
;;   ;;
;;   ;; Because we need to regard things like <condition> as being used here, and
;;   ;; that just isn't anything that def-genblob-transform is going to be
;;   ;; exposing to us.
;;   (define vl-genblob-lucidcheck ((x vl-genblob-p)
;;                                  (ss vl-scopestack-p)
;;                                  (st vl-lucidstate-p))
;;     :returns (st vl-lucidstate-p)
;;     :measure (vl-genblob-count x)
;;     :verify-guards nil
;;     (b* (((vl-genblob x) (vl-genblob-fix x))
;;          (ss (vl-scopestack-push x ss))
;;          (st (vl-portdecllist-lucidcheck x.portdecls ss st))
;;          (st (vl-assignlist-lucidcheck x.assigns ss st))
;;          ;; BOZO aliases?
;;          (st (vl-vardecllist-lucidcheck x.vardecls ss st))
;;          (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
;;          (st (vl-fundecllist-lucidcheck x.fundecls ss st))
;;          (st (vl-taskdecllist-lucidcheck x.taskdecls ss st))
;;          (st (vl-modinstlist-lucidcheck x.modinsts ss st))
;;          (st (vl-gateinstlist-lucidcheck x.gateinsts ss st))
;;          (st (vl-alwayslist-lucidcheck x.alwayses ss st))
;;          (st (vl-initiallist-lucidcheck x.initials ss st))
;;          (st (vl-typedeflist-lucidcheck x.typedefs ss st))
;;          ;; Imports -- BOZO?  Mark packages as used?
;;          ;; Fwdtypedefs -- I think it's fine to ignore these
;;          ;; Modports -- BOZO? weird to have these anyway?
;;          (st (vl-generates-lucidcheck x.generates ss st))
;;          ;; Ports -- BOZO?  What do we want to do with these?
;;          )
;;       st))

;;   (define vl-generates-lucidcheck ((x  vl-genelementlist-p)
;;                                    (ss vl-scopestack-p)
;;                                    (st vl-lucidstate-p))
;;     :returns (st vl-lucidstate-p)
;;     :measure (vl-genblob-generates-count x)
;;     (b* (((when (atom x))
;;           (vl-lucidstate-fix st))
;;          (st (vl-genblob-lucidcheck-generate (car x) ss st)))
;;       (vl-generates-lucidcheck (cdr x) ss st)))

;;   (define vl-genblob-lucidcheck-generate ((x vl-genelement-p)
;;                                           (ss vl-scopestack-p)
;;                                           (st vl-lucidstate-p))
;;     :returns (st vl-lucidstate-p)
;;     :measure (vl-genblob-generate-count x)
;;     (vl-genelement-case x
;;       :vl-genloop
      

;;       :vl-genif   ...
;;       :vl-gencase ...
;;       :vl-genblock (vl-genblob-lucidcheck-elementlist x.elems ss st)
;;       :vl-genarray (vl-genblob-lucidcheck-genarrayblocklist x.blocks ss st)
;;       :vl-genbase  ...))

;;   (define vl-genblob-lucidcheck-elementlist ((x vl-genelementlist-p)
;;                                              (ss vl-scopestack-p)
;;                                              (st vl-lucidstate-p))
;;     :returns (st vl-lucidstate-p)
;;     :measure (vl-genblob-elementlist-count x)
;;     (vl-genblob-lucidcheck (vl-sort-genelements x) ss st))

;;   (define vl-genblob-lucidcheck-genarrayblocklist ((x vl-genarrayblocklist-p)
;;                                                    (ss vl-scopestack-p)
;;                                                    (st vl-lucidstate-p))
;;     :returns (st vl-lucidstate-p)
;;     :measure (vl-genblob-genarrayblocklist-count x)
;;     (b* (((when (atom x))
;;           (vl-lucidstate-fix st))
;;          ((maybe-mv st first)
;;           (vl-genblob-lucidcheck-genarrayblock (car x)
;;                                                ss st))
;;          ((maybe-mv st rest)
;;                (vl-genblob-lucidcheck-genarrayblocklist (cdr x)
;;                                                         ss st)))
;;              (maybe-mv st (cons first rest))))
;;  (define vl-genblob-lucidcheck-genarrayblock
;;          ((x vl-genarrayblock-p)
;;           (ss vl-scopestack-p)
;;           (st vl-lucidstate-p))
;;          :returns
;;          (mv (st vl-lucidstate-p)
;;              (new-x vl-genarrayblock-p))
;;          :measure
;;          (vl-genblob-genarrayblock-count x)
;;          (b* (((vl-genarrayblock x))
;;               ((maybe-mv st new-elems)
;;                (vl-genblob-lucidcheck-elementlist x.elems ss st)))
;;              (maybe-mv st
;;                        (change-vl-genarrayblock x
;;                                                 :elems new-elems))))
;;  ///
;;  (local (in-theory (disable vl-genblob-lucidcheck-genarrayblock
;;                             vl-genblob-lucidcheck-genarrayblocklist
;;                             vl-genblob-lucidcheck-elementlist
;;                             vl-genblob-lucidcheck-generate
;;                             vl-generates-lucidcheck
;;                             vl-genblob-lucidcheck)))
;;  (verify-guards vl-genblob-lucidcheck
;;                 :hints nil)
;;  (deffixequiv-mutual
;;       vl-genblob-lucidcheck
;;       :hints ((and stable-under-simplificationp
;;                    (std::expand-calls-computed-hint
;;                         clause
;;                         '(vl-genblob-lucidcheck-genarrayblock
;;                               vl-genblob-lucidcheck-genarrayblocklist
;;                               vl-genblob-lucidcheck-elementlist
;;                               vl-genblob-lucidcheck-generate
;;                               vl-generates-lucidcheck
;;                               vl-genblob-lucidcheck))))))

(def-genblob-transform vl-genblob-lucidcheck ((ss vl-scopestack-p)
                                              (st vl-lucidstate-p))
  ;; BOZO I don't really understand what this is doing or whether it's right.
  ;; For instance how does this handle arrays?
  :returns ((st vl-lucidstate-p))
  (b* (((vl-genblob x)     (vl-genblob-fix x))
       (ss                 (vl-scopestack-push x ss))
       ((mv st ?generates) (vl-generates-lucidcheck x.generates ss st))

       (st (vl-assignlist-lucidcheck    x.assigns    ss st))
       (st (vl-alwayslist-lucidcheck    x.alwayses   ss st))
       (st (vl-initiallist-lucidcheck   x.initials   ss st))
       (st (vl-fundecllist-lucidcheck   x.fundecls   ss st))
       (st (vl-taskdecllist-lucidcheck  x.taskdecls  ss st))
       (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
       (st (vl-vardecllist-lucidcheck   x.vardecls   ss st))
       (st (vl-portdecllist-lucidcheck  x.portdecls  ss st))
       (st (vl-typedeflist-lucidcheck   x.typedefs   ss st))
       (st (vl-gateinstlist-lucidcheck  x.gateinsts  ss st))
       (st (vl-modinstlist-lucidcheck   x.modinsts   ss st))
       (st (vl-interfaceportlist-lucidcheck x.ifports ss st))
       ;; BOZO aliases, modports??, typedefs ...
       )
    (mv st x))
  :apply-to-generates vl-generates-lucidcheck)

(def-vl-lucidcheck module
  :body
  (b* (((vl-module x))
       (genblob (vl-module->genblob x))
       ((mv st ?new-x) (vl-genblob-lucidcheck genblob ss st)))
    st))

(def-vl-lucidcheck-list modulelist :element module)


(def-vl-lucidcheck package
  :body
  (b* (((vl-package x))
       (ss (vl-scopestack-push x ss))
       (st (vl-fundecllist-lucidcheck x.fundecls ss st))
       (st (vl-taskdecllist-lucidcheck x.taskdecls ss st))
       (st (vl-typedeflist-lucidcheck x.typedefs ss st))
       (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
       (st (vl-vardecllist-lucidcheck x.vardecls ss st)))
    st))

(def-vl-lucidcheck-list packagelist :element package)

(def-vl-lucidcheck interface
  :body
  (b* (((vl-interface x))
       (ss (vl-scopestack-push x ss))
       (st (vl-portdecllist-lucidcheck  x.portdecls  ss st))
       (st (vl-vardecllist-lucidcheck   x.vardecls   ss st))
       (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
       ;; bozo do something with modports?
       ;; bozo generates
       )
    st))

(def-vl-lucidcheck-list interfacelist :element interface)

(define vl-design-lucidcheck-main ((x  vl-design-p)
                                   (ss vl-scopestack-p)
                                   (st vl-lucidstate-p))
  :returns (new-st vl-lucidstate-p)
  :ignore-ok t
  :irrelevant-formals-ok t
  (b* (((vl-design x))
       (st (vl-modulelist-lucidcheck x.mods ss st))
       (st (vl-fundecllist-lucidcheck x.fundecls ss st))
       (st (vl-taskdecllist-lucidcheck x.taskdecls ss st))
       (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
       (st (vl-vardecllist-lucidcheck x.vardecls ss st))
       (st (vl-typedeflist-lucidcheck x.typedefs ss st))
       (st (vl-packagelist-lucidcheck x.packages ss st))
       (st (vl-interfacelist-lucidcheck x.interfaces ss st))
       ;; bozo programs, configs, udps, ...
       )
    st))

; Analysis of Marks -----------------------------------------------------------

(define vl-scopestack-top-level-name ((ss vl-scopestack-p))
  :returns (name maybe-stringp :rule-classes :type-prescription)
  :measure (vl-scopestack-count ss)
  (vl-scopestack-case ss
    :null nil
    :global nil
    :local
    (or (vl-scopestack-top-level-name ss.super)
        (vl-scope->name ss.top))))

(define vl-lucid-some-solo-occp ((x vl-lucidocclist-p))
  :returns (solop booleanp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (or (eq (vl-lucidocc-kind (car x)) :solo)
        (vl-lucid-some-solo-occp (cdr x)))))


;; Performance BOZO - we would probably be better off using something like
;; sparse bitsets here, but that would require developing something like
;; nats-from that produces a sparse bitset.  That's fine but might take an hour
;; or two of work.


(define vl-fast-range-p ((x vl-packeddimension-p))
  :prepwork ((local (in-theory (enable vl-packeddimension-p))))
  :hooks nil
  :inline t
  (mbe :logic (vl-range-p x)
       :exec (not (eq x :vl-unsized-dimension))))

(define vl-lucid-range->bits ((x vl-range-p))
  :guard (vl-range-resolved-p x)
  :returns (bits (and (nat-listp bits)
                      (setp bits)))
  (b* (((vl-range x))
       (msb (vl-resolved->val x.msb))
       (lsb (vl-resolved->val x.lsb))
       (min (min msb lsb))
       (max (max msb lsb)))
    ;; We add one to max because nats-from enumerates [a, b)
    (nats-from min (+ 1 max))))

(deflist vl-lucid-all-slices-p (x)
  :guard (vl-lucidocclist-p x)
  (eq (vl-lucidocc-kind x) :slice))

(define vl-lucid-resolved-slice-p ((x vl-lucidocc-p))
  :guard (equal (vl-lucidocc-kind x) :slice)
  :returns (resolvedp booleanp :rule-classes :type-prescription)
  (b* (((vl-lucidocc-slice x)))
    (and (vl-expr-resolved-p x.left)
         (vl-expr-resolved-p x.right))))

(define vl-lucid-resolved-slice->bits ((x vl-lucidocc-p))
  :guard (and (equal (vl-lucidocc-kind x) :slice)
              (vl-lucid-resolved-slice-p x))
  :returns (indices (and (nat-listp indices)
                         (setp indices)))
  :prepwork ((local (in-theory (enable vl-lucid-resolved-slice-p))))
  (b* (((vl-lucidocc-slice x))
       (msb (vl-resolved->val x.left))
       (lsb (vl-resolved->val x.right))
       (min (min msb lsb))
       (max (max msb lsb)))
    ;; We add one to max because nats-from enumerates [a, b)
    (nats-from min (+ 1 max))))

(deflist vl-lucid-all-slices-resolved-p (x)
  :guard (and (vl-lucidocclist-p x)
              (vl-lucid-all-slices-p x))
  (vl-lucid-resolved-slice-p x))

(define vl-lucid-resolved-slices->bits ((x vl-lucidocclist-p))
  :guard (and (vl-lucid-all-slices-p x)
              (vl-lucid-all-slices-resolved-p x))
  :returns (indices (and (nat-listp indices)
                         (setp indices)))
  (if (atom x)
      nil
    (union (vl-lucid-resolved-slice->bits (car x))
           (vl-lucid-resolved-slices->bits (cdr x)))))

(define vl-lucid-valid-bits-for-datatype ((x  vl-datatype-p)
                                          (ss vl-scopestack-p))
  :returns (mv (simple-p booleanp :rule-classes :type-prescription)
               (bits     (and (nat-listp bits)
                              (setp bits))))
  (b* (((mv warning x) (vl-datatype-usertype-elim x ss 1000))
       ((when warning)
        ;; Some kind of error resolving the user-defined data types, let's
        ;; not try to analyze this at all.
        (mv nil nil)))
    (vl-datatype-case x
      (:vl-coretype
       (case x.name
         ((:vl-logic :vl-reg :vl-bit)
          ;; Integer vector types.  We'll support one packed dimension here,
          ;; i.e., we're looking for things like wire [3:0] w;
          (b* (((when (consp x.udims))
                (mv nil nil))
               ((when (atom x.pdims))
                ;; No packed or unpacked dimensions.  Single bit.
                (mv t '(0)))
               ((unless (and (atom (cdr x.pdims))
                             (vl-fast-range-p (first x.pdims))
                             (vl-range-resolved-p (first x.pdims))))
                ;; Too many or unresolved dimensions -- too hard.
                (mv nil nil)))
            (mv t (vl-lucid-range->bits (first x.pdims)))))

         ((:vl-byte :vl-shortint :vl-int :vl-longint :vl-integer :vl-time)
          ;; Integer atom types.  If there aren't any dimensions then it still
          ;; makes sense to treat them as bits.
          (if (or (consp x.pdims)
                  (consp x.udims))
              (mv nil nil)
            (case x.name
              (:vl-byte     (mv t (nats-from 0 8)))
              (:vl-shortint (mv t (nats-from 0 16)))
              (:vl-int      (mv t (nats-from 0 32)))
              (:vl-longint  (mv t (nats-from 0 64)))
              (:vl-integer  (mv t (nats-from 0 32)))
              (:vl-time     (mv t (nats-from 0 64)))
              (otherwise    (mv (impossible) nil)))))

         (otherwise
          ;; Something trickier like a string, c handle, event, void, real, etc.
          ;; Too hard, don't consider it.
          (mv nil nil))))
      (:vl-struct
       ;; Probably don't want to deal with structs yet
       (mv nil nil))
      (:vl-union
       ;; BOZO eventually maybe try to do something with unions
       (mv nil nil))
      (:vl-enum
       ;; BOZO eventually maybe try to do something with enums
       (mv nil nil))
      (:vl-usertype
       ;; This shouldn't happen because usertype-elim should have gotten
       ;; rid of it.
       (mv nil nil)))))


(define vl-pp-merged-index ((x vl-merged-index-p) &key (ps 'ps))
  :prepwork ((local (in-theory (enable vl-merged-index-p))))
  (cond ((consp x)
         (vl-ps-seq (vl-print "[")
                    (vl-print (cdr x))
                    (vl-print ":")
                    (vl-print (car x))
                    (vl-print "]")))
        (x
         (vl-print-nat x))
        (t
         (vl-print "NIL"))))

(define vl-pp-merged-index-list ((x vl-merged-index-list-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-merged-index (car x))
               (if (consp (cdr x))
                   (if (consp (cddr x))
                       (vl-print ", ")
                     (vl-print " and "))
                 ps)
               (vl-pp-merged-index-list (cdr x)))))

(define vl-lucid-summarize-bits ((x (and (nat-listp x)
                                         (setp x))))
  :returns (summary stringp :rule-classes :type-prescription)
  (b* (;; X are indices from low to high.
       ;; They need to be in that order for merging to work.  So merge them
       ;; in low to high order.
       (merged (vl-merge-contiguous-indices x))
       ;; For printing we want them in high to low order, so reverse them.
       (merged (rev merged)))
    ;; Now turn them into nice looking strings.
    (with-local-ps (vl-pp-merged-index-list merged)))
  :prepwork
  ((local (defthm l0
            (implies (nat-listp x)
                     (vl-maybe-nat-listp x))
            :hints(("Goal" :induct (len x))))))
  ///
  (assert! (equal (vl-lucid-summarize-bits '(1 2 3)) "[3:1]"))
  (assert! (equal (vl-lucid-summarize-bits '(1 2 3 5 6 7)) "[7:5] and [3:1]"))
  (assert! (equal (vl-lucid-summarize-bits '(1 2 4 6 7 11)) "11, [7:6], 4 and [2:1]")))


(define vl-lucid-dissect-var-main ((ss         vl-scopestack-p)
                                   (item       (or (vl-paramdecl-p item)
                                                   (vl-vardecl-p item)))
                                   (used       vl-lucidocclist-p)
                                   (set        vl-lucidocclist-p))
  :returns (warnings vl-warninglist-p)
  (b* ((used     (vl-lucidocclist-fix used))
       (set      (vl-lucidocclist-fix set))

       (name     (if (eq (tag item) :vl-vardecl)
                     (vl-vardecl->name item)
                   (vl-paramdecl->name item)))

       (warnings nil)

       ((when (and (atom used) (atom set)))
        ;; No uses and no sets of this variable.  It seems best, in this case,
        ;; to issue only a single warning about this spurious variable, rather
        ;; than separate unused/unset warnings.
        (warn :type :vl-lucid-spurious
              :msg "~w0 is never used or set anywhere. (~s1)"
              :args (list name
                          (with-local-ps (vl-pp-scopestack-path ss)))))

       (used-solop (vl-lucid-some-solo-occp used))
       (set-solop  (vl-lucid-some-solo-occp set))
       ((when (and used-solop set-solop))
        ;; The variable is both used and set in full somewhere, so there is
        ;; clearly nothing we need to warn about and we don't need to do any
        ;; further bit-level analysis.
        warnings)

       (datatype-for-indexing
        (b* (((when (eq (tag item) :vl-vardecl))
              (vl-vardecl->type item))
             (paramtype (vl-paramdecl->type item)))
          (vl-paramtype-case paramtype
            (:vl-implicitvalueparam
             ;; This is a really hard case.  I'm going to not try to support
             ;; it, under the theory that we're going to be doing lucid
             ;; checking after unparameterization, and at that point most
             ;; parameters should be used in simple ways.
             nil)
            (:vl-explicitvalueparam paramtype.type)
            (:vl-typeparam
             ;; Doesn't make any sense to try to index into a type.
             nil))))

       ((mv simplep valid-bits)
        (if datatype-for-indexing
            (vl-lucid-valid-bits-for-datatype datatype-for-indexing ss)
          ;; Else, too hard to do any kind of indexing
          (mv nil nil)))

       ;; Try to warn about any unused bits
       (warnings
        (b* (((when (atom used))
              ;; No uses of this variable at all.  No need to do any special
              ;; bit-level analysis.
              (warn :type :vl-lucid-unused
                    :msg "~w0 is set but is never used. (~s1)"
                    :args (list name
                                (with-local-ps (vl-pp-scopestack-path ss)))))
             ((when used-solop)
              ;; The variable is used somewhere all by itself without any
              ;; indexing, so there's no reason to do any bit-level analysis.
              warnings)
             ((unless (and simplep
                           (vl-lucid-all-slices-p used)
                           (vl-lucid-all-slices-resolved-p used)))
              ;; We found uses of the variable but we don't understand what the
              ;; valid bits are or what some of these indices are referring to,
              ;; so this is too hard and we're not going to try to issue any
              ;; warnings.
              warnings)
             ;; Otherwise, we *do* understand all the uses of this variable
             ;; so we can figure out which bits are used.
             (used-bits   (vl-lucid-resolved-slices->bits used))
             (unused-bits (difference valid-bits used-bits))
             ((unless unused-bits)
              ;; All of the bits get used somewhere so this is fine.
              warnings))
          (warn :type :vl-lucid-unused
                :msg "~w0 has some bits that are never used: ~s1. (~s2)"
                :args (list name
                            (vl-lucid-summarize-bits unused-bits)
                            (with-local-ps (vl-pp-scopestack-path ss))))))

       ;; Try to warn about any unset bits
       (warnings
        (b* (((when (atom set))
              (warn :type :vl-lucid-unset
                    :msg "~w0 is used but is never initialized. (~s1)"
                    :args (list name
                                (with-local-ps (vl-pp-scopestack-path ss)))))
             ((when set-solop)
              warnings)
             ((unless (and simplep
                           (vl-lucid-all-slices-p set)
                           (vl-lucid-all-slices-resolved-p set)))
              warnings)
             (set-bits    (vl-lucid-resolved-slices->bits set))
             (unset-bits  (difference valid-bits set-bits))
             ((unless unset-bits)
              warnings))
          (warn :type :vl-lucid-unset
                :msg "~w0 has some bits that are never set: ~s1. (~s2)"
                :args (list name
                            (vl-lucid-summarize-bits unset-bits)
                            (with-local-ps (vl-pp-scopestack-path ss))
                            )))))
    warnings))

(define vl-lucid-dissect-pair ((key vl-lucidkey-p)
                               (val vl-lucidval-p)
                               (reportcard vl-reportcard-p)
                               (st  vl-lucidstate-p))
  :returns (reportcard vl-reportcard-p)
  (b* ((reportcard (vl-reportcard-fix reportcard))
       ((vl-lucidstate st))
       ((vl-lucidkey key))
       ((vl-lucidval val))
       (topname
        ;; The top-level design element to blame, from the scopestack, for any
        ;; warnings.  If there isn't any containing element, we'll just blame
        ;; the whole :design.
        (or (vl-scopestack-top-level-name key.scopestack)
            :design))
       ((when val.errors)
        ;; We won't warn about anything else.
        (b* ((w (make-vl-warning
                 :type :vl-lucid-error
                 :msg "Error computing use/set information for ~s0.  Debugging details: ~x1."
                 :args (list (with-local-ps (vl-pp-lucidkey key))
                             val.errors)
                 :fatalp nil
                 :fn __function__)))
          (vl-extend-reportcard topname w reportcard))))
    (case (tag key.item)

      (:vl-fundecl
       (b* (((when (vl-lucid-some-solo-occp val.used))
             reportcard)
            (w (make-vl-warning :type :vl-lucid-unused
                                :msg "Function ~w0 is never used. (~s1)"
                                :args (list (vl-fundecl->name key.item)
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack)))
                                :fn __function__
                                :fatalp nil)))
         (vl-extend-reportcard topname w reportcard)))

      (:vl-taskdecl
       (b* (((when (vl-lucid-some-solo-occp val.used))
             reportcard)
            (w (make-vl-warning :type :vl-lucid-unused
                                :msg "Task ~w0 is never used. (~s1)"
                                :args (list (vl-taskdecl->name key.item)
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack)))
                                :fn __function__
                                :fatalp nil)))
         (vl-extend-reportcard topname w reportcard)))

      (:vl-typedef
       (b* (((when (vl-lucid-some-solo-occp val.used))
             reportcard)
            (w (make-vl-warning :type :vl-lucid-unused
                                :msg "Type ~w0 is never used. (~s1)"
                                :args (list (vl-typedef->name key.item)
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack)))
                                :fn __function__
                                :fatalp nil)))
         (vl-extend-reportcard topname w reportcard)))

      (:vl-vardecl
       (b* ((warnings (vl-lucid-dissect-var-main key.scopestack key.item val.used val.set)))
         (vl-extend-reportcard-list topname warnings reportcard)))

      (:vl-paramdecl
       (b* (((unless st.paramsp)
             ;; Don't do any analysis of parameters unless it's permitted.
             reportcard)
            (warnings (vl-lucid-dissect-var-main key.scopestack key.item val.used val.set)))
         (vl-extend-reportcard-list topname warnings reportcard)))

      (:vl-interfaceport
       (b* (((when (or val.used val.set))
             ;; Used or set anywhere at all is good enough for an interface.
             reportcard)
            (w (make-vl-warning :type :vl-lucid-spurious
                                :msg "Interface port ~w0 is never mentioned. (~s1)"
                                :args (list (vl-interfaceport->name key.item)
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack)))
                                :fn __function__
                                :fatalp nil)))
         (vl-extend-reportcard topname w reportcard)))

      (:vl-modinst
       (b* (((vl-modinst key.item))
            (mod (vl-scopestack-find-definition key.item.modname key.scopestack))
            ((unless (eq (tag mod) :vl-interface))
             ;; Something like a UDP or a module instance.  We have no
             ;; expectation that this should be used anywhere.
             reportcard)
            ;; Interface port.  We expect that this is at least used or set
            ;; somewhere.  It probably doesn't necessarily need to be both used
            ;; and set.
            ((when (or val.used val.set))
             reportcard)
            (w (make-vl-warning :type :vl-lucid-spurious
                                :msg "Interface ~w0 is never mentioned. (~s1)"
                                :args (list key.item.instname
                                            (with-local-ps (vl-pp-scopestack-path key.scopestack)))
                                :fn __function__
                                :fatalp nil)))
         (vl-extend-reportcard topname w reportcard)))

      (otherwise
       ;; Other kinds of items include, for instance, modinsts, gateinsts,
       ;; modports, generate statements, etc.  We don't have anything sensible
       ;; to say about those.
       reportcard))))

(define vl-lucid-dissect-database ((db         vl-luciddb-p "Already shrunk.")
                                   (reportcard vl-reportcard-p)
                                   (st         vl-lucidstate-p))
  :returns (reportcard vl-reportcard-p)
  :measure (vl-luciddb-count db)
  (b* ((db (vl-luciddb-fix db))
       ((when (atom db))
        (vl-reportcard-fix reportcard))
       ((cons key val) (car db))
       (reportcard (vl-lucid-dissect-pair key val reportcard st)))
    (vl-lucid-dissect-database (cdr db) reportcard st)))

(define vl-lucid-dissect ((st vl-lucidstate-p))
  :returns (reportcard vl-reportcard-p)
  (b* (((vl-lucidstate st))
       (copy (fast-alist-fork st.db nil))
       (-    (fast-alist-free copy)))
    (vl-lucid-dissect-database copy nil st)))

(define vl-design-lucid ((x vl-design-p)
                         &key
                         ((paramsp booleanp) 't))
  :returns (new-x vl-design-p)
  :guard-debug t
  (b* ((x  (cwtime (hons-copy (vl-design-fix x))
                   :name vl-design-lucid-hons
                   :mintime 1))
       (ss (vl-scopestack-init x))
       (st (cwtime (vl-lucidstate-init x :paramsp paramsp)))
       (st (cwtime (vl-design-lucidcheck-main x ss st)))
       (reportcard (cwtime (vl-lucid-dissect st))))
    (vl-scopestacks-free)

    ;; Just debugging
    ;;(vl-cw-ps-seq (vl-pp-lucidstate st))
    ;;(vl-cw-ps-seq (vl-print-reportcard reportcard :elide nil))

    (vl-apply-reportcard x reportcard)))

