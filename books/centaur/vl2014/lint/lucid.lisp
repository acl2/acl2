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
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))


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
  :short "Check for unused, unset, spurious wires, and multiply driven wires.")


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
solo occurrence of @('b').</p>"

   ((ctx vl-context1-p
         "The general context where the usage occurred.  Knowing where the
          occurrence came from is useful when we need to report about multiply
          driven signals.")
    (ss  vl-scopestack-p
           "Scopestack where this occurrence was found.  Used in multidrive
            detection.")))

  (:slice
   :short "An indexed occurrence of an identifier."
   :long "<p>We use this to record occurrences of an identifier with a bit- or
part-select.  For individual selects like @('foo[3]'), both left and right will
be the same.</p>"
   ((left  vl-expr-p)
    (right vl-expr-p)
    (ctx   vl-context1-p
           "The general context where the usage occurred.  Knowing where the
            occurrence came from is useful when we need to report about
            multiply driven signals.")
    (ss    vl-scopestack-p
           "Scopestack where this occurrence was found.  Used in multidrive
            detection.")))

  (:tail
   :short "An occurrence of an identifier with something fancy."
   :long "<p>We use this to record occurrences of a variable where there is
additional indexing or some kind of struct field referencing.  For instance, if
we have a variable, @('myinst'), which is an @('instruction_t') structure, then
we might have reads or writes of individual fields, like @('myinst.opcode') or
@('myinst.arg1').  We don't currently record what the tail is or analyze it in
any sensible way, but this at least allows us to see that something has been
read/written.</p>"
   ((ctx vl-context1-p)
    (ss  vl-scopestack-p))))

(define vl-lucidocc->ctx ((x vl-lucidocc-p))
  :returns (ctx vl-context1-p)
  :inline t
  (vl-lucidocc-case x
    :solo x.ctx
    :slice x.ctx
    :tail x.ctx))

(define vl-lucidocc->ss ((x vl-lucidocc-p))
  :returns (ss vl-scopestack-p)
  :inline t
  (vl-lucidocc-case x
    :solo x.ss
    :slice x.ss
    :tail x.ss))

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

   (generatesp booleanp :rule-classes :type-prescription
               "Should we include multidrive warnings in generates?  It will
                generally only make sense to do this <i>after</i>
                unparameterization, because until then things like

                @({ if (condition) assign foo = 1;
                    else assign foo = 0; })

                may appear to be multiple assignments to @('foo'), even though
                they never happen at the same time.")

   (warnings vl-warninglist-p)))


; State Initialization --------------------------------------------------------

(local (xdoc::set-default-parents vl-lucidstate-init))

(define vl-scope-luciddb-init-aux
  :parents (vl-scope-luciddb-init)
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
              ;; Note: used to check whether there were any declarations, and
              ;; otherwise skip putting it on the scopestack. I am guessing
              ;; this isn't an important optimiztion.
              (eq (vl-stmt-kind x) :vl-blockstmt))
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
  ;; BOZO this is probably almost right.  We probably should add some
  ;; additional handling to initialize genvars somehow.
  :no-new-x t
  :returns ((db vl-luciddb-p))
  (b* (((vl-genblob x) (vl-genblob-fix x))
       (ss (vl-scopestack-push x ss))
       (db (vl-scope-luciddb-init x ss db))
       (db (vl-generates-luciddb-init x.generates ss db))
       (db (vl-fundecllist-luciddb-init x.fundecls ss db))
       (db (vl-taskdecllist-luciddb-init x.taskdecls ss db))
       (db (vl-alwayslist-luciddb-init x.alwayses ss db))
       (db (vl-initiallist-luciddb-init x.initials ss db)))
    db)
  :apply-to-generates vl-generates-luciddb-init)

(define vl-module-luciddb-init ((x  vl-module-p)
                                (ss vl-scopestack-p)
                                (db vl-luciddb-p))
  :returns (new-db vl-luciddb-p)
  (b* ((genblob (vl-module->genblob x))
       (db (vl-genblob-luciddb-init genblob ss db)))
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
  (b* ((x  (vl-interface-fix x))
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
   ((paramsp booleanp) 't)
   ((generatesp booleanp) 't))
  :returns (st vl-lucidstate-p)
  (make-vl-lucidstate :db (vl-luciddb-init x)
                      :paramsp paramsp
                      :generatesp generatesp))


; State Debugging -------------------------------------------------------------

(local (xdoc::set-default-parents vl-pps-lucidstate))

(define vl-pp-scope-name ((x vl-scope-p) &key (ps 'ps))
  (b* ((x    (vl-scope-fix x))
       (name (vl-scope->name x)))
    (if name
        (vl-print-str name)
      (vl-ps-seq (vl-print "<unnamed ")
                 (vl-print-str (symbol-name (tag x)))
                 (vl-print ">")))))

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
    (:solo   (vl-ps-seq (vl-print "(:solo :ss ")
                        (vl-pp-scopestack-path x.ss)
                        (vl-print " :ctx ")
                        (vl-pp-context-summary x.ctx)
                        (vl-print ")")))
    (:slice  (vl-ps-seq (vl-cw "(:slice ~a0 ~a1 :ss " x.left x.right)
                        (vl-pp-scopestack-path x.ss)
                        (vl-print " :ctx ")
                        (vl-pp-context-summary x.ctx)
                        (vl-print ")")))
    (:tail  (vl-ps-seq (vl-print "(:tail :ss ")
                       (vl-pp-scopestack-path x.ss)
                       (vl-print " :ctx ")
                       (vl-pp-context-summary x.ctx)
                       (vl-print ")")))


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
                         (ctx   vl-context1-p))
  :parents (vl-lucidstate-mark)
  :returns (new-db vl-luciddb-p)
  (b* ((db   (vl-luciddb-fix db))
       (occ  (vl-lucidocc-fix occ))
       (key  (vl-lucidkey-fix key))
       (ctx  (vl-context1-fix ctx))

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
                            (ctx   vl-context1-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((vl-lucidstate st))
       (db (vl-luciddb-mark mtype key occ st.db ctx)))
    (change-vl-lucidstate st :db db)))

(define vl-lucid-mark-simple ((mtype (member mtype '(:used :set)))
                              (name  stringp)
                              (ss    vl-scopestack-p)
                              (st    vl-lucidstate-p)
                              (ctx   vl-context1-p))
  :returns (new-st vl-lucidstate-p)
  (b* ((st (vl-lucidstate-fix st))
       ((mv item item-ss)
        (vl-scopestack-find-item/ss name ss))
       ((unless item)
        ;; BOZO eventually turn into a proper bad-id warning
        (cw "Warning: missing item ~s0.~%" name)
        st)
       (key (make-vl-lucidkey :item item :scopestack item-ss))
       (occ (make-vl-lucidocc-solo :ctx ctx :ss ss)))
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
                                    (ss    vl-scopestack-p)
                                    (st    vl-lucidstate-p)
                                    (ctx   vl-context1-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((vl-hidstep step))
       ((when (eq (tag step.item) :vl-interfaceport))
        (b* ((key (make-vl-lucidkey
                   :item step.item
                   :scopestack (vl-normalize-scopestack step.ss)))
             (occ (make-vl-lucidocc-solo :ctx ctx :ss ss)))
          (vl-lucidstate-mark mtype key occ st ctx))))
    (vl-lucidstate-fix st)))

(define vl-hidtrace-mark-interfaces ((mtype  (member mtype '(:used :set)))
                                     (trace  vl-hidtrace-p)
                                     (ss     vl-scopestack-p)
                                     (st     vl-lucidstate-p)
                                     (ctx    vl-context1-p))
  :returns (new-st vl-lucidstate-p)
  (b* (((when (atom trace))
        (vl-lucidstate-fix st))
       (st (vl-hidstep-mark-interfaces mtype (car trace) ss st ctx)))
    (vl-hidtrace-mark-interfaces mtype (cdr trace) ss st ctx)))

(define vl-hidsolo-mark ((mtype        (member mtype '(:used :set)))
                         (force-bogusp booleanp)
                         (hid          vl-expr-p)
                         (ss           vl-scopestack-p)
                         (st           vl-lucidstate-p)
                         (ctx          vl-context1-p))
  :guard (vl-hidexpr-p hid)
  :returns (new-st vl-lucidstate-p)
  ;; BOZO this doesn't mark the indices used in the HID expression!!
  (b* (((mv err trace tail) (vl-follow-hidexpr hid ss ctx))
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
       (occ (if (or force-bogusp
                    (not (vl-hidexpr->endp tail)))
                (make-vl-lucidocc-tail :ctx ctx :ss ss)
              (make-vl-lucidocc-solo :ctx ctx :ss ss)))
       (st  (vl-hidtrace-mark-interfaces mtype rest ss st ctx))
       (st  (vl-lucidstate-mark mtype key occ st ctx)))
    st))

(define vl-hidslice-mark ((mtype  (member mtype '(:used :set)))
                          (hid    vl-expr-p)
                          (left   vl-expr-p)
                          (right  vl-expr-p)
                          (ss     vl-scopestack-p)
                          (st     vl-lucidstate-p)
                          (ctx    vl-context1-p))
  :guard (vl-hidexpr-p hid)
  :returns (new-st vl-lucidstate-p)
  ;; BOZO this doesn't mark the indices used in the HID expression!!
  (b* (((mv err trace tail) (vl-follow-hidexpr hid ss ctx))
       ((when err)
        (b* (((vl-lucidstate st)))
          (change-vl-lucidstate st :warnings st.warnings)))
       ((cons (vl-hidstep step) rest) trace)
       (key (make-vl-lucidkey
             :item step.item
             :scopestack (vl-normalize-scopestack step.ss)))
       (occ (if (vl-hidexpr->endp tail)
                (make-vl-lucidocc-slice :left left
                                        :right right
                                        :ctx ctx
                                        :ss ss)
              ;; Too complicated to handle really.
              (make-vl-lucidocc-tail :ctx ctx :ss ss)))
       (st  (vl-hidtrace-mark-interfaces mtype rest ss st ctx))
       (st  (vl-lucidstate-mark mtype key occ st ctx)))
    st))

(define vl-rhsatom-lucidcheck ((x   vl-expr-p)
                               (ss  vl-scopestack-p)
                               (st  vl-lucidstate-p)
                               (ctx vl-context1-p))
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
                                 (ctx vl-context1-p))
    :measure (vl-expr-count x)
    :returns (new-st vl-lucidstate-p)
    :verify-guards nil
    :inline nil
    (b* (((when (vl-hidexpr-p x))
          (b* ((st (vl-hidsolo-mark :used nil x ss st ctx))
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

         ((when (and (or (eq x.op :vl-select-minuscolon)
                         (eq x.op :vl-select-pluscolon)
                         (eq x.op :vl-partselect-pluscolon)
                         (eq x.op :vl-partselect-minuscolon))
                     (vl-hidexpr-p (first x.args))))
          ;; HORRIBLE HACK, force these to be bogus.
          (b* (((list from left right) x.args)
               (st (vl-hidsolo-mark :used t from ss st ctx)) ;; "forced bogus"
               (st (vl-rhsexpr-lucidcheck left ss st ctx))
               (st (vl-rhsexpr-lucidcheck right ss st ctx))
               (st (vl-rhsexprlist-lucidcheck (vl-hidexpr-collect-indices from) ss st ctx)))
            st))

         ;; BOZO may eventually wish to specially handle many other operators:
         ;;  - assignment pattern stuff
         ;;  - tagged operators (recording which tags are used)
         ;;  - streaming concatenation and with operators
         )
      (vl-rhsexprlist-lucidcheck x.args ss st ctx)))

  (define vl-rhsexprlist-lucidcheck ((x   vl-exprlist-p)
                                     (ss  vl-scopestack-p)
                                     (st  vl-lucidstate-p)
                                     (ctx vl-context1-p))
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
                                     (ctx vl-context1-p))
  :returns (new-st vl-lucidstate-p)
  (if x
      (vl-rhsexpr-lucidcheck x ss st ctx)
    (vl-lucidstate-fix st)))


(defines vl-lhsexpr-lucidcheck

  (define vl-lhsexpr-lucidcheck ((x   vl-expr-p)
                                 (ss  vl-scopestack-p)
                                 (st  vl-lucidstate-p)
                                 (ctx vl-context1-p))
    :measure (vl-expr-count x)
    :returns (new-st vl-lucidstate-p)
    :verify-guards nil
    :inline nil
    (b* (((when (vl-atom-p x))
          (if (vl-hidexpr-p x)
              ;; No extra indices or anything to worry about marking.
              (vl-hidsolo-mark :set nil x ss st ctx)
            (vl-lucidstate-fix st)))

         ((vl-nonatom x))

         ;; BOZO subtle orders because index exprs might be hidexprs.  Make sure we
         ;; do index exprs first.
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

         ((when (and (or (eq x.op :vl-select-minuscolon)
                         (eq x.op :vl-select-pluscolon)
                         (eq x.op :vl-partselect-pluscolon)
                         (eq x.op :vl-partselect-minuscolon))
                     (vl-hidexpr-p (first x.args))))
          ;; HORRIBLE HACK, force these to be bogus.
          (b* (((list from left right) x.args)
               (st (vl-hidsolo-mark :set t from ss st ctx)) ;; "forced bogus"
               (st (vl-rhsexpr-lucidcheck left ss st ctx))
               (st (vl-rhsexpr-lucidcheck right ss st ctx))
               (st (vl-rhsexprlist-lucidcheck (vl-hidexpr-collect-indices from) ss st ctx)))
            st))

         ((when (vl-hidexpr-p x))
          (b* ((st (vl-hidsolo-mark :set nil x ss st ctx))
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
                                     (ctx vl-context1-p))
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
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (type     (mksym 'vl- name '-p))
       (fn       (mksym 'vl- name '-lucidcheck))
       (fix      (mksym 'vl- name '-fix)))
    `(define ,fn ((x ,type)
                  (ss vl-scopestack-p)
                  (st vl-lucidstate-p)
                  ,@(and takes-ctx '((ctx vl-context1-p))))
       :returns (new-st vl-lucidstate-p)
       :guard ,guard
       (b* ((x  (,fix x))
            (ss (vl-scopestack-fix ss))
            (st (vl-lucidstate-fix st)))
         ,body))))

(defmacro def-vl-lucidcheck-list (name &key element takes-ctx)
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (type     (mksym 'vl- name '-p))
       (fn       (mksym 'vl- name '-lucidcheck))
       (elem-fn  (mksym 'vl- element '-lucidcheck)))
    `(define ,fn ((x ,type)
                  (ss vl-scopestack-p)
                  (st vl-lucidstate-p)
                  ,@(and takes-ctx '((ctx vl-context1-p))))
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

  (define vl-datatype-lucidcheck ((x   vl-datatype-p)
                                  (ss  vl-scopestack-p)
                                  (st  vl-lucidstate-p)
                                  (ctx vl-context1-p))
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
                                      (ctx vl-context1-p))
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
                                          (ctx vl-context1-p))
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

(define vl-lucid-ctx ((ss   vl-scopestack-p)
                      (elem vl-ctxelement-p))
  :returns (ctx vl-context1-p)
  (make-vl-context1 :mod (vl-scopestack->path ss)
                    :elem elem))

(def-vl-lucidcheck paramdecl
  :body
  (b* (((vl-paramdecl x))
       (ctx (vl-lucid-ctx ss x)))
    (vl-paramtype-case x.type
      (:vl-implicitvalueparam
       (b* (((unless x.type.default)
             ;; No initial value, nothing to do.
             st)
            ;; Initial value, so the parameter itself is set.
            ;; Furthermore, we also need to mark the variables that are
            ;; used in the initial value expression as being used.
            (st (vl-lucid-mark-simple :set x.name ss st ctx))
            (st (vl-rhsexpr-lucidcheck x.type.default ss st ctx)))
         st))
      (:vl-explicitvalueparam
       (b* ((st (vl-datatype-lucidcheck x.type.type ss st ctx))
            ((unless x.type.default)
             st)
            (st (vl-lucid-mark-simple :set x.name ss st ctx))
            (st (vl-rhsexpr-lucidcheck x.type.default ss st ctx)))
         st))
      (:vl-typeparam
       (b* (((unless x.type.default)
             st)
            (st (vl-lucid-mark-simple :set x.name ss st ctx))
            (st (vl-datatype-lucidcheck x.type.default ss st ctx)))
         st)))))

(def-vl-lucidcheck-list paramdecllist :element paramdecl)

(def-vl-lucidcheck vardecl
  :body
  (b* (((vl-vardecl x))
       (ctx (vl-lucid-ctx ss x))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st ctx))
       (st (vl-datatype-lucidcheck x.type ss st ctx))
       (st (if x.initval
               ;; Initial value, so this variable is set and we also need to
               ;; mark all variables used in the rhs as being used.
               (b* ((st (vl-rhsexpr-lucidcheck x.initval ss st ctx))
                    (st (vl-lucid-mark-simple :set x.name ss st ctx)))
                 st)
             st)))
    st))

(def-vl-lucidcheck-list vardecllist :element vardecl)


(defines vl-stmt-lucidcheck

  (define vl-stmt-lucidcheck ((x   vl-stmt-p)
                              (ss  vl-scopestack-p)
                              (st  vl-lucidstate-p)
                              (ctx vl-context1-p))
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

        :vl-returnstmt
        (if x.val
            (vl-rhsexpr-lucidcheck x.val ss st ctx)
          st)

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
              (vl-scopestack-push (vl-blockstmt->blockscope x) ss))
             ;; (st (vl-importlist-lucidcheck x.imports ss st))
             (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
             (st (vl-vardecllist-lucidcheck x.vardecls ss st))
             (st (vl-stmtlist-lucidcheck x.stmts ss st ctx)))
          st))))

  (define vl-stmtlist-lucidcheck ((x   vl-stmtlist-p)
                                  (ss  vl-scopestack-p)
                                  (st  vl-lucidstate-p)
                                  (ctx vl-context1-p))
    :returns (new-st vl-lucidstate-p)
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          (vl-lucidstate-fix st))
         (st (vl-stmt-lucidcheck (car x) ss st ctx)))
      (vl-stmtlist-lucidcheck (cdr x) ss st ctx)))

  (define vl-caselist-lucidcheck ((x  vl-caselist-p)
                                  (ss vl-scopestack-p)
                                  (st vl-lucidstate-p)
                                  (ctx vl-context1-p))
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
  (b* (((vl-always x))
       (ctx (vl-lucid-ctx ss x)))
    (vl-stmt-lucidcheck x.stmt ss st ctx)))

(def-vl-lucidcheck-list alwayslist :element always)

(def-vl-lucidcheck initial
  :body
  (b* (((vl-initial x))
       (ctx (vl-lucid-ctx ss x)))
    (vl-stmt-lucidcheck x.stmt ss st ctx)))

(def-vl-lucidcheck-list initiallist :element initial)

(encapsulate nil
  (local (in-theory (enable (tau-system))))
  (def-vl-lucidcheck portdecl
    :body
    (b* (((vl-portdecl x))
         (ctx (vl-lucid-ctx ss x))
         (st  (vl-datatype-lucidcheck x.type ss st ctx)))
      (case x.dir
        (:vl-input
         ;; We "pretend" that input ports are set because they ought to be set by
         ;; the superior module, function call, or task invocation.
         (vl-lucid-mark-simple :set x.name ss st ctx))
        (:vl-output
         ;; We "pretend" that output ports are used because they ought to be used
         ;; the superior module, function call, or task invocation.
         (vl-lucid-mark-simple :used x.name ss st ctx))
        (:vl-inout
         ;; We don't pretend that inout ports are used or set, because they ought
         ;; to be both used and set within the submodule at some point in time.
         ;; (Otherwise they may as well be just an input or just an output.)
         st)))))

(def-vl-lucidcheck-list portdecllist :element portdecl)

(def-vl-lucidcheck interfaceport
  ;; Unlike regular ports, I think we want to not mark an interface port as
  ;; being used or set.  The smarts for an interface port will mostly be in our
  ;; reporting code.  If the thing is never used or set anywhere at all, we'll
  ;; not report it as an error.  But it's perfectly OK for a module to only
  ;; read from an interface, or to only write to it.
  :body
  (b* (((vl-interfaceport x))
       (ctx (vl-lucid-ctx ss x))
       (st  (vl-packeddimensionlist-lucidcheck x.udims ss st ctx))
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
       (ctx (vl-lucid-ctx ss x))
       (st (vl-datatype-lucidcheck x.rettype ss st ctx))
       ;; Subtle.  Before pushing the function's scope, we mark it as "set".
       ;; This doesn't make a whole lot of sense: what does it mean for a
       ;; function to be set?  But if we regard it as meaning, "it has a
       ;; defined value", then the very act of defining the function is kind of
       ;; like setting it.
       (st    (vl-lucid-mark-simple :set x.name ss st ctx))
       (scope (vl-fundecl->blockscope x))
       (ss    (vl-scopestack-push scope ss))
       ;; Now that we've pushed the function scope, mark the function's name
       ;; (i.e., the return value) as used, because we're imagining that it
       ;; is "used" by whoever calls the function.
       (st    (vl-lucid-mark-simple :used x.name ss st ctx))
       ;; Mark all inputs to the function as set, because we're imagining
       ;; that they're set by the caller.
       (st    (vl-portdecllist-lucidcheck x.portdecls ss st))
       ;; (st (vl-importlist-lucidcheck x.imports ss st))
       (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
       (st (vl-vardecllist-lucidcheck x.vardecls ss st)))
    (vl-stmt-lucidcheck x.body ss st ctx)))

(def-vl-lucidcheck-list fundecllist :element fundecl)

(def-vl-lucidcheck taskdecl
  :body
  (b* (((vl-taskdecl x))
       (ctx (vl-lucid-ctx ss x))
       ;; Subtle.  Mark the task itself as set.  See comments in fundecl
       ;; handling for an explanation.
       (st    (vl-lucid-mark-simple :set x.name ss st ctx))
       (scope (vl-taskdecl->blockscope x))
       (ss    (vl-scopestack-push scope ss))
       (st    (vl-portdecllist-lucidcheck x.portdecls ss st))
       ;; (st (vl-importlist-lucidcheck x.imports ss st))
       (st (vl-paramdecllist-lucidcheck x.paramdecls ss st))
       (st (vl-vardecllist-lucidcheck x.vardecls ss st)))
    (vl-stmt-lucidcheck x.body ss st ctx)))

(def-vl-lucidcheck-list taskdecllist :element taskdecl)

(def-vl-lucidcheck assign
  :body
  (b* (((vl-assign x))
       (ctx (vl-lucid-ctx ss x))
       (st (vl-lhsexpr-lucidcheck x.lvalue ss st ctx))
       (st (vl-rhsexpr-lucidcheck x.expr ss st ctx))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st ctx)))
    st))

(def-vl-lucidcheck-list assignlist :element assign)

(def-vl-lucidcheck typedef
  :body
  (b* (((vl-typedef x))
       (ctx (vl-lucid-ctx ss x))
       (st (vl-lucid-mark-simple :set x.name ss st ctx))
       (st (vl-datatype-lucidcheck x.type ss st ctx)))
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
       (ctx (vl-lucid-ctx ss x))
       (st (vl-maybe-range-lucidcheck x.range ss st ctx))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st ctx))
       (st (vl-plainarglist-lucidcheck x.args ss st ctx)))
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
       (ctx (vl-lucid-ctx ss x))
       (st (vl-maybe-range-lucidcheck x.range ss st ctx))
       (st (vl-maybe-gatedelay-lucidcheck x.delay ss st ctx))
       (st (vl-paramargs-lucidcheck x.paramargs ss st ctx))
       (st (vl-arguments-lucidcheck x.portargs ss st ctx)))
    st))

(def-vl-lucidcheck-list modinstlist :element modinst)

(def-genblob-transform vl-genblob-lucidcheck ((ss vl-scopestack-p)
                                              (st vl-lucidstate-p))
  :no-new-x t
  ;; BOZO this is probably almost right.  We should probably be doing more with
  ;; GENIF and GENCASE stuff to mark the condition expressions as used.  I
  ;; think def-genblob-transform has keywords we could use for that.
  :returns ((st vl-lucidstate-p))
  (b* (((vl-genblob x)     (vl-genblob-fix x))
       (ss                 (vl-scopestack-push x ss))
       (st (vl-generates-lucidcheck x.generates ss st))
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
    st)
  :apply-to-generates vl-generates-lucidcheck)

(def-vl-lucidcheck module
  :body
  (b* ((genblob (vl-module->genblob x))
       (st (vl-genblob-lucidcheck genblob ss st)))
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

(define vl-lucid-first-solo-occ ((x vl-lucidocclist-p))
  :returns (occ? (and (iff (vl-lucidocc-p occ?) (vl-lucid-some-solo-occp x))
                      (iff occ?                 (vl-lucid-some-solo-occp x))))
  :prepwork ((local (in-theory (enable vl-lucid-some-solo-occp))))
  (cond ((atom x)
         nil)
        ((eq (vl-lucidocc-kind (car x)) :solo)
         (vl-lucidocc-fix (car x)))
        (t
         (vl-lucid-first-solo-occ (cdr x)))))

(define vl-lucid-collect-solo-occs ((x vl-lucidocclist-p))
  :returns (solos vl-lucidocclist-p)
  (cond ((atom x)
         nil)
        ((eq (vl-lucidocc-kind (car x)) :solo)
         (cons (vl-lucidocc-fix (car x))
               (vl-lucid-collect-solo-occs (cdr x))))
        (t
         (vl-lucid-collect-solo-occs (cdr x))))
  ///
  (local (in-theory (enable vl-lucid-some-solo-occp)))
  (more-returns
   (solos (iff solos (vl-lucid-some-solo-occp x))
          :name vl-lucid-collect-solo-occs-under-iff)
   (solos (equal (consp solos) (if solos t nil))
          :name consp-of-vl-lucid-collect-solo-occs)))

;; Performance BOZO - we would probably be better off using something like
;; sparse bitsets here, but that would require developing something like
;; nats-from that produces a sparse bitset.  That's fine but might take an hour
;; or two of work.

(define vl-fast-range-p ((x vl-packeddimension-p))
  :prepwork ((local (in-theory (enable vl-packeddimension-p))))
  :hooks nil
  :inline t
  :enabled t
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

(define vl-lucid-valid-bits-for-decl ((item (or (vl-paramdecl-p item)
                                                (vl-vardecl-p item)))
                                      (ss   vl-scopestack-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :returns (mv (simple-p booleanp :rule-classes :type-prescription)
               (bits     (and (nat-listp bits)
                              (setp bits))))
  (b* ((datatype-for-indexing
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
       ((when datatype-for-indexing)
        (vl-lucid-valid-bits-for-datatype datatype-for-indexing ss)))
    ;; Else, too hard to do any kind of indexing
    (mv nil nil)))

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

(define vl-lucid-pp-bits ((x (and (nat-listp x) (setp x))) &key (ps 'ps))
  (b* (;; X are indices from low to high.
       ;; They need to be in that order for merging to work.  So merge them
       ;; in low to high order.
       (merged (vl-merge-contiguous-indices x))
       ;; For printing we want them in high to low order, so reverse them.
       (merged (rev merged)))
    ;; Now turn them into nice looking strings.
    (vl-pp-merged-index-list merged))
  :prepwork
  ((local (defthm l0
            (implies (nat-listp x)
                     (vl-maybe-nat-listp x))
            :hints(("Goal" :induct (len x)))))))

(define vl-lucid-summarize-bits ((x (and (nat-listp x)
                                         (setp x))))
  :returns (summary stringp :rule-classes :type-prescription)
  (with-local-ps (vl-lucid-pp-bits x))
  ///
  (assert! (equal (vl-lucid-summarize-bits '(1 2 3)) "[3:1]"))
  (assert! (equal (vl-lucid-summarize-bits '(1 2 3 5 6 7)) "[7:5] and [3:1]"))
  (assert! (equal (vl-lucid-summarize-bits '(1 2 4 6 7 11)) "11, [7:6], 4 and [2:1]")))



; Identifying Multiple Drivers ------------------------------------------------
;
; Since we are collecting up the lists of all sets and uses of variables, we
; can analyze the list of SETs for a particular variable to try to see if it is
; multiply driven.
;
; A variable is not necessarily multiply driven just because there are multiple
; SETs.  For instance, if someone writes:
;
;   assign foo[1] = ...;
;   assign foo[2] = ...;
;
; Then we'll end up with two slice occurrences for foo, but foo obviously
; doesn't have multiple drivers because these sets are to disjoint slices.  So
; we need to do a sort of bit-level analysis here.
;
; Meanwhile, there are also certain kinds of multiple drivers that we do want
; to allow.  For instance, consider:
;
;    always @(posedge clk)
;    begin
;       foo = 0;
;       if (condition) foo = 1;
;    end
;
; This is all basically reasonable and foo isn't really being multiply driven.
; But this will create two separate SET occurrences for foo.  So, we'll need to
; take care to sort of collapse any SETs that occur in the same always block,
; function declaration, or task declaration.
;
; Also, we definitely don't really want to regard initial statements as any
; sort of real SETs, because something like this is perfectly fine:
;
;    initial foo = 0;
;    always @(posedge clk) foo = foo_in;

(define vl-lucidocclist-drop-initials ((x vl-lucidocclist-p))
  :returns (new-x vl-lucidocclist-p)
  :short "Remove all occurrences that are from @('initial') statements."
  :guard-hints(("Goal" :in-theory (enable tag-reasoning)))
  (b* (((when (atom x))
        nil)
       (elem (vl-context1->elem (vl-lucidocc->ctx (car x))))
       (initial-p (mbe :logic (vl-initial-p elem)
                       :exec (eq (tag elem) :vl-initial)))
       ((when initial-p)
        (vl-lucidocclist-drop-initials (cdr x))))
    (cons (vl-lucidocc-fix (car x))
          (vl-lucidocclist-drop-initials (cdr x)))))

(define vl-inside-true-generate-p ((ss vl-scopestack-p))
  :measure (vl-scopestack-count ss)
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (vl-scopestack-case ss
    :null nil
    :global nil
    :local (or (vl-inside-true-generate-p ss.super)
               (and (mbe :logic (vl-genblob-p ss.top)
                         :exec (eq (tag ss.top) :vl-genblob))
                    ;; Pretty gross hack.  When we turn modules into genblobs
                    ;; they have a name.  When we turn real generates into
                    ;; genblobs (vl-sort-genelements) they don't.  So, we're
                    ;; only in a "true" generate if there is no name.
                    (not (vl-genblob->name ss.top))))))

(define vl-lucidocclist-drop-generates ((x vl-lucidocclist-p))
  :returns (new-x vl-lucidocclist-p)
  :short "Removes all occurrences that are inside of @('generate') blocks."
  :guard-hints(("Goal" :in-theory (enable tag-reasoning)))
  (b* (((when (atom x))
        nil)
       ((when (vl-inside-true-generate-p (vl-lucidocc->ss (car x))))
        (vl-lucidocclist-drop-generates (cdr x))))
    (cons (vl-lucidocc-fix (car x))
          (vl-lucidocclist-drop-generates (cdr x)))))



;; Module instances.

(define vl-lucid-plainarg-nicely-resolved-p ((x vl-plainarg-p))
  (b* (((vl-plainarg x)))
    (if x.dir
        t
      nil)))

(deflist vl-lucid-plainarglist-nicely-resolved-p (x)
  :guard (vl-plainarglist-p x)
  (vl-lucid-plainarg-nicely-resolved-p x))

(define vl-lucid-modinst-nicely-resolved-p ((x vl-modinst-p))
  (b* (((vl-modinst x)))
    (vl-arguments-case x.portargs
      (:vl-arguments-named nil)
      (:vl-arguments-plain (vl-lucid-plainarglist-nicely-resolved-p x.portargs.args)))))

(define vl-lucidocclist-drop-bad-modinsts ((x vl-lucidocclist-p))
  :returns (new-x vl-lucidocclist-p)
  :short "Removes occurrences from unresolved module instances."
  :long "<p>The problem we are solving here happens when there is a buggy
module instance.</p>

<p>Suppose a module being instanced has a parse error, or that we hit some
problem resolving the arguments of the instance, for whatever reason.  In this
case, for lucid's usual use/set checking, the right thing to do (to suppress
false positives) is to pretend each argument to the module is both used and
set.</p>

<p>However, for multidrive warnings this is counterproductive and causes us to
think inputs are driven!  So, for multidrive detection, drop module instances
whose arguments are not sensibly resolved.</p>"
  :guard-hints(("Goal" :in-theory (enable tag-reasoning)))
  (b* (((when (atom x))
        nil)
       (elem      (vl-context1->elem (vl-lucidocc->ctx (car x))))
       (modinst-p (mbe :logic (vl-modinst-p elem)
                       :exec (eq (tag elem) :vl-modinst)))
       ((when (and modinst-p
                   (not (vl-lucid-modinst-nicely-resolved-p elem))))
        ;; Skip it because it is a very bad modinst.
        (vl-lucidocclist-drop-bad-modinsts (cdr x))))
    ;; Else everything is peachy.
    (cons (vl-lucidocc-fix (car x))
          (vl-lucidocclist-drop-bad-modinsts (cdr x)))))

(define vl-lucid-scopestack-subscope-p ((a vl-scopestack-p)
                                        (b vl-scopestack-p))
  :short "Determine if scopestack @('a') occurs within scopestack @('b')."
  :measure (vl-scopestack-count b)
  (b* ((a (vl-scopestack-fix a))
       (b (vl-scopestack-fix b)))
    (or (hons-equal a b)
        (vl-scopestack-case b
          :null nil
          :global nil
          :local (vl-lucid-scopestack-subscope-p a b.super)))))

(define vl-lucidocclist-drop-foreign-writes ((x       vl-lucidocclist-p)
                                             (decl-ss vl-scopestack-p))
  :returns (new-s vl-lucidocclist-p)
  (b* (((when (atom x))
        nil)
       (ss1 (vl-lucidocc->ss (car x)))
       ((unless (vl-lucid-scopestack-subscope-p ss1 decl-ss))
        ;; Foreign, drop it.
        (vl-lucidocclist-drop-foreign-writes (cdr x) decl-ss)))
    (cons (vl-lucidocc-fix (car x))
          (vl-lucidocclist-drop-foreign-writes (cdr x) decl-ss))))


; Grouping up always/fundecls/taskdecls

(fty::defalist vl-lucidmergealist
  ;; Alist used to group up always/fundecl/taskdecl writes to the same variable
  :key-type vl-context1-p
  :val-type vl-lucidocclist-p
  :count vl-lucidmergealist-count)

(define vl-lucid-filter-merges
  :short "Group up occurrences into those to be merged (into a merge alist) and
          those not to be merged (into a regular list)."
  ((x       vl-lucidocclist-p    "Occurrences to filter.")
   (merge   vl-lucidmergealist-p "Accumulator for occs to merge (always blocks, function decls, tasks.).")
   (regular vl-lucidocclist-p    "Accumulator for occs not to merge (continuous assigns, instances)."))
  :returns
  (mv (merge   vl-lucidmergealist-p)
      (regular vl-lucidocclist-p))
  :measure (len x)
  :guard-hints(("Goal" :in-theory (enable tag-reasoning)))
  (b* ((x       (vl-lucidocclist-fix x))
       (merge   (vl-lucidmergealist-fix merge))
       (regular (vl-lucidocclist-fix regular))
       ((when (atom x))
        (mv merge regular))
       (occ1   (car x))
       (ctx1   (vl-lucidocc->ctx occ1))
       (elem1  (vl-context1->elem ctx1))
       (mergep (or (mbe :logic (vl-fundecl-p elem1)  :exec (eq (tag elem1) :vl-fundecl))
                   (mbe :logic (vl-taskdecl-p elem1) :exec (eq (tag elem1) :vl-taskdecl))
                   (mbe :logic (vl-always-p elem1)   :exec (eq (tag elem1) :vl-always))))
       ((unless mergep)
        (vl-lucid-filter-merges (cdr x) merge (cons (car x) regular)))
       (others (cdr (hons-get ctx1 merge)))
       (merge  (hons-acons ctx1 (cons occ1 others) merge)))
    (vl-lucid-filter-merges (cdr x) merge regular)))

(define vl-lucid-do-merges1 ((occs vl-lucidocclist-p "Some sets that all occur in the same always/function/task."))
  :returns (merged-occs vl-lucidocclist-p "Merged together occurrences, if any.")
  (b* ((solo (vl-lucid-first-solo-occ occs))
       ((when solo)
        ;; Doesn't matter what else happens, this block writes to all of foo,
        ;; so consider it as a write to all of foo.
        (list solo))
       ((when (atom occs))
        nil))
    ;; BOZO eventually we should do something smarter here to try to merge
    ;; together any bits we can tell are used.  Maybe we need a new kind of occ
    ;; for that.  For now, we'll just arbitrarily return the first occurrence,
    ;; which may make our analysis a bit incomplete.
    (list (vl-lucidocc-fix (car occs)))))

(define vl-lucid-do-merges ((merge vl-lucidmergealist-p))
  :returns (merged vl-lucidocclist-p)
  :short "Combine the occurrences in the merge alist into single occurrences."
  :measure (vl-lucidmergealist-count merge)
  (b* ((merge (vl-lucidmergealist-fix merge))
       ((when (atom merge))
        nil)
       ((cons ?ctx1 occs1) (first merge)))
    (append (vl-lucid-do-merges1 occs1)
            (vl-lucid-do-merges (rest merge)))))

(define vl-lucidocclist-merge-blocks ((x vl-lucidocclist-p))
  :returns (merged vl-lucidocclist-p)
  :parents (vl-lucid-multidrive-detect)
  :short "Combine together the writes to a variable that occur in the same
          always block."
  (b* (((mv merge-alist regular) (vl-lucid-filter-merges x nil nil))
       (merge-alist (fast-alist-clean merge-alist)))
    (fast-alist-free merge-alist)
    (append (vl-lucid-do-merges merge-alist)
            regular)))

(define vl-pp-lucid-multidrive-summary ((occs vl-lucidocclist-p) &key (ps 'ps))
  (if (atom occs)
      ps
    (vl-ps-seq (vl-indent 4)
               (vl-print " - ")
               (vl-pp-ctxelement-summary (vl-context1->elem (vl-lucidocc->ctx (car occs)))
                                         :withloc t)
               (vl-println "")
               (vl-pp-lucid-multidrive-summary (cdr occs)))))

(define vl-lucid-multidrive-summary ((occs vl-lucidocclist-p))
  :returns (summary stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-lucid-multidrive-summary occs)))


; Heuristic for identifying transistor-style drivers.
;
; In some cases, a particular driver looks like a transistory sort of thing
; and we will not want to issue warnings about multiple drivers.
;  - Gate instances of transistor-style gates like tran gates, pullups, bufifs, nmos, etc.
;  - Assignments that are often used to make one-hot muxes, like
;      assign foo = condition ? foo : 1'bz;

(define vl-lucid-z-expr-p ((x vl-expr-p))
  ;; Recognizes: any width `Z`, `foo ? bar : Z`, or `foo ? Z : bar`
  (if (vl-atom-p x)
      (vl-zatom-p x)
    (b* (((vl-nonatom x) x))
      (and (eq x.op :vl-qmark)
           (or (and (vl-atom-p (cadr x.args))
                    (vl-zatom-p (cadr x.args)))
               (and (vl-atom-p (caddr x.args))
                    (vl-zatom-p (caddr x.args))))))))

(define vl-lucid-z-assign-p ((x vl-assign-p))
  (vl-lucid-z-expr-p (vl-assign->expr x)))

(define vl-lucid-z-gateinst-p ((x vl-gateinst-p))
  (b* (((vl-gateinst x) x))
    (member x.type
            '(:vl-cmos :vl-rcmos :vl-bufif0 :vl-bufif1 :vl-notif0 :vl-notif1
              :vl-nmos :vl-pmos :vl-rnmos :vl-rpmos :vl-tranif0 :vl-tranif1
              :vl-rtranif1 :vl-rtranif0 :vl-tran :vl-rtran :vl-pulldown
              :vl-pullup))))

(define vl-lucidocc-transistory-p ((x vl-lucidocc-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (b* ((elem (vl-context1->elem (vl-lucidocc->ctx x)))
       (tag  (tag elem)))
    (or (and (mbe :logic (vl-gateinst-p elem) :exec (eq tag :vl-gateinst))
             (vl-lucid-z-gateinst-p elem))
        (and (mbe :logic (vl-assign-p elem) :exec (eq tag :vl-assign))
             (vl-lucid-z-assign-p elem)))))

(define vl-lucidocclist-some-transistory-p ((x vl-lucidocclist-p))
  (if (atom x)
      nil
    (or (vl-lucidocc-transistory-p (car x))
        (vl-lucidocclist-some-transistory-p (cdr x)))))



; Bit-level analysis.  This is potentially pretty inefficient but I don't think
; we have to worry much about it, because it will only be inefficient when
; there are lots of writes to the same variable.

(define vl-lucid-collect-resolved-slices ((x vl-lucidocclist-p))
  :returns (resolved (and (vl-lucidocclist-p resolved)
                          (vl-lucid-all-slices-p resolved)
                          (vl-lucid-all-slices-resolved-p resolved)))
  (b* (((when (atom x))
        nil)
       ((when (and (eq (vl-lucidocc-kind (car x)) :slice)
                   (vl-lucid-resolved-slice-p (car x))))
        (cons (vl-lucidocc-fix (car x))
              (vl-lucid-collect-resolved-slices (cdr x)))))
    (vl-lucid-collect-resolved-slices (cdr x))))

(define vl-lucid-slices-append-bits ((x vl-lucidocclist-p))
  :guard (and (vl-lucid-all-slices-p x)
              (vl-lucid-all-slices-resolved-p x))
  :returns (bits nat-listp)
  (if (atom x)
      nil
    (append (vl-lucid-resolved-slice->bits (car x))
            (vl-lucid-slices-append-bits (cdr x))))
  ///
  (more-returns
   (bits true-listp :rule-classes :type-prescription)))

(define vl-lucid-pp-multibits
  ((badbits  setp              "The set of multiply driven bits.")
   (occs     vl-lucidocclist-p "Occs which may or may not drive these bits.")
   &key (ps 'ps))
  :guard (and (nat-listp badbits)
              (vl-lucid-all-slices-p occs)
              (vl-lucid-all-slices-resolved-p occs))
  (b* (((when (atom occs))
        ps)
       (occbits (vl-lucid-resolved-slice->bits (car occs)))
       (overlap (intersect occbits badbits))
       ((unless overlap)
        (vl-lucid-pp-multibits badbits (cdr occs))))
    ;; Else, there is some overlap here:
    (vl-ps-seq (vl-indent 4)
               (if (vl-plural-p overlap)
                   (vl-print " - Bits ")
                 (vl-print " - Bit "))
               (vl-lucid-pp-bits overlap)
               (vl-print ": ")
               (vl-pp-ctxelement-summary (vl-context1->elem (vl-lucidocc->ctx (car occs)))
                                         :withloc t)
               (vl-println "")
               (vl-lucid-pp-multibits badbits (cdr occs)))))

(define vl-inside-interface-p ((ss vl-scopestack-p))
  :measure (vl-scopestack-count ss)
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (vl-scopestack-case ss
    :null nil
    :global nil
    :local (or (vl-inside-interface-p ss.super)
               (mbe :logic (vl-interface-p ss.top)
                    :exec (eq (tag ss.top) :vl-interface)))))

(define vl-inside-blockscope-p ((ss vl-scopestack-p))
  :measure (vl-scopestack-count ss)
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (vl-scopestack-case ss
    :null nil
    :global nil
    :local (or (vl-inside-blockscope-p ss.super)
               (mbe :logic (vl-blockscope-p ss.top)
                    :exec (eq (tag ss.top) :vl-blockscope)))))


(defsection vl-custom-suppress-multidrive-p
  :short "Mechanism for custom suppression of multidrive warnings."
  :long "<p>We use this at Centaur to suppress multidrive warnings within
certain modules that we know are not RTL designs.</p>

<p>This is an attachable function that should return @('t') when you want
to suppress warnings.  It can inspect:</p>

<ul>
<li>@('ss') - the scopestack for the declaration.</li>
<li>@('item') - the variable or parameter declaration itself.</li>
<li>@('set') - the list of places where the variable was set.</li>
</ul>

<p>This suppression is done in addition to the default heuristics.  That is,
your function can focus just on the additional rules you want to add, and
doesn't have to recreate the default heuristics.</p>"

  (encapsulate
    (((vl-custom-suppress-multidrive-p * * *) => *
      :formals (ss item set)
      :guard (and (vl-scopestack-p ss)
                  (or (vl-paramdecl-p item)
                      (vl-vardecl-p item))
                  (vl-lucidocclist-p set))))

    (local (defun vl-custom-suppress-multidrive-p (ss item set)
             (declare (ignorable ss item set))
             nil))

    (defthm booleanp-of-vl-custom-suppress-multidrive-p
      (booleanp (vl-custom-suppress-multidrive-p ss item set))
      :rule-classes :type-prescription))

  (define vl-custom-suppress-multidrive-p-default ((ss    vl-scopestack-p)
                                                   (item  (or (vl-paramdecl-p item)
                                                              (vl-vardecl-p item)))
                                                   (set   vl-lucidocclist-p))
    (declare (ignorable ss item set))
    nil)

  (defattach vl-custom-suppress-multidrive-p
    vl-custom-suppress-multidrive-p-default))

(define vl-lucidocclist-remove-tails ((x vl-lucidocclist-p))
  :returns (new-x vl-lucidocclist-p)
  (cond ((atom x)
         nil)
        ((eq (vl-lucidocc-kind (car x)) :tail)
         (vl-lucidocclist-remove-tails (cdr x)))
        (t
         (cons (vl-lucidocc-fix (car x))
               (vl-lucidocclist-remove-tails (cdr x))))))

(define vl-lucid-multidrive-detect
  ((ss    vl-scopestack-p)
   (item  (or (vl-paramdecl-p item)
              (vl-vardecl-p item)))
   (set   vl-lucidocclist-p)
   (genp  booleanp "Consider occurrences from generates?"))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :returns (warnings vl-warninglist-p)
  (b* ((ss  (vl-scopestack-fix ss))
       (set (vl-lucidocclist-fix set))

       ((when (or (atom set)
                  (atom (cdr set))))
        ;; No driver or at most one driver, so there are not multiple drivers.
        nil)
       ;; Clean up the list of sets by:
       ;;
       ;;  1. Eliminating any sets from initial blocks
       ;;
       ;;  2. Merging together any writes that happen in the same always block,
       ;;     function declaration, or task declaration, so that we don't
       ;;     complain about things like:
       ;;
       ;;       always @(posedge clk) begin
       ;;         foo = 0;
       ;;         if (whatever) foo = 1;
       ;;       end
       ;;
       ;;  3. Drop occurrences from "bad" module instances (where we could have
       ;;     accidentally think that inputs are being driven)
       ;;
       ;;  4. Drop generates if we have been told to ignore them.
       ;;
       ;;  5. Drop "foreign writes" -- writes that occur from a scopestack other
       ;;     than where the variable is declared.  Without this, we get into
       ;;     problems due to things like this:
       ;;
       ;;        submod inst1 (...);
       ;;        submod inst2 (...);
       ;;        always @(...) begin
       ;;           assign inst1.foo = 1;
       ;;           assign inst2.foo = 1;
       ;;        end
       ;;
       ;;     The problem is that this looks like two drivers onto submod.foo.
       ;;
       ;;  6. Drop TAIL occurrences, because they might be things like foo[3-:0]
       ;;     that we don't understand.
       (set (vl-lucidocclist-drop-initials set))
       (set (vl-lucidocclist-merge-blocks set))
       (set (vl-lucidocclist-drop-bad-modinsts set))
       (set (vl-lucidocclist-drop-foreign-writes set ss))
       (set (if genp set (vl-lucidocclist-drop-generates set)))
       (set (vl-lucidocclist-remove-tails set))

       ((when (or (atom set)
                  (atom (cdr set))))
        nil)

       ((when (and (eq (tag item) :vl-vardecl)
                   (not (member (vl-vardecl->nettype item) '(nil :vl-wire :vl-uwire)))))
        ;; This has a fancy net type such as TRI, TRIREG, WOR, WAND, SUPPLY,
        ;; etc., which suggests that this is a transistor-level design rather
        ;; than an RTL level design.
        ;;
        ;;  - We certainly do not want to issue any warnings about nets such as
        ;;    TRI/WAND/WOR since those net types strongly indicate that
        ;;    multiple drivers are expected.
        ;;
        ;;  - BOZO I don't know whether or not it ever makes sense to be driving
        ;;    a supply1/supply0 wire.  But I think that even if this doesn't make
        ;;    sense, it's nothing we want to be issuing warnings about.
        nil)

       ((when (vl-lucidocclist-some-transistory-p set))
        ;; Something that is driving this wire looks like a transistor or like
        ;; it sometimes may drive Z values onto the wire.  We therefore do NOT
        ;; want to issue any warnings.
        nil)

       ((mv simple-p ?valid-bits)
        (vl-lucid-valid-bits-for-decl item ss))
       ((unless simple-p)
        ;; Something like an array or fancy structure that is just going to be
        ;; too hard for us to warn about.  (BOZO some day we might try to
        ;; improve the scope of what we can check.)
        nil)

       ((when (vl-inside-interface-p ss))
        ;; This variable is declared somewhere within an interface.  It's fine
        ;; for there to be multiple uses/sets of it, because there may be many
        ;; instances of the interface throughout the design.
        nil)

       ((when (vl-inside-blockscope-p ss))
        ;; This variable is defined in a block scope, i.e., a function, task, or
        ;; begin/end block.  Such variables are used in procedural code and are
        ;; hence not anything we want to give multidrive warnings about.
        nil)

       ((when (vl-custom-suppress-multidrive-p ss item set))
        ;; The user wants to exclude this warning.
        nil)

       (name     (if (eq (tag item) :vl-vardecl)
                     (vl-vardecl->name item)
                   (vl-paramdecl->name item)))

       (solos (vl-lucid-collect-solo-occs set))
       ((when (and (consp solos)
                   (consp (cdr solos))))
        (list (make-vl-warning :type :vl-lucid-multidrive
                               :msg "~w0 has multiple drivers:~%~s1"
                               :args (list name (vl-lucid-multidrive-summary solos))
                               :fn __function__)))

       ;; If we get this far, there aren't any whole-wire conflicts.  Let's see
       ;; if we can find any bit-level conflicts.

       (resolved (vl-lucid-collect-resolved-slices set))
       (allbits  (vl-lucid-slices-append-bits resolved))

       ((when (and (consp solos)
                   (consp allbits)))
        ;; There is a write to the entire wire, and also some writes to individual
        ;; bits.  So, we want to warn about any of these allbits.
        (list (make-vl-warning
               :type :vl-lucid-multidrive
               :msg "~w0 has multiple drivers:~%~s1"
               :args (list name
                           (with-local-ps
                             (vl-indent 4)
                             (vl-print " - Full: ")
                             (vl-pp-ctxelement-summary (vl-context1->elem (vl-lucidocc->ctx (car solos)))
                                                       :withloc t)
                             (vl-println "")
                             (vl-lucid-pp-multibits (mergesort allbits) resolved)))
               :fn __function__)))

       ;; Otherwise, there aren't any writes to the whole wire, but there may
       ;; still be overlaps between the individual bits, so check for
       ;; duplicates.
       (dupes   (duplicated-members allbits))
       ((unless (consp dupes))
        ;; No bits are obviously duplicated.
        nil))
    (list (make-vl-warning
           :type :vl-lucid-multidrive
           :msg "~w0 has multiple drivers on some bits:~%~s1"
           :args (list name (with-local-ps
                              (vl-lucid-pp-multibits (mergesort dupes) resolved)))
           :fn __function__))))

(define vl-lucid-dissect-var-main
  ((ss         vl-scopestack-p)
   (item       (or (vl-paramdecl-p item)
                   (vl-vardecl-p item)))
   (used       vl-lucidocclist-p)
   (set        vl-lucidocclist-p)
   (genp       booleanp))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :returns (warnings vl-warninglist-p)
  (b* ((used     (vl-lucidocclist-fix used))
       (set      (vl-lucidocclist-fix set))

       (name     (if (eq (tag item) :vl-vardecl)
                     (vl-vardecl->name item)
                   (vl-paramdecl->name item)))

       (warnings (vl-lucid-multidrive-detect ss item set genp))

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

       ((mv simplep valid-bits)
        (vl-lucid-valid-bits-for-decl item ss))

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
       (b* ((warnings (vl-lucid-dissect-var-main key.scopestack key.item val.used val.set st.generatesp)))
         (vl-extend-reportcard-list topname warnings reportcard)))

      (:vl-paramdecl
       (b* (((unless st.paramsp)
             ;; Don't do any analysis of parameters unless it's permitted.
             reportcard)
            (warnings (vl-lucid-dissect-var-main key.scopestack key.item val.used val.set st.generatesp)))
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
                         ((paramsp booleanp) 't)
                         ((generatesp booleanp) 't))
  :returns (new-x vl-design-p)
  :guard-debug t
  (b* ((x  (cwtime (hons-copy (vl-design-fix x))
                   :name vl-design-lucid-hons
                   :mintime 1))
       (ss (vl-scopestack-init x))
       (st (cwtime (vl-lucidstate-init x
                                       :paramsp paramsp
                                       :generatesp generatesp)))
       (st (cwtime (vl-design-lucidcheck-main x ss st)))
       (reportcard (cwtime (vl-lucid-dissect st))))
    (vl-scopestacks-free)

    ;; Just debugging
    ;;(vl-cw-ps-seq (vl-pp-lucidstate st))
    ;;(vl-cw-ps-seq (vl-print-reportcard reportcard :elide nil))

    (vl-apply-reportcard x reportcard)))
