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
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system) nfix)))

(defxdoc addnames
  :parents (transforms)
  :short "Name any unnamed gate instances, block statements, generates, etc."
  :long "<p>Note: We used to name everything fairly arbitrarily, as
unnamed_elemtype_nnn, where \"nnn\" was a globally-unique number.  But this
turns out to be too fragile -- a localized design change can nonlocally affect
the numbering everywhere.  We ran into this when specifying signals for a
decomposition; those signals happened to be inside an unnamed generate block,
which likely would mean we'd have to change the signal names often as the
design changed.</p>

<p>In fact, there is a System Verilog spec-mandated scheme for naming unnamed
generate blocks, from Sec. 27.6 of the IEEE spec.  The names generated are
\"genblkN\", numbered within each scope starting at 1.  Explicitly named
generate blocks still take up an index -- the index N indicates the Nth
generate block in the scope, not the Nth unnamed generate block.  If another
item is named e.g. \"genblk5\", then leading zeros are added to the numeral
until there's no conflict, e.g. \"genblk005\".</p>

<p>A complication: if the name to be introduced exists in a higher scope, then
a reference to that name in the current scope (or below) now refers to the
genblock, not to the item from the higher scope.  E.g.:</p>
@({
 module top;
   wire genblk1;
   if (1) begin // genblk01, to avoid conflict
      if (1) begin // genblk1
         wire b;
      end
      wire a = genblk1; // !!
   end
 endmodule
 })

<p>Implementations are split on what happens here.  NCVerilog allows the
reference to genblk1 to refer to the wire, while still naming the inner scope
genblk1 (in, e.g., VCD dumps).  So evidently the generate block is named
genblk1, but is not found when looking up module item genblk1.  (This is OK
because you're not allowed to use hierarchical references through unnamed
generate blocks.)  VCS complains about the reference to genblk1, nonsensically
saying it hasn't been declared yet.  Perhaps what it really means is that it
interprets the reference as a reference to the generate block, which isn't
allowed, and the error message just is making some invalid assumption about
what went wrong.  When the reference is removed, a VCD dump also indicates that
the inner block is called genblk1.</p>

<p>Summary: Both implementations agree that the inner block is called genblk1,
but they don't agree on whether a reference to wire genblk1 is disturbed by its
presence; ncv thinks it isn't, vcs thinks it is.</p>

<p>The situation changes again if there is a hierarchical reference through a
scope named genblk1:</p>
@({
 module sub;
   wire [3:0] foo = 2;
 endmodule
 module top;
  sub genblk1 ();
  if (1) begin // genblk01
    if (1) begin // genblk1
      wire [3:0] foo = 1;
    end
    wire [3:0] fooref = genblk1.foo + 8;
  end
 endmodule
 })

<p>Here ncv complains that implicit names aren't allowed in hierarchical names,
whereas VCS happily runs, with the value of fooref ending up as 9, indicating
that it took genblk1 as referring to the generate block, not the module
instance.</p>

<p>So for now, because it's simple, we'll go with VCS's behavior: unnamed
generate blocks become full named members of the hierarchy that can be looked
up by name.</p>

<p>The situation is tricky with elements other than generate blocks, because
implementations aren't supposed to give them names.  However, the other
elements we plan to name are ports, module and gate instances, and block
statements.  Ports and block statements aren't referenceable by HIDs, so they
won't interfere with any lookups.  Module and gate instances might, though.
BOZO Our solution for now is just to assume that we've chosen obscure enough
generated instance names that there won't be any conflicts.</p>")

(defprod addnames-indices
  ((genblk-idx posp :default 1)
   (gateinst-idx posp :default 1)
   (blockstmt-idx posp :default 1)
   (modinst-idx posp :default 1))
  :layout :tree)

(fty::defvisitor-template collect-odd-names ((x :object)
                                              (acc string-listp))
  :returns (new-acc (:acc acc :fix (string-list-fix acc)) string-listp)
  :fnname-template <type>-collect-odd-names
  :renames ((vl-stmt vl-stmt-collect-odd-names-aux)
            (vl-genelement vl-genelement-collect-odd-names-aux)
            (vl-genblock vl-genblock-collect-odd-names-aux))
  :type-fns ((vl-stmt vl-stmt-collect-odd-names)
             (vl-genelement vl-genelement-collect-odd-names)
             (vl-genblock vl-genblock-collect-odd-names)
             (vl-modelement :skip)
             (vl-fundecllist :skip)
             (vl-taskdecllist :skip)))

;; (local (in-theory (disable STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP
;;                            double-containment
;;                            str::string-list-fix-when-atom
;;                            acl2::string-listp-when-not-consp)))

(fty::defvisitor vl-stmt-collect-odd-names
  :template collect-odd-names
  :type statements
  :measure (two-nats-measure :count 0)
  (define vl-stmt-collect-odd-names ((x vl-stmt-p)
                                     (acc string-listp))
    :returns (names string-listp)
    :measure (two-nats-measure (vl-stmt-count x) 1)
    (b* ((acc (string-list-fix acc)))
      (vl-stmt-case x
        :vl-blockstmt (if x.name (cons x.name acc) acc)
        :otherwise (vl-stmt-collect-odd-names-aux x acc)))))


;; (fty::defvisitors vl-genelement-deps-collect-odd-names 
;;   :template collect-odd-names
;;   :dep-types (vl-genelement))




(fty::defvisitor vl-genelement-collect-odd-names
  :template collect-odd-names
  :type vl-genelement
  :measure (two-nats-measure :count 0)
  (define vl-genelement-collect-odd-names ((x vl-genelement-p)
                                           (acc string-listp))
    :returns (names string-listp)
    :measure (two-nats-measure (vl-genelement-count x) 1)
    (b* ((acc (string-list-fix acc)))
      (vl-genelement-case x
        ;; these cases are covered by the scopeitem alist
        :vl-genbegin acc
        :vl-genarray acc
        
        :otherwise (vl-genelement-collect-odd-names-aux x acc))))
  (define vl-genblock-collect-odd-names ((x vl-genblock-p)
                                         (acc string-listp))
    :returns (names string-listp)
    :measure (two-nats-measure (vl-genblock-count x) 1)
    (b* (((vl-genblock x))
         (acc (string-list-fix acc)))
      (if x.condnestp
          (vl-genelementlist-collect-odd-names x.elems acc)
        (if (stringp x.name)
            (cons x.name acc)
          acc)))))
      
(fty::defvisitors vl-genblob-collect-odd-names 
  :template collect-odd-names
  :types (vl-genblob))


(define names-union-to-nameset-with-dupes ((names string-listp)
                                           (nameset)
                                           (dupes string-listp))
  :returns (mv (nameset-out)
               (dupes-out string-listp))
  (b* (((When (atom names))
        (mv nameset (string-list-fix dupes)))
       (name (string-fix (car names)))
       ((when (hons-get (string-fix (car names)) nameset))
        (names-union-to-nameset-with-dupes (cdr names) nameset (cons name dupes))))
    (names-union-to-nameset-with-dupes
     (cdr names) (hons-acons name t nameset) dupes)))

;; Ports are going to be named separately, considering only other port names.
;; Genblocks, gateinsts, blockstmts, modinsts will all consider the full scope
;; namespace including other gateinsts, blockstmts, etc.

(define vl-genblob-nameset ((x vl-genblob-p))
  :returns (mv (nameset)
               (dupes string-listp))
  (b* ((alist (make-fast-alist (vl-genblob-scope-item-alist x nil)))
       (odd-names (vl-genblob-collect-odd-names x nil)))
     (names-union-to-nameset-with-dupes odd-names alist nil)))

(define vl-blockstmt-nameset ((x vl-stmt-p))
  :guard (vl-stmt-case x :vl-blockstmt)
  :returns (mv (nameset)
               (dupes string-listp))
  (b* ((alist (make-fast-alist (vl-blockscope-scope-item-alist (vl-blockstmt->blockscope x) nil)))
       (odd-names (vl-stmtlist-collect-odd-names (vl-blockstmt->stmts x) nil)))
     (names-union-to-nameset-with-dupes odd-names alist nil)))

(define vl-fundecl-nameset ((x vl-fundecl-p))
  :returns (mv (nameset)
               (dupes string-listp))
  (b* ((alist (make-fast-alist (vl-blockscope-scope-item-alist (vl-fundecl->blockscope x) nil)))
       (odd-names (vl-stmt-collect-odd-names (vl-fundecl->body x) nil)))
     (names-union-to-nameset-with-dupes odd-names alist nil)))

(define vl-taskdecl-nameset ((x vl-taskdecl-p))
  :returns (mv (nameset)
               (dupes string-listp))
  (b* ((alist (make-fast-alist (vl-blockscope-scope-item-alist (vl-taskdecl->blockscope x) nil)))
       (odd-names (vl-stmt-collect-odd-names (vl-taskdecl->body x) nil)))
     (names-union-to-nameset-with-dupes odd-names alist nil)))


(define addnames-nameset-elts-longer-than ((length natp)
                                           (nameset))
  :returns (count natp :rule-classes :type-prescription)
  (if (atom nameset)
      0
    (+ (if (and (consp (car nameset))
                (stringp (caar nameset))
                (>= (length (caar nameset)) (lnfix length)))
           1
         0)
       (addnames-nameset-elts-longer-than length (cdr nameset))))
  ///
  (defthm addnames-nameset-elts-longer-than-decreases-weak
    (implies (natp len)
             (<= (addnames-nameset-elts-longer-than (+ 1 len) nameset)
                 (addnames-nameset-elts-longer-than len nameset)))
    :rule-classes (:rewrite :linear))

  (defthm lookup-implies-addnames-elts-longer-than-decreases
    (implies (and (hons-assoc-equal x nameset)
                  (stringp x)
                  (equal len (length x)))
             (< (addnames-nameset-elts-longer-than (+ 1 len) nameset)
                (addnames-nameset-elts-longer-than len nameset)))
    :hints (("goal" :induct t :do-not-induct t
             :in-theory (enable hons-assoc-equal)))
    :rule-classes (:rewrite :linear)))

(define addnames-find-new-name ((base stringp)
                                (digitstr stringp)
                                (nameset))
  :returns (name stringp)
  :measure (addnames-nameset-elts-longer-than
            (+ (length (string-fix base))
               (length (string-fix digitstr)))
            nameset)
  :prepwork ((local (in-theory (enable string-append))))
  (b* ((str (cat base digitstr))
       ((unless (hons-get str nameset))
        str))
    (addnames-find-new-name base (cat "0" digitstr) nameset))
  ///
  (defret addnames-find-new-name-finds-new-name
    (not (hons-assoc-equal (addnames-find-new-name base digitstr nameset) nameset))))

(define vl-gateinst-addnames ((x vl-gateinst-p)
                              (indices addnames-indices-p)
                              (nameset))
  :returns (mv (new-x vl-gateinst-p)
               (new-indices addnames-indices-p)
               (warnings vl-warninglist-p))
  (b* (((vl-gateinst x))
       ((when x.name)
        (mv (vl-gateinst-fix x)
            (addnames-indices-fix indices) nil))
       ((addnames-indices indices))
       (name (addnames-find-new-name "###___unnamed_gate_" (natstr indices.gateinst-idx) nameset))
       (indices (change-addnames-indices indices :gateinst-idx (+ 1 indices.gateinst-idx))))
    (mv (change-vl-gateinst x :name name)
        indices nil)))

(define vl-modinst-addnames ((x vl-modinst-p)
                             (indices addnames-indices-p)
                             (nameset))
  :returns (mv (new-x vl-modinst-p)
               (new-indices addnames-indices-p)
               (warnings vl-warninglist-p))
  (b* (((vl-modinst x))
       ((when x.instname)
        (mv (vl-modinst-fix x)
            (addnames-indices-fix indices)
            nil))
       ((addnames-indices indices))
       (name (addnames-find-new-name "###___unnamed_modinst_" (natstr indices.modinst-idx) nameset))
       (indices (change-addnames-indices indices :modinst-idx (+ 1 indices.modinst-idx))))
    (mv (change-vl-modinst x :instname name)
        indices nil)))

(define vl-port-addnames ((x vl-port-p)
                          (idx natp)
                          (nameset))
  :returns (mv (new-x vl-port-p)
               (new-index natp :rule-classes :type-prescription))
  (case (tag (vl-port-fix x))
    (:vl-interfaceport (mv (vl-port-fix x)
                          (lnfix idx)))
    (otherwise
     (b* (((vl-regularport x) (vl-port-fix x))
          ((when x.name)
           (mv x
               (lnfix idx)))
          (name (addnames-find-new-name "unnamed_port_" (natstr idx) nameset))
          (idx (1+ (lnfix idx))))
       (mv (change-vl-regularport x :name name) idx)))))


(define vl-portlist-addnames ((x vl-portlist-p)
                              (idx natp)
                              (nameset))
  :returns (new-x vl-portlist-p)
  (b* (((when (atom x))
        (fast-alist-free nameset)
        nil)
       (idx (lnfix idx))
       ((mv x1 idx) (vl-port-addnames (car x) idx nameset)))
    (cons x1 (vl-portlist-addnames (cdr x) idx nameset))))

(define vl-portlist-addnames-top ((x vl-portlist-p))
  :returns (new-x vl-portlist-p)
  (b* (((mv nameset ?dupes)
        (names-union-to-nameset-with-dupes ;; dumb
         (remove nil (vl-portlist->names x)) nil nil)))
    (vl-portlist-addnames x 1 nameset)))


(define vl-blockstmt-addnames-base ((x vl-stmt-p)
                                    (indices addnames-indices-p)
                                    (nameset))
  :guard (vl-stmt-case x :vl-blockstmt)
  :returns (mv (new-x vl-stmt-p)
               (new-indices addnames-indices-p)
               (warnings vl-warninglist-p))
  (b* (((vl-blockstmt x))
       ((when x.name)
        (mv (vl-stmt-fix x)
            (addnames-indices-fix indices)
            nil))
       ((addnames-indices indices))
       (name (addnames-find-new-name "unnamed_block_" (natstr indices.blockstmt-idx) nameset))
       (indices (change-addnames-indices indices :blockstmt-idx (+ 1 indices.blockstmt-idx))))
    (mv (change-vl-blockstmt x :name name)
        indices nil))
  ///
  (defret kind-of-vl-blockstmt-addnames-base
    (implies (vl-stmt-case x :vl-blockstmt)
             (equal (vl-stmt-kind new-x) :vl-blockstmt))))

(define vl-genblock-addnames-base ((x vl-genblock-p)
                                   (indices addnames-indices-p)
                                   (nameset))
  :returns (mv (new-x vl-genblock-p)
               (new-indices addnames-indices-p)
               (warnings vl-warninglist-p))
  (b* (((vl-genblock x))
       ((when x.name)
        (mv (vl-genblock-fix x)
            (addnames-indices-fix indices)
            nil))
       ((addnames-indices indices))
       (name (addnames-find-new-name "genblk" (natstr indices.genblk-idx) nameset)))
       ;; Don't increment the genblock index here and don't add the new name to the nameset,
       ;; because we want to name different branches of an IF the same.
    (mv (change-vl-genblock x :name name)
        (addnames-indices-fix indices)
        nil))
  ///
  (defret count-of-vl-genblock-addnames-base
    (equal (vl-genblock-count new-x)
           (vl-genblock-count x))
    :hints(("Goal" :in-theory (enable vl-genblock-count)))))

(define vl-genarray-addnames-base ((x vl-genelement-p)
                                   (indices addnames-indices-p)
                                   (nameset))
  :guard (vl-genelement-case x :vl-genarray)
  :returns (mv (new-x vl-genelement-p)
               (new-indices addnames-indices-p)
               (warnings vl-warninglist-p))
  (b* (((vl-genarray x))
       ((when x.name)
        (mv (vl-genelement-fix x)
            (addnames-indices-fix indices)
            nil))
       ((addnames-indices indices))
       (name (addnames-find-new-name "genblk" (natstr indices.genblk-idx) nameset)))
       ;; Don't increment the genblock index here and don't add the new name to the nameset,
       ;; because we want to name different branches of an IF the same.
    (mv (change-vl-genarray x :name name)
        (addnames-indices-fix indices)
        nil))
  ///
  (defret kind-of-vl-genarray-addnames-base
    (implies (vl-genelement-case x :vl-genarray)
             (equal (vl-genelement-kind new-x) :vl-genarray))))
       


(fty::defvisitor-template addnames ((x :object)
                                    (indices addnames-indices-p)
                                    (nameset))
  :returns (mv (new-x :update)
               (new-indices (:acc indices :fix (addnames-indices-fix indices))
                            addnames-indices-p)
               (warnings (:join (append-without-guard warnings1 warnings)
                          :tmp-var warnings1
                          :initial nil)
                         vl-warninglist-p))
  :fnname-template <type>-addnames
  :renames ((vl-fundecl vl-fundecl-addnames-aux)
            (vl-taskdecl vl-taskdecl-addnames-aux))
  :type-fns ((vl-gateinst vl-gateinst-addnames)
             (vl-modinst vl-modinst-addnames)
             (vl-fundecl vl-fundecl-addnames)
             (vl-taskdecl vl-taskdecl-addnames)))


(define addnames-warn-about-duplicated-names (x dupes)
  :returns (warnings vl-warninglist-p)
  (and dupes
       (b* ((warnings nil))
         (warn :type :vl-duplicated-names
               :msg "Duplicated names inside ~a0: ~x1"
               :args (list x dupes)))))

(fty::defvisitor vl-stmt-addnames
  :template addnames
  :type statements
  :renames ((vl-stmt vl-stmt-addnames-aux))
  :type-fns ((vl-stmt vl-stmt-addnames))
  :measure (two-nats-measure :count 0)
  (define vl-stmt-addnames ((x vl-stmt-p)
                            (indices addnames-indices-p)
                            (nameset))
    :returns (mv (new-x vl-stmt-p)
                 (new-indices addnames-indices-p)
                 (warnings vl-warninglist-p))
    :measure (two-nats-measure (vl-stmt-count x) 1)
    (b* ((x (vl-stmt-fix x)))
      (vl-stmt-case x
        :vl-blockstmt
        (b* (((mv new-x indices warnings)
              (vl-blockstmt-addnames-base x indices nameset))
             ((mv sub-nameset dupes) (vl-blockstmt-nameset x))
             ((wmv warnings) (addnames-warn-about-duplicated-names x dupes))
             (sub-indices (make-addnames-indices))
             ((wmv new-stmts ?sub-indices warnings)
              (vl-stmtlist-addnames x.stmts sub-indices sub-nameset)))
          (fast-alist-free sub-nameset)
          (mv (change-vl-blockstmt new-x :stmts new-stmts)
              indices warnings))
        :otherwise
        (vl-stmt-addnames-aux x indices nameset)))))

;; (fty::defvisitors vl-fun/taskdecl-deps-addnames
;;   :template addnames
;;   :dep-types (vl-fundecl vl-taskdecl))

(fty::defvisitors vl-fun/taskdecls-addnames-aux
  :template addnames
  :types (vl-fundecl vl-taskdecl))

(define vl-fundecl-addnames ((x vl-fundecl-p)
                             (indices addnames-indices-p)
                             (nameset))
  :returns (mv (new-x vl-fundecl-p)
               (new-indices addnames-indices-p)
               (warnings vl-warninglist-p))
  (declare (ignore nameset))
  (b* ((x (vl-fundecl-fix x))
       ((mv sub-nameset dupes) (vl-fundecl-nameset x))
       (warnings (addnames-warn-about-duplicated-names x dupes))
       (sub-indices (make-addnames-indices))
       ((wmv new-x ?sub-indices warnings)
        (vl-fundecl-addnames-aux x sub-indices sub-nameset)))
    (fast-alist-free sub-nameset)
    (mv new-x
        (addnames-indices-fix indices)
        warnings)))

(define vl-taskdecl-addnames ((x vl-taskdecl-p)
                             (indices addnames-indices-p)
                             (nameset))
  :returns (mv (new-x vl-taskdecl-p)
               (new-indices addnames-indices-p)
               (warnings vl-warninglist-p))
  (declare (ignore nameset))
  (b* ((x (vl-taskdecl-fix x))
       ((mv sub-nameset dupes) (vl-taskdecl-nameset x))
       (warnings (addnames-warn-about-duplicated-names x dupes))
       (sub-indices (make-addnames-indices))
       ((wmv new-x ?sub-indices warnings)
        (vl-taskdecl-addnames-aux x sub-indices sub-nameset)))
    (fast-alist-free sub-nameset)
    (mv new-x
        (addnames-indices-fix indices)
        warnings)))
  

;; (fty::defvisitors vl-genelement-deps-addnames 
;;   :template addnames
;;   :dep-types (vl-genelement))

;; (def-genblob-transform vl-genblob-addnames ((indices addnames-indices-p)
;;                                             (nameset))
;;   :returns ((indices addnames-indices-p)
;;             (nameset)
;;             (warnings vl-warninglist-p))
;;   (b* 




(local (defthm len-forward-to-consp
         (implies (posp (len x))
                  (and (consp x) x))
         :rule-classes ((:forward-chaining :trigger-terms ((len x))))))

(fty::defvisitors vl-genblob-addnames-deps
  :template addnames
  :dep-types (vl-genblob vl-genelement vl-modelement))

(fty::defvisitor-multi vl-genelement-addnames
  (fty::defvisitor :template addnames
    :type vl-genelement
    :renames ((vl-genblock :skip)
              (vl-genelement vl-genelement-addnames-aux))
    :type-fns ((vl-genblock vl-genblock-addnames)
               (vl-genelement vl-genelement-addnames)
               (vl-modelement :skip))
    :measure (two-nats-measure :count 0))

  (fty::defvisitor :template addnames
    :type vl-genblob
    :renames ((vl-genblob vl-genblob-addnames-aux))
    :measure (two-nats-measure (vl-genelementlist-count (vl-genblob->generates x)) 1))

  (define vl-genelement-addnames ((x vl-genelement-p)
                                  (indices addnames-indices-p)
                                  (nameset))
    :returns (mv (new-x vl-genelement-p)
                 (new-indices addnames-indices-p)
                 (warnings vl-warninglist-p))
    :measure (two-nats-measure (vl-genelement-count x) 1)
    (b* (((mv x indices warnings)
          (vl-genelement-addnames-aux x indices nameset))
         (incr (vl-genelement-case x
                 :vl-genbase 0
                 :otherwise 1))
         (indices (change-addnames-indices indices
                                           :genblk-idx (+ incr (addnames-indices->genblk-idx indices))))
         ((wmv x indices warnings)
          (vl-genelement-case x
            :vl-genarray (vl-genarray-addnames-base x indices nameset)
            :otherwise (mv x indices nil))))
      (mv x indices warnings)))

  (define vl-genblock-addnames ((x vl-genblock-p)
                                (indices addnames-indices-p)
                                (nameset))
    :returns (mv (new-x vl-genblock-p)
                 (new-indices addnames-indices-p)
                 (warnings vl-warninglist-p))
    :measure (two-nats-measure (vl-genblock-count x) 2)
    (b* (((vl-genblock x) (vl-genblock-fix x))
         (indices (addnames-indices-fix indices))
         ((when x.condnestp)
          (b* (((unless (and (tuplep 1 x.elems)
                             (or (vl-genelement-case (car x.elems) :vl-genif)
                                 (vl-genelement-case (car x.elems) :vl-gencase))))
                (mv x indices
                    (b* ((warnings nil))
                      (fatal :type :vl-programming-error
                           :msg "Block flagged as nested conditional was not: ~a0"
                           :args (list x)))))
               ((mv elem indices warnings)
                (vl-genelement-addnames-aux (car x.elems) indices nameset)))
            (mv (change-vl-genblock x :elems (list elem))
                indices warnings)))
         (blob (vl-sort-genelements x.elems :id x.name :scopetype :vl-genblock))
         ((mv new-blob warnings) (vl-genblob-addnames blob x))
         (x.elems (vl-genblob->elems new-blob x.elems))
         ((wmv new-x indices warnings) (vl-genblock-addnames-base x indices nameset)))
      (mv (change-vl-genblock new-x :elems x.elems) indices warnings)))

  (define vl-genblob-addnames ((x vl-genblob-p)
                               (ctx))
    :returns (mv (new-x vl-genblob-p)
                 (warnings vl-warninglist-p))
    :measure (two-nats-measure (vl-genelementlist-count (vl-genblob->generates x)) 2)
    (b* ((x (vl-genblob-fix x))
         ((mv sub-nameset dupes) (vl-genblob-nameset x))
         (warnings (addnames-warn-about-duplicated-names ctx dupes))
         (sub-indices (make-addnames-indices))
         ((wmv new-blob ?sub-indices warnings) (vl-genblob-addnames-aux x sub-indices sub-nameset)))
      (fast-alist-free sub-nameset)
      (mv new-blob warnings))))
      
(define vl-module-addnames ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) (vl-module-fix x))
       (warnings x.warnings)
       (ports (vl-portlist-addnames-top x.ports))
       (blob (vl-module->genblob x))
       ((wmv new-blob warnings) (vl-genblob-addnames blob x)))
    (vl-genblob->module new-blob (change-vl-module x :warnings warnings :ports ports))))

(define vl-interface-addnames ((x vl-interface-p))
  :returns (new-x vl-interface-p)
  (b* (((vl-interface x) (vl-interface-fix x))
       (warnings x.warnings)
       (ports (vl-portlist-addnames-top x.ports))
       (blob (vl-interface->genblob x))
       ((wmv new-blob warnings) (vl-genblob-addnames blob x)))
    (vl-genblob->interface new-blob (change-vl-interface x :warnings warnings :ports ports))))

(define vl-package-addnames ((x vl-package-p))
  :returns (new-x vl-package-p)
  (b* (((vl-package x) (vl-package-fix x))
       (warnings x.warnings)
       (blob (vl-package->genblob x))
       ((wmv new-blob warnings) (vl-genblob-addnames blob x)))
    (vl-genblob->package new-blob (change-vl-package x :warnings warnings))))


(defprojection vl-modulelist-addnames ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-addnames x))

(defprojection vl-interfacelist-addnames ((x vl-interfacelist-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-addnames x))

(defprojection vl-packagelist-addnames ((x vl-packagelist-p))
  :returns (new-x vl-packagelist-p)
  (vl-package-addnames x))

(define vl-design-addnames ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) (vl-design-fix x))
       (mods (vl-modulelist-addnames x.mods))
       (interfaces (vl-interfacelist-addnames x.interfaces))
       (packages (vl-packagelist-addnames x.packages))
       (indices (make-addnames-indices))
       (warnings x.warnings)
       ((wmv fundecls & warnings) (vl-fundecllist-addnames x.fundecls indices nil))
       ((wmv taskdecls & warnings) (vl-taskdecllist-addnames x.taskdecls indices nil)))
    (change-vl-design x
                      :mods mods
                      :interfaces interfaces
                      :packages packages
                      :fundecls fundecls
                      :taskdecls taskdecls
                      :warnings warnings)))

