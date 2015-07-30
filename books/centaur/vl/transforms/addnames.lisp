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
(include-book "../mlib/allnames")
(include-book "../util/namedb")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc addinstnames
  :parents (transforms)
  :short "Name any unnamed gate or module instances, block statements, generates, etc."

  :long "<p>The names are safely generated using a @(see vl-namefactory-p) and
will have names such as @('modinst_11') and @('gateinst_46').  We also insert generate blocks around any single base generate elements that are inside if, case, or loop generate forms.</p>")


(define maybe-add-name ((x maybe-stringp)
                        (basename stringp)
                        (namedb vl-namedb-p))
  :prepwork ((local (Defthm stringp-of-maybe-string-fix
                      (iff (stringp (maybe-string-fix x))
                           x)
                      :hints(("Goal" :in-theory (enable maybe-string-fix))))))
  :returns (mv (new-x stringp :rule-classes :type-prescription)
               (new-namedb vl-namedb-p))
  (b* ((x (maybe-string-fix x))
       ((when x) (mv x (vl-namedb-fix namedb))))
    (vl-namedb-indexed-name basename namedb)))
    

(fty::defvisitor-template addnames ((x :object)
                                    (namedb vl-namedb-p))
  :returns (mv (new-x :update)
               (new-namedb (:acc namedb :fix (vl-namedb-fix namedb))
                           vl-namedb-p))
  :fnname-template <type>-addnames
  :renames ((vl-design vl-design-addnames-aux))
  :prod-fns
  ((vl-regularport   (name     (lambda (x namedb) (maybe-add-name x "unnamed_port" namedb))))
   (vl-modinst       (instname (lambda (x namedb) (maybe-add-name x "unnamed_modinst" namedb))))
   (vl-gateinst      (name     (lambda (x namedb) (maybe-add-name x "unnamed_gateinst" namedb))))
   (vl-blockstmt     (name     (lambda (x namedb) (maybe-add-name x "unnamed_blockstmt" namedb))))
   (vl-genblock      (name     (lambda (x namedb) (maybe-add-name x "unnamed_genblock" namedb))))
   (vl-genarray      (name     (lambda (x namedb) (maybe-add-name x "unnamed_genarray" namedb))))))


(fty::defvisitors vl-modelement-addnames
  :template addnames
  :types (vl-modelement))

(fty::defvisitor vl-generate-addnames
  :template addnames
  :type vl-genelement
  :prod-fns ((vl-genloop     (body    vl-genelement-addnames-blocknorm))
             (vl-genif       (then    vl-genelement-addnames-blocknorm)
                             (else    vl-genelement-addnames-blocknorm))
             (vl-gencase     (default vl-genelement-addnames-blocknorm))
             (vl-gencaselist (val     vl-genelement-addnames-blocknorm)))

  :measure (two-nats-measure :count 0)

  (define vl-genelement-addnames-blocknorm ((x vl-genelement-p)
                                            (namedb vl-namedb-p))
    :returns (mv (new-x vl-genelement-p)
                 (new-namedb vl-namedb-p))
    :measure (two-nats-measure (vl-genelement-count x) 1)
    (b* (((mv x namedb) (vl-genelement-addnames x namedb)))
      (vl-genelement-case x
        :vl-genblock
        ;; It's already a block, leave it.
        (mv x namedb)
        :otherwise ;; Change genbase or generate into a genblock when nested in
                   ;; an if, loop, or case.
        (b* (((mv name namedb) (vl-namedb-indexed-name "unnamed_genblock" namedb)))
          (mv (make-vl-genblock
               :name name
               :elems (list x)
               :loc (vl-genelement->loc x))
              namedb))))))
         


(fty::defvisitors vl-design-addnames-aux
  :template addnames
  :types (vl-design))

(define vl-design-addnames ((x vl-design-p))
  :returns (new-x vl-design-p)
  :prepwork ((local (defthm string-listp-keys-of-nameset
                      (implies (nameset-p x)
                               (string-listp (alist-keys x)))
                      :hints(("Goal" :in-theory (enable nameset-p))))))
  (b* ((nameset (vl-design-allnames x nil))
       (namedb (vl-starting-namedb (alist-keys nameset)))
       (- (fast-alist-free nameset))
       ((mv new-x namedb) (vl-design-addnames-aux x namedb)))
    (vl-free-namedb namedb)
    new-x))

