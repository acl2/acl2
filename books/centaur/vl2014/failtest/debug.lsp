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

; This is just a convenient place to write debugging code.

; fvq bash
; ../bin/vl shell

(lp)
(redef!)
(set-ld-skip-proofsp t state)
(include-book "../loader/parser/tests/base" :dir :system)

(untrace$)

(trace-parser vl-parse-udp-declaration-fn)
(trace-parser vl-parse-integrated-udp-head-fn)
(trace-parser vl-parse-udp-output-declaration-fn)
(trace-parser vl-parse-port-declaration-noatts-fn)
(trace-parser vl-parse-port-declaration-atts-fn)
;(trace-parser vl-parse-basic-port-declaration-tail)
(trace-parser vl-parse-output-reg-port-tail-fn)

(defconst *edgesynth-debug* t)
(defconst *vl-unparam-debug* t)
(defconst *vl-shadowcheck-debug* t)

(trace-parser vl-parse-module-port-list-top-fn)

(defconst *loadconfig*
  (make-vl-loadconfig
   :start-files (list "implicit2.v")
   ))

(defconsts (*loadresult* state)
  ;; If you turn on warning tracing, don't be scared about warnings during parsing
  ;; because they are most likely due to backtracking.
  (vl-load *loadconfig*))

(vl-design->mods (vl-loadresult->design *loadresult*))

(defconst *d0* (vl-loadresult->design *loadresult*))
(vl-module->modnamespace (vl-find-module "sub" (vl-design->mods *d0*)))

(defconst *d1* (vl-design-make-implicit-wires *d0*))
(vl-module->modnamespace (vl-find-module "sub" (vl-design->mods *d1*)))

(defconst *d2* (vl-design-portdecl-sign *d1*))
(vl-module->modnamespace (vl-find-module "sub" (vl-design->mods *d2*)))


                          :name xf-portdecl-sign))
       (design (xf-cwtime (vl-design-udp-elim design)
                          :name xf-udp-elim))
       (design (xf-cwtime (vl-design-duplicate-detect design)
                          :name xf-duplicate-detect))
       (design (xf-cwtime (vl-design-portcheck design)
                          :name xf-portcheck))
       (design (xf-cwtime (vl-design-designwires design)
                          :name xf-mark-design-wires))
       (design (xf-cwtime (vl-design-resolve-indexing design)
                          :name xf-resolve-indexing))
       (design (xf-cwtime (vl-design-argresolve design)
                          :name xf-argresolve))
       (design (xf-cwtime (vl-design-origexprs design)
                          :name xf-origexprs))
       (design (xf-cwtime (mp-verror-transform-hook design)
                          :name xf-mp-verror))
       (design (xf-cwtime (vl-design-clean-warnings design)
                          :name xf-clean-warnings)))


;; OK, so after parsing we DO have both variable declarations.
;; And this indeed has duplicates.
(vl-module->modnamespace (vl-find-module "sub" (vl-design->mods (vl-loadresult->design *loadresult*))))
;; So where are those duplicates being dropped?

(trace$ vl-annotate-design)
;; By the end of annotate the duplicates are gone?!

(trace$ vl-design-make-implicit-wires)


(defconsts *simpconfig*
  (make-vl-simpconfig))

(defconsts (*good* *bad* &)
  (vl-simplify (vl-loadresult->design *loadresult*) *simpconfig*))

(top-level
 (with-local-ps
   (vl-print-reportcard (vl-design-reportcard *good*))))

(top-level
 (with-local-ps
   (vl-print-reportcard (vl-design-reportcard *bad*))))

(car (vl-design->mods *bad*))


(vl-pps-modulelist
 (vl-design->mods (vl-annotate-design (vl-loadresult->design *loadresult*))))

(vl-pps-modulelist
 (vl-design->mods *good*))

(vl-pps-modulelist
 (vl-design->mods *bad*))

(defconsts (*pre* state)
  (sneaky-load :pre-unparam state))

(vl-pps-modulelist (vl-design->mods *pre*))


(define vl-design-unparameterize
  :short "Top-level @(see unparameterization) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (;; Throw out modules that have problems with shadowed parameters.
       (- (sneaky-save :pre-unparam x))
       ((vl-design x) (vl-design-unparam-check x))
       ((unless (uniquep (vl-modulelist->names x.mods)))
        (raise "Programming error: module names are not unique.")
        x)
       (new-mods (vl-modulelist-unparameterize x.mods 1000))

       ;; Just to be absolutely certain this can't happen:
       ((unless (mbt (uniquep (vl-modulelist->names new-mods))))
        (impossible)
        x)

       (- (clear-memoize-table 'vl-create-unparameterized-module))
       (- (cw "; vl-unparameterize: ~x0 => ~x1 modules.~%" (len x.mods) (len new-mods)))
       (ans (change-vl-design x :mods new-mods))
       (- (sneaky-save :post-unparam ans)))
    ans))






(define vl-design-caseelim ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (- (sneaky-save :pre-caseelim x))
       (ans (change-vl-design x :mods (vl-modulelist-caseelim x.mods)))
       (- (sneaky-save :post-caseelim ans)))
    ans))

(define vl-design-elim-unused-vars
  :short "Top-level @(see elim-unused-vars) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (- (sneaky-save :pre-unused x))
       (ans (change-vl-design x
                              :mods (vl-modulelist-elim-unused-vars x.mods)))
       (- (sneaky-save :post-unused x)))
    ans))

(defconsts (*pre-un* state) (sneaky-load :pre-unused state))
(defconsts (*post-un* state) (sneaky-load :post-unused state))

(vl-pps-modulelist (vl-design->mods *pre-un*))


(defconsts (*des* state)
  (sneaky-load :post-caseelim state))

(vl-pps-modulelist (vl-design->mods *des*))
(vl-pps-modulelist (vl-design->mods *bad*))











(def-vl-resolve-indexing vl-fundecl-resolve-indexing
  :type vl-fundecl-p
  :body
  (b* (((vl-fundecl x) x)

       (- (vl-cw-ps-seq
           (vl-cw "------------------------~%Function: ~a0.~%~%" x)))

       ;; This is tricky because the function can have its own declarations.
       ((mv regdecls vardecls eventdecls paramdecls)
        (vl-filter-blockitems x.decls))

       ;; Remove any locally declared names from the global arrfal/wirefal
       ;; we've been given.  In practice, shadowed-names should be short
       ;; because most functions are pretty simple and don't have more than a
       ;; few variables.  So, I'm not worried about just using
       ;; set-difference-equal calls, here.
       (shadowed-names
        (mergesort (append (vl-regdecllist->names regdecls)
                           (vl-vardecllist->names vardecls)
                           (vl-eventdecllist->names eventdecls)
                           (vl-paramdecllist->names paramdecls))))
       (- (vl-cw-ps-seq
           (vl-cw "shadowed names: ~x0.~%" shadowed-names)))

       (visible-global-arrnames
        (set-difference-equal (alist-keys arrfal) shadowed-names))
       (visible-global-wirenames
        (set-difference-equal (alist-keys wirefal) shadowed-names))

       ;; It would probably be safe to turn indexing operations that are
       ;; selecting from most parameters and variables into bitselects.  But
       ;; for now we'll play it safe, and only really try to deal with
       ;; registers here.
       ((mv reg-arrays reg-wires)
        (vl-regdecllist-filter-arrays regdecls nil nil))

       ;; The function's inputs are also okay to turn into bit selects, because
       ;; they can't be arrays.
       (innames         (vl-taskportlist->names x.inputs))

       (local-arrnames  (append-without-guard reg-arrays
                                              visible-global-arrnames))
       (local-wirenames (append-without-guard reg-wires
                                              innames
                                              visible-global-wirenames))
       (local-arrfal    (make-lookup-alist local-arrnames))
       (local-wirefal   (make-lookup-alist local-wirenames))

       (- (cw "visible global arrnames: ~x0.~%" visible-global-arrnames))
       (- (cw "visible global wirenames: ~x0.~%" visible-global-wirenames))
       (- (cw "local arrnames: ~x0.~%" local-arrnames))
       (- (cw "local wirenames: ~x0.~%" local-wirenames))
       (- (cw "local arrfal: ~x0.~%" local-arrfal))
       (- (cw "local wirefal: ~x0.~%" local-wirefal))

       ((mv warnings new-body)
        (vl-stmt-resolve-indexing x.body local-arrfal local-wirefal warnings))
       (- (fast-alist-free local-arrfal))
       (- (fast-alist-free local-wirefal))
       (new-x (change-vl-fundecl x :body new-body)))
    (mv warnings new-x)))


