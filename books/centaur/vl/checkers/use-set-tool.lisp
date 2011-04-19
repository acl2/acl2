; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "use-set")
(include-book "../loader/loader")
(include-book "../transforms/xf-make-implicit-wires")
(include-book "../transforms/xf-argresolve")
(include-book "../transforms/xf-portdecl-sign")
(include-book "../transforms/cn-hooks")


(defconst *use-set-defines*
  (list
   (cons "ACTIVE_HIGH" (vl-echarlist-from-str "(* VL_ACTIVE_HIGH *)"))
   (cons "ACTIVE_LOW"  (vl-echarlist-from-str "(* VL_ACTIVE_LOW *)"))))

(defthm vl-defines-p-of-append
  ;; BOZO bad place
  (implies (and (vl-defines-p x)
                (vl-defines-p y))
           (vl-defines-p (append x y)))
  :hints(("Goal" :in-theory (enable vl-defines-p))))

(defund vl-use-set-analysis-fn (override-dirs
                                start-files
                                search-path
                                defines
                                omit
                                suppress-spuriousp
                                suppress-unusedp
                                suppress-unsetp
                                suppress-typosp
;                                suppress-mismatchesp
                                suppress-linputsp
                                suppress-warningsp
                                state)
  (declare (xargs :guard (and (string-listp override-dirs)
                              (string-listp start-files)
                              (string-listp search-path)
                              (string-listp defines)
                              (string-listp omit)
                              (state-p state))
                  :stobjs state))

; This is main function for the standalone USE-SET tool.

  (b* ((defines (append (vl-make-initial-defines defines)
                        *use-set-defines*))

       ((mv successp mods ?filemap ?defines warnings state)
        (cwtime (vl-load override-dirs start-files search-path defines
                         nil ;; don't generate a filemap
                         state)
                :name initial-parsing))
       (-
        (or successp (cw "Note: Not all loading was successful.~%")))

; We print out the warnings from the parse, but hide warnings like ifxz and
; noports since they're chatty and aren't particularly relevant to the use-set
; analysis.

       (warnings (vl-remove-warnings '(:vl-warn-ifxz :vl-warn-noports) warnings))
       (state (ec-call (princ$ (with-local-ps (vl-print-warnings warnings))
                               *standard-co* state)))

; Before we run our analysis, we are going to transform the parsed modules
; in a few simple ways.
;
;   1. We will add declarations for implicit wires (wires which are used but
;      not declared) and for port-implicit wires (wires which are declared as
;      "input w" or "output w", but not also "wire w".  This way, we only have
;      to look at the list of declared wires to see all wire names.
;
;   2. We will also resolve all the argument lists.  This transformation
;      converts named argument lists, like "(.foo(1), .bar(2))", into plain
;      argument lists, like "(1, 2)", and also marks each argument as an input
;      or an output.
;
; Once these transformations are applied, we can construct the use and set
; alist in a pretty direct way.

       (mods (cwtime (vl-modulelist-make-implicit-wires mods)
                     :name xf-make-implicit-wires))

       (mods (cwtime (vl-modulelist-portdecl-sign mods)
                     :name xf-crosscheck-port-signedness))

       (mods (cwtime (vl-modulelist-argresolve mods)
                     :name xf-arg-resolve))

       (mods (cwtime (mp-verror-transform-hook mods)
                     :name xf-mp-verror-transform))

; this never worked well:
;
;       (mods (cwtime (vl-modulelist-cross-active mods)
;                     :name xf-cross-active))

;       (mods (cwtime (vl-modulelist-backflow-annotate mods)
;                     :name xf-backflow-annotate))

       ((mv mods report) (cwtime (vl-mark-wires-for-modulelist mods omit)
                              :name use-set-analysis))

       (state (ec-call
               (acl2::put-global 'mods mods state)))

       (mpv-warnings (let ((mpv (vl-find-module "mp_verror" mods)))
                       (and mpv
                            (vl-module->warnings mpv))))

       (state (ec-call
               (princ$ (with-local-ps (vl-print-useset-report-top report
                                                                  mpv-warnings
                                                                  suppress-spuriousp
                                                                  suppress-unusedp
                                                                  suppress-unsetp
                                                                  suppress-typosp
;                                                                  suppress-mismatchesp
                                                                  suppress-linputsp
                                                                  suppress-warningsp))
                       *standard-co* state)))
       )
      state))

(defmacro vl-use-set-analysis (start-files &key
                                           override-dirs
                                           search-path
                                           defines
                                           omit-wires
                                           suppress-spurious
                                           suppress-unused
                                           suppress-unset
                                           suppress-typos
                                           suppress-mismatches
                                           suppress-linputsp
                                           suppress-warningsp)

; This is the macro that Logic invokes when they want to carry out a USE-SET
; analysis.  Hopefully this is easy to add new keywords to, etc., without
; breaking anyone's examples.

  (declare (ignore suppress-mismatches))

  `(vl-use-set-analysis-fn ,override-dirs
                           ,start-files
                           ,search-path
                           ,defines
                           ,omit-wires
                           ,suppress-spurious
                           ,suppress-unused
                           ,suppress-unset
                           ,suppress-typos
;                           ,suppress-mismatches
                           ,suppress-linputsp
                           ,suppress-warningsp
                           state))



