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

(defconst *vl-lint-version* "0.07")

(include-book "bit-use-set")
(include-book "check-namespace")
(include-book "disconnected")
(include-book "xf-drop-missing-submodules")
(include-book "xf-hid-flatten")
(include-book "xf-lint-stmt-rewrite")
(include-book "xf-remove-toohard")
(include-book "xf-undefined-names")

(include-book "../checkers/condcheck")
(include-book "../checkers/duplicate-detect")
(include-book "../checkers/leftright")
(include-book "../checkers/multidrive-detect")
(include-book "../checkers/portcheck")
(include-book "../checkers/qmarksize-check")
(include-book "../checkers/selfassigns")
(include-book "../checkers/skip-detect")

(include-book "../loader/loader")
(include-book "../transforms/cn-hooks")
(include-book "../transforms/xf-argresolve")
(include-book "../transforms/xf-array-indexing")
(include-book "../transforms/xf-assign-trunc")
(include-book "../transforms/xf-blankargs")
(include-book "../transforms/xf-clean-params")
(include-book "../transforms/xf-drop-blankports")
(include-book "../transforms/xf-expr-split")
(include-book "../transforms/xf-expand-functions")
(include-book "../transforms/xf-follow-hids")
(include-book "../transforms/xf-orig")
(include-book "../transforms/xf-oprewrite")
(include-book "../transforms/xf-portdecl-sign")
(include-book "../transforms/xf-resolve-ranges")
(include-book "../transforms/xf-replicate-insts")
(include-book "../transforms/xf-sizing")
(include-book "../transforms/xf-stmt-rewrite")
(include-book "../transforms/xf-unparameterize")
(include-book "../transforms/xf-unused-reg")

(local (include-book "../mlib/modname-sets"))
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))



(defsection vl-filter-mods-with-good-paramdecls

; VL-Lint Only.
;
; Unparameterization requires that the module list is complete and that all
; modules have good parameters.  In our ordinary translation process, we throw
; away any modules with bad parameters, any then transitively throw away any
; modules with instances of missing modules.  But in VL-Lint, we'd like to try
; to carry out unparameterization with as little damage as possible.
;
; As a pre-unparameterization step, in this transform we throw away any modules
; with bad parameters and then throw away any instances of missing modules.
; This is obviously unsound, so it should never be used in our ordinary
; translation process.

  (defund vl-filter-mods-with-good-paramdecls (x good bad)
    (declare (xargs :guard (vl-modulelist-p x)))
    (cond ((atom x)
           (mv good bad))
          ((vl-good-paramdecllist-p (vl-module->paramdecls (car x)))
           (vl-filter-mods-with-good-paramdecls (cdr x)
                                                (cons (car x) good)
                                                bad))
          (t
           (vl-filter-mods-with-good-paramdecls (cdr x)
                                                good
                                                (cons (car x) bad)))))

  (local (in-theory (enable vl-filter-mods-with-good-paramdecls)))

  (defthm vl-filter-mods-with-good-paramdecls-basics
    (let ((ret (vl-filter-mods-with-good-paramdecls x good bad)))
      (and (implies (and (force (vl-modulelist-p x))
                         (force (vl-modulelist-p good)))
                    (vl-modulelist-p (mv-nth 0 ret)))
           (implies (and (force (vl-modulelist-p x))
                         (force (vl-modulelist-p bad)))
                    (vl-modulelist-p (mv-nth 1 ret)))))))




(defund vl-print-certain-warnings (mods show hide)
  (declare (xargs :guard (and (vl-modulelist-p mods)
                              (symbol-listp show)
                              (symbol-listp hide))))
  (b* ((warnings (vl-modulelist-flat-warnings-exec mods nil))
       (types    (mergesort (vl-warninglist->types-exec warnings nil)))
       (hide     (if hide
                     (mergesort hide)
                   types))
       (show     (mergesort show))
       ;; Misc is all the warning types that we aren't told to show, but aren't
       ;; told to ignore.  We'll print a note that these warnings exist but
       ;; that we weren't told to show or hide them.
       (misc     (difference types (union show hide)))
       (warnings (vl-keep-warnings show warnings)))
    (vl-cw-ps-seq
     (vl-ps-update-autowrap-col 65)
     (vl-print-warnings warnings)
     (vl-println "")
     (if (not misc)
         ps
       (vl-ps-seq
        (vl-cw "Note: not showing ~&0 warnings.~%" misc)
        (vl-println ""))))))



(defun run-vl-lint (start-files search-path searchext top-mods state)
  (declare (xargs :guard (and (string-listp start-files)
                              (string-listp search-path)
                              (string-listp searchext)
                              (string-listp top-mods))
                  :stobjs state))
  (b* ((- (cw "Starting VL-Lint ~s0~%" *vl-lint-version*))
       (- (cw "~%vl-lint: loading modules...~%"))
       ((mv ?successp mods ?filemap ?defines ?warnings state)
        (cwtime (vl-load :override-dirs nil
                         :start-files   start-files
                         :search-path   search-path
                         :searchext     searchext)))
       ;; Throw away any modules we don't care about, if we have been
       ;; given any top-mods.
       (mods (if (not top-mods)
                 mods
               (vl-remove-unnecessary-modules (mergesort top-mods)
                                              (mergesort mods))))
       (mods0 mods)

       (- (cw "~%vl-lint: initial processing...~%"))
       (mods (cwtime (vl-modulelist-portcheck mods)))
       (mods (cwtime (vl-modulelist-duplicate-detect mods)))
       (mods (cwtime (vl-modulelist-condcheck mods)))
       (mods (cwtime (vl-modulelist-leftright-check mods)))
       (mods (cwtime (vl-modulelist-drop-missing-submodules mods)))
;; BOZO reinstate this??       (mods (cwtime (vl-modulelist-add-undefined-names mods)))
       (mods (cwtime (vl-modulelist-portdecl-sign mods)))
       (mods (cwtime (vl-modulelist-make-array-indexing mods)))
       (mods (cwtime (vl-modulelist-origexprs mods)))
       (mods (cwtime (vl-modulelist-check-namespace mods)))

       (- (cw "~%vl-lint: processing arguments, parameters...~%"))
       (mods (cwtime (vl-modulelist-elim-unused-regs mods)))
       (mods (cwtime (vl-modulelist-argresolve mods)))

       ;; BOZO not exactly sure where this should go, maybe this will work.
       (mods (cwtime (vl-modulelist-expand-functions mods)))

       ;; BOZO we need to do something to throw away instances with unresolved
       ;; arguments to avoid programming-errors in drop-blankports... and actually
       ;; we hit errors like that later, too.
       (mods (cwtime (vl-modulelist-drop-blankports mods)))
       (mods (cwtime (mp-verror-transform-hook mods)))
       (mods (cwtime (vl-modulelist-follow-hids mods)))
       (mods (cwtime (vl-modulelist-clean-params mods)))
       (mods (cwtime (vl-modulelist-check-good-paramdecls mods)))
       ((mv mods bad)
        (vl-filter-mods-with-good-paramdecls mods nil nil))
       (- (or (not bad)
              (progn$
               (cw "~%~%Note: deleting ~x0 module~s1 because they include ~
                    unsupported parameter declarations.~%~%~
                    Module~s1 being deleted: ~&2~%~%~
                    Details:~%~%"
                   (len bad)
                   (if (= (len bad) 1) "" "s")
                   (mergesort (vl-modulelist->names bad)))
               (vl-print-certain-warnings bad
                                          (list :vl-bad-paramdecl
                                                :vl-bad-paramdecls)
                                          nil))))
       (mods (cwtime (vl-modulelist-drop-missing-submodules mods)))
       (mods (if (and (uniquep (vl-modulelist->names mods))
                      (vl-modulelist-complete-p mods mods)
                      (vl-good-paramdecllist-list-p-of-vl-modulelist->paramdecls mods))
                 mods
               (er hard? 'vl-lint
                   "Programming error.  Expected modules to be complete ~
                    and to have good parameters, but this is not the case. ~
                    Please tell Jared about this failure.")))
       ((mv mods failmods) (cwtime (vl-unparameterize mods 30)))
       (mods (append mods failmods))
       (- (vl-gc))

       (- (cw "~%vl-lint: processing ranges, statements...~%"))
       (mods (cwtime (vl-modulelist-rangeresolve mods)))
       (mods (cwtime (vl-modulelist-selresolve mods)))
       (mods (cwtime (vl-modulelist-check-selfassigns mods)))
       (mods (cwtime (vl-modulelist-lint-stmt-rewrite mods)))
       (mods (cwtime (vl-modulelist-stmtrewrite mods 1000)))
       (mods (cwtime (vl-modulelist-hid-flatten mods)))

       ;; BOZO it seems sort of legitimate to do this before sizing, which
       ;; might be nice.  Of course, a more rigorous use/set analysis will
       ;; need to be post-sizing.
       (- (cw "~%vl-lint: finding disconnected wires...~%"))
       (mods (cwtime (vl-modulelist-remove-toohard mods)))
       (mods (cwtime (vl-modulelist-find-disconnected mods)))

       (- (cw "~%vl-lint: processing expressions...~%"))
       (mods (cwtime (vl-modulelist-oprewrite mods)))
       (mods (cwtime (vl-modulelist-exprsize mods)))
       (mods (cwtime (vl-modulelist-qmarksize-check mods)))

       (- (cw "~%vl-lint: finding unused/unset wires...~%"))
       ;; BOZO this probably doesn't quite work here due to replicate not having been done
       ((mv mods dalist) (cwtime (us-analyze-mods mods)))
       (- (vl-gc))

       (- (cw "~%vl-lint: processing assignments...~%"))
       (mods (cwtime (vl-modulelist-split mods)))
       (mods (cwtime (vl-modulelist-replicate mods)))
       (mods (cwtime (vl-modulelist-blankargs mods)))
       (mods (cwtime (vl-modulelist-trunc mods)))

       (- (cw "~%vl-lint: finding skipped and multiply driven wires...~%"))
       ;; NOTE: use mods0, not mods, if you ever want this to finish. :)
       (sd-probs (cwtime (sd-analyze-modulelist mods0)))
       (mods     (cwtime (vl-modulelist-multidrive-detect mods)))

       (- (cw "~%vl-lint: cleaning up...~%"))
       (mods    (cwtime (vl-modulelist-clean-warnings mods)))
       (mwalist (cwtime (vl-origname-modwarningalist mods)))
       )
    (mv mods mods0 mwalist sd-probs dalist state)))


(defund sd-problem-major-p (x)
  (declare (xargs :guard (sd-problem-p x)))
  (b* (((sd-problem x) x))
    (or (>= x.priority 10)
        (and (>= x.priority 6) (>= x.groupsize 4))
        (>= (sd-problem-score x) 8))))

(defsection sd-filter-problems

  (defund sd-filter-problems (x major minor)
    "Returns (MV MAJOR MINOR)"
    (declare (xargs :guard (sd-problemlist-p x)))
    (cond ((atom x)
           (mv major minor))
          ((sd-problem-major-p (car x))
           (sd-filter-problems (cdr x) (cons (car x) major) minor))
          (t
           (sd-filter-problems (cdr x) major (cons (car x) minor)))))

  (local (in-theory (enable sd-filter-problems)))

  (defthm sd-problemlist-p-of-sd-filter-problems
    (and (implies (and (sd-problemlist-p x)
                       (sd-problemlist-p major))
                  (sd-problemlist-p (mv-nth 0 (sd-filter-problems x major minor))))
         (implies (and (sd-problemlist-p x)
                       (sd-problemlist-p minor))
                  (sd-problemlist-p (mv-nth 1 (sd-filter-problems x major minor)))))))






(defund vl-modwarningalist-types (x)
  (declare (xargs :guard (vl-modwarningalist-p x)))
  (if (atom x)
      nil
    (append (vl-warninglist->types (cdar x))
            (vl-modwarningalist-types (cdr x)))))


(defund vl-keep-from-modwarningalist (types x)
  ;; Returns a new fast alist.
  (declare (xargs :guard (and (symbol-listp types)
                              (vl-modwarningalist-p x))))
  (if (atom x)
      nil
    (b* ((name1     (caar x))
         (warnings1 (cdar x))
         (keep1     (vl-keep-warnings types warnings1))
         (rest      (vl-keep-from-modwarningalist types (cdr x))))
      (if keep1
          (hons-acons name1 keep1 rest)
        rest))))

(defthm vl-modwarningalist-p-of-vl-keep-from-modwarningalist
  (implies (force (vl-modwarningalist-p x))
           (vl-modwarningalist-p (vl-keep-from-modwarningalist types x)))
  :hints(("Goal" :in-theory (enable vl-keep-from-modwarningalist))))


(defpp vl-lint-print-warnings (filename label types walist)
  :guard (and (stringp filename)
              (stringp label)
              (symbol-listp types)
              (vl-modwarningalist-p walist))
  :body
  (b* ((walist (vl-keep-from-modwarningalist types walist))
       (walist (vl-clean-modwarningalist walist))
       (count  (length (append-domains walist)))
       (-      (cond ((= count 0)
                      (cw "~s0: No ~s1 Warnings.~%" filename label))
                     ((= count 1)
                      (cw "~s0: One ~s1 Warning.~%" filename label))
                     (t
                      (cw "~s0: ~x1 ~s2 Warnings.~%" filename count label)))))
    (vl-ps-seq
     (cond ((= count 0)
            (vl-cw "No ~s0 Warnings.~%~%" label))
           ((= count 1)
            (vl-cw "One ~s0 Warning:~%~%" label))
           (t
            (vl-cw "~x0 ~s1 Warnings:~%~%" count label)))
     (vl-print-modwarningalist walist))))



(defconst *use-set-warnings*
  (list :use-set-fudging
        :use-set-trainwreck
        :use-set-future-trainwreck
        :use-set-warn-unset
        :use-set-warn-unused
        :use-set-warn-spurious
        :vl-collect-wires-approx
        :vl-collect-wires-fail
        :vl-dropped-always
        :vl-dropped-assign
        :vl-dropped-initial
        :vl-dropped-insts
        :vl-dropped-modinst
        :vl-warn-function
        :vl-warn-taskdecl
        :vl-unsupported-block
        ))


(defconst *warnings-covered*

  ;; Warnings that are covered by our regular reports.  Other warnings besides
  ;; these will get put into vl-other.txt

  (append *use-set-warnings*
          (list
           ;; basic
           :bad-mp-verror
           :vl-bad-range
           :vl-warn-duplicates
           :vl-bad-instance
           :vl-unresolved-hid
           :vl-warn-unused-reg
           :vl-warn-blank
           :vl-undefined-names
           :vl-port-mismatch

           ;; trunc
           :vl-warn-extension
           :vl-warn-truncation
           :vl-warn-extension-minor
           :vl-warn-truncation-minor
           :vl-warn-integer-size
           :vl-warn-integer-size-minor
           :vl-warn-vague-spec

           ;; disconnected
           :vl-warn-disconnected
           :vl-warn-disconnected-interesting
           :vl-collect-wires-fail
           :vl-collect-wires-approx
           :vl-dropped-always
           :vl-dropped-assign
           :vl-dropped-initial
           :vl-dropped-insts
           :vl-dropped-modinst
           :vl-warn-function
           :vl-warn-taskdecl
           :vl-unsupported-block

           ;; smells
           :vl-warn-qmark-width
           :vl-warn-qmark-const
           :vl-warn-leftright
           :vl-warn-selfassign
           :vl-warn-partselect-same

           ;; multidrive
           :vl-warn-multidrive
           :vl-warn-multidrive-minor)))

(defconst *warnings-ignored*

  ;; Warnings that aren't covered but which we don't want to put into vl-other.txt
  ;; anyway.

  (list
   :vl-warn-taskdecl
   :vl-warn-function

   ))

(defun vl-lint-report (walist sd-probs state)
  (declare (xargs :guard (and (vl-modwarningalist-p walist)
                              (sd-problemlist-p sd-probs))
                  :mode :program
                  :stobjs state))

  (b* (((mv major minor) (sd-filter-problems sd-probs nil nil))
       (major (reverse major))
       (minor (reverse minor))

       (- (cw "~%vl-lint: saving results...~%~%"))

       (othertypes  (difference (mergesort (vl-modwarningalist-types walist))
                                (mergesort (append *warnings-covered*
                                                   *warnings-ignored*))))

       (state
        (with-ps-file
         "vl-basic.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-basic.txt"
                                 "Basic"
                                 '(:bad-mp-verror
                                   :vl-bad-range
                                   :vl-warn-duplicates
                                   :vl-bad-instance
                                   :vl-unresolved-hid
                                   :vl-warn-unused-reg
                                   :vl-undefined-names
                                   :vl-warn-blank
                                   :vl-port-mismatch
                                   )
                                 walist)))

       (state
        (with-ps-file
         "vl-trunc.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-print "
NOTE: see the bottom of this file for an explanation of what these warnings
mean and how to avoid them.

")

         (vl-lint-print-warnings "vl-trunc.txt"
                                 "Truncation/Extension"
                                 '(:vl-warn-extension
                                   :vl-warn-truncation
                                   :vl-warn-integer-size)
                                 walist)

         (vl-print "

UNDERSTANDING THESE WARNINGS.

1. VL-WARN-TRUNCATION warnings are issued when the left-hand side of an
assignment statement is not as wide as the right-hand side.

False positives here can typically be suppressed by using part-selects to make
the intended truncations explicit.  For instance:

    wire [47:0] foo ;
    wire [63:0] bar ;

    assign foo = bar ;        // implicit truncation, causes warning
    assign foo = bar[47:0] ;  // explicit truncation, no warning

    assign foo = condition ? bar : 0 ;      // implicit truncation, causes warning
    assign foo = condition ? bar[47:0] : 0; // explicit truncation, no warning


2. VL-WARN-EXTENSION warnings are the opposite: they are issued when the
left-hand side is wider than the right-hand side would have been on its own.

False-positives can again typically be suppressed by explicitly concatenting in
zeroes, or by using part-selects to cut the left-hand side to the right size.
For instance:

    wire [47:0] foo ;
    wire [63:0] bar ;

    assign bar = foo ;             // implicit extension, causes warning
    assign bar = { 16'b0, foo } ;  // explicit extension, no warning
    assign bar[47:0] = foo;        // no extension, no warning


Note that we consider certain truncation and extension warnings to be \"minor\"
and do not report them here.  Such warnings are unlikely to be a problem, but
you can see \"vl-trunc-minor.txt\" to review them.")))

       (state
        (with-ps-file
         "vl-disconnected.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-disconnected.txt"
                                 "Disconnected Wire"
                                 '(:vl-warn-disconnected
                                   :vl-warn-disconnected-interesting
                                   ;; Caveats that could make the analysis wrong
                                   :vl-collect-wires-fail
                                   :vl-collect-wires-approx
                                   :vl-dropped-always
                                   :vl-dropped-assign
                                   :vl-dropped-initial
                                   :vl-dropped-insts
                                   :vl-dropped-modinst
                                   :vl-warn-function
                                   :vl-warn-taskdecl
                                   :vl-unsupported-block)
                                 walist)))

       (state
        (with-ps-file
         "vl-multi.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-multi.txt"
                                 "Multidrive"
                                 '(:vl-warn-multidrive)
                                 walist)))

       (state
        (if (not major)
            (progn$
             (cw "; No Skip-Detect Warnings.~%")
             state)
          (progn$
           (cw "vl-skipdet.txt: ~x0 Skip-Detect Warnings.~%" (len major))
           (with-ps-file "vl-skipdet.txt"
                         (vl-ps-update-autowrap-col 68)
                         (vl-cw "Skip-Detect Warnings.~%~%")
                         (sd-pp-problemlist-long major)))))

       (state
        (with-ps-file
         "vl-trunc-minor.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-print "
NOTE: see the bottom of this file for an explanation of what these warnings
mean and how to avoid them.

")
         (vl-lint-print-warnings "vl-trunc-minor.txt"
                                 "Minor Truncation/Extension"
                                 '(:vl-warn-extension-minor
                                   :vl-warn-truncation-minor
                                   :vl-warn-integer-size-minor
                                   :vl-warn-vague-spec)
                                 walist)
         (vl-print "

UNDERSTANDING THESE WARNINGS.

1.  VL-WARN-TRUNCATION-32 warnings are generated for any assignments that are
being truncated and whose right-hand sides are 32-bits wide.  This is a minor
warning because it typically arises from assignments where plain integers are
involved, e.g., if foo and bar are 10 bits wide, then a truncation-32 warning
will be generated for:

    assign foo = bar ^ 5;

This is because \"5\" has an implementation-dependent width (of at least 32
bits), and in VL-Lint we treat it as being 32-bits wide.  So, the above
describes a 32-bit XOR that is then truncated down to 10 bits.  Fixing these
warnings is usually easy: just explicitly specify the sizes of the numbers
involved, e.g., a \"corrected\" version might be:

    assign foo = bar ^ 10'd 5;

This is generally a good idea since it avoids any implementation-dependent
sizing (which can occasionally affect the results of expressions).


2.  VL-WARN-EXTENSION-MINOR warnings are generated for any assignments where
the width of the left-hand side is used to size the expression, and where the
right-hand side involves only addition operations.  For instance, given:

    wire [9:0] foo;
    wire [9:0] bar;
    wire [9:0] sum;
    wire carry;

Then an assignment like this:

    assign { carry, sum } = foo + bar;

would result in a minor extension warning.  These warnings are typically quite
minor since you frequently want to get the carry out of a sum.  But you could
suppress them by writing something like this:

    Variant 1: assign {carry, sum} = {1'b0,foo} + bar;
    Variant 2: assign {carry, sum} = foo + bar + 11'b0;

or similar, to make explicit on the right-hand side that you want an 11-bit
wide addition instead of a 10-bit wide addition.")))

       (state
        (with-ps-file
         "vl-multi-minor.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-multi-minor.txt"
                                 "Minor Multidrive"
                                 '(:vl-warn-multidrive-minor)
                                 walist)))

       (state
        (if (not minor)
            (prog2$
             (cw "; No Minor Skip-Detect Warnings.~%")
             state)
          (prog2$
           (cw "vl-skipdet-minor.txt: ~x0 Minor Skip-Detect Warnings.~%" (len minor))
           (with-ps-file "vl-skipdet-minor.txt"
                         (vl-ps-update-autowrap-col 68)
                         (vl-cw "Minor Skip-Detect Warnings.~%~%")
                         (sd-pp-problemlist-long minor)))))


       (state
        (with-ps-file
         "vl-use-set.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-use-set.txt"
                                 "Unused/Unset Wire Warnings"
                                 *use-set-warnings*
                                 walist)))


       (state
        (with-ps-file
         "vl-smells.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-smells.txt"
                                 "Code-Smell Warnings"
                                 '(:vl-warn-qmark-width
                                   :vl-warn-qmark-const
                                   :vl-warn-leftright
                                   :vl-warn-selfassign
                                   :vl-warn-instances-same
                                   )
                                 walist)))

       (state
        (with-ps-file
         "vl-smells-minor.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-smells-minor.txt"
                                 "Minor Code-Smell Warnings"
                                 '(:vl-warn-partselect-same
                                   :vl-warn-instances-same-minor)
                                 walist)))

       (state
        (with-ps-file
         "vl-other.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-other.txt"
                                 "Other/Unclassified"
                                 othertypes
                                 walist)))

       (- (cw "~%")))

    state))


(encapsulate
  ()
  (defttag vl-lint)
  (remove-untouchable acl2::writes-okp nil))

(defmacro vl-lint (&key start-files search-path
                        (searchext ''("v"))
                        ;; gross yucky thing; suppress defaults to all ACL2
                        ;; output, but for debugging use :suppress nil to be
                        ;; able to see what is wrong.
                        top-mods
                        (suppress ':all))
  (declare (ignorable start-files search-path searchext suppress))
  `(with-output
    :off ,(or suppress 'proof-tree)
    (make-event
     (b* ((- (acl2::set-max-mem (* 12 (expt 2 30))))
          (- (acl2::hons-resize :str-ht 1000000))
          ((mv & & state)
           ;; For some reason we have to assign to this here, inside the
           ;; make-event code, rather than ahead of time.
           (assign acl2::writes-okp t))
          ((mv ?mods ?mods0 ?mwalist ?sd-probs ?dalist ?state)
           (cwtime (run-vl-lint ,start-files ,search-path ,searchext ,top-mods state)
                   :name vl-lint))
          (state (vl-lint-report mwalist sd-probs state)))
       (value `(progn (defconst *mods* ',mods)
                      (defconst *mods0* ',mods0)
                      (defconst *mwalist* ',mwalist)
                      (defconst *sd-probs* ',sd-probs)
                      (defconst *dalist* ',dalist)
                      ))))))





