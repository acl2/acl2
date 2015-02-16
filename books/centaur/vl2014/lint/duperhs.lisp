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
(include-book "../mlib/strip")
(include-book "../mlib/expr-tools")
(include-book "../mlib/writer")
(local (include-book "../util/arithmetic"))

(defxdoc duperhs-check
  :parents (lint)
  :short "Check for assignments with the same right-hand side."
  :long "<p>This is a trivially simple check for cases like:</p>

@({
   assign a = rhs;
   assign b = rhs;
})

<p>That is, where @('rhs') is literally identical in both assignments.  Such
assignments are not necessarily errors, but are kind of odd.</p>")

(local (xdoc::set-default-parents duperhs-check))

(defalist vl-duperhs-alistp (x)
  :key (vl-expr-p x)        ;; Fixed up RHS
  :val (vl-assignlist-p x)  ;; Assignments that map to this RHS
  :keyp-of-nil nil
  :valp-of-nil t)

(define vl-make-duperhs-alist-aux ((x     vl-assignlist-p)
                                   (alist vl-duperhs-alistp))
  :returns (new-alist vl-duperhs-alistp :hyp :guard)
  (b* (((when (atom x))
        alist)
       (x1 (car x))
       ((vl-assign x1) x1)
       (rhs1 (hons-copy (vl-expr-strip x1.expr)))
       (look (hons-get rhs1 alist))
       ;; It doesn't matter if it exists or not, just add it in.
       (alist (hons-acons rhs1 (cons x1 (cdr look)) alist)))
    (vl-make-duperhs-alist-aux (cdr x) alist)))

(define vl-make-duperhs-alist ((x vl-assignlist-p))
  :returns (alist "A slow alist."vl-duperhs-alistp :hyp :fguard)
  :short "Builds the @(see vl-duperhs-alistp) for a list of assignments."
  (b* ((alist (len x))
       (alist (vl-make-duperhs-alist-aux x alist))
       (ans   (hons-shrink-alist alist nil)))
    (fast-alist-free alist)
    (fast-alist-free ans)
    ans))

(define vl-duperhs-too-trivial-p
  ((rhs vl-expr-p "The rhs shared by some list of assignments."))
  :returns (trivial-p "Is this too trivial to warn about?"
                      booleanp :rule-classes :type-prescription)
  :short "Heuristic to avoid warning about assigning simple, common right-hand
sides to multiple wires."

  :long "<p>It seems fine to assign a constant, weirdint, real, or string to
multiple wires; this is especially frequent for things like 0 and 1, so we
don't want to warn in these cases.</p>

<p>We'll just suppress warnings for any atoms other than identifiers.  This
will allow us to still flag situations like:</p>

@({
     assign wire1 = wirefoo;
     assign wire2 = wirefoo;
})

<p>I later decided I wanted to extend this, and additionally not cause warnings
for odd but innocuous things like @('~ 1'b0') and @('{1'b0}').</p>"

  (b* (((when (vl-fast-atom-p rhs))
        (not (vl-fast-id-p (vl-atom->guts rhs))))
       ((vl-nonatom rhs) rhs))
    (and (or (eq rhs.op :vl-unary-bitnot)
             (eq rhs.op :vl-concat))
         (tuplep 1 rhs.args)
         (vl-fast-atom-p (first rhs.args))
         (not (vl-fast-id-p (vl-atom->guts (first rhs.args)))))))

(define vl-maybe-warn-duperhs
  :short "Create warnings for assignments that share some RHS."
  ((rhs      vl-expr-p        "The shared RHS among all these assignments")
   (assigns  vl-assignlist-p  "A list of assignments that share this RHS.")
   (warnings vl-warninglist-p "A warnings accumulator to extend."))
  :returns (new-warnings vl-warninglist-p)
  (b* (((when (or (atom assigns)
                  (atom (cdr assigns))))
        ;; Nothing to do -- there isn't more than one assignment for this RHS.
        (ok))

       ((when (vl-duperhs-too-trivial-p rhs))
        (ok))

       (rhs-names (vl-expr-names rhs))
       (special-names (append (str::collect-strs-with-isubstr "ph1" rhs-names)
                              (str::collect-strs-with-isubstr "reset" rhs-names)
                              (str::collect-strs-with-isubstr "clear" rhs-names)
                              (str::collect-strs-with-isubstr "enable" rhs-names)
                              (str::collect-strs-with-isubstr "clken" rhs-names)
                              (str::collect-strs-with-isubstr "valid" rhs-names)
                              ))
       ((when (consp special-names))
        ;; It's common for the same expression to be used multiple times for
        ;; clock enables and for a clock to go multiple places, so try to
        ;; filter this out.
        (ok)))

    ;; BOZO maybe filter out other things? (reset, done, clear, stuff like
    ;; that, by name?)
    (warn :type :vl-warn-same-rhs
          :msg "Found assignments that have exactly the same right-hand side, ~
                which might indicate a copy/paste error:~%~s0"
          :args (list (str::prefix-lines (with-local-ps
                                          ;; may help avoid unnecessary line wrapping
                                          (vl-ps-update-autowrap-col 200)
                                          (vl-pp-assignlist assigns))
                                         "     ")
                      ;; These aren't printed, but we include them in the
                      ;; warning so our warning-suppression mechanism can be
                      ;; applied.
                      assigns))))

(define vl-warnings-for-duperhs-alist
  ((alist    vl-duperhs-alistp  "The duperhs alist we've built for some module.")
   (warnings vl-warninglist-p   "A warnings accumulator to extend."))
  :returns (new-warnings vl-warninglist-p)
  (b* (((when (atom alist))
        (ok))
       (rhs      (caar alist))
       (assigns  (cdar alist))
       (warnings (vl-maybe-warn-duperhs rhs assigns warnings)))
    (vl-warnings-for-duperhs-alist (cdr alist) warnings)))

(define vl-module-duperhs-check ((x vl-module-p))
  :short "Look for duplicated rhses in a module, and add warnings about them."
  :returns (new-x "A copy of X, perhaps extended with new warnings."
                  vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       (alist    (vl-make-duperhs-alist x.assigns))
       (warnings (vl-warnings-for-duperhs-alist alist x.warnings)))
    (change-vl-module x :warnings warnings)))

(defprojection vl-modulelist-duperhs-check (x)
  (vl-module-duperhs-check x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-duperhs-check ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x)
       (new-mods (vl-modulelist-duperhs-check x.mods)))
    (clear-memoize-table 'vl-expr-strip)
    (change-vl-design x :mods new-mods)))

