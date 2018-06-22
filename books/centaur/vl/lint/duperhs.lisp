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
(include-book "../mlib/strip")
(include-book "../mlib/expr-tools")
(include-book "../mlib/writer")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc duperhs-check
  :parents (vl-lint)
  :short "Check for assignments with the same right-hand side."
  :long "<p>This is a trivially simple check for cases like:</p>

@({
   assign a = rhs;
   assign b = rhs;
})

<p>That is, where @('rhs') is literally identical in both assignments.  Such
assignments are not necessarily errors, but are kind of odd.</p>")

(local (xdoc::set-default-parents duperhs-check))

(fty::defalist vl-duperhs-alist
  :key-type vl-expr-p       ;; Fixed up RHS
  :val-type vl-assignlist-p ;; Assignments that map to this RHS
  )

(define vl-make-duperhs-alist-aux ((x     vl-assignlist-p)
                                   (alist vl-duperhs-alist-p))
  :returns (new-alist vl-duperhs-alist-p)
  (b* ((alist (vl-duperhs-alist-fix alist))
       ((when (atom x))
        alist)
       ((vl-assign x1) (vl-assign-fix (car x)))
       (rhs1 (hons-copy (vl-expr-strip x1.expr)))
       (look (hons-get rhs1 alist))
       ;; It doesn't matter if it exists or not, just add it in.
       (alist (hons-acons rhs1 (cons x1 (cdr look)) alist)))
    (vl-make-duperhs-alist-aux (cdr x) alist)))

(define vl-make-duperhs-alist ((x vl-assignlist-p))
  :returns (alist vl-duperhs-alist-p "A slow alist.")
  :short "Builds the @(see vl-duperhs-alist-p) for a list of assignments."
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

  (vl-expr-case rhs
    :vl-literal t
    :vl-unary (and (vl-unaryop-equiv rhs.op :vl-unary-bitnot)
                   (vl-expr-case rhs.arg :vl-literal))
    :vl-concat (and (tuplep 1 rhs.parts)
                    (let ((arg (first rhs.parts)))
                      (vl-expr-case arg :vl-literal)))
    :vl-multiconcat
    ;; This recognizes things like {7{1'b0}} or {8{1'b1}}, etc., which are very
    ;; unlikely to be any kind of problem.
    (and (vl-expr-resolved-p rhs.reps)
         (tuplep 1 rhs.parts)
         (let ((arg (first rhs.parts)))
           (vl-expr-case arg :vl-literal)))
    :otherwise nil))


(define vl-maybe-warn-duperhs
  :short "Create warnings for assignments that share some RHS."
  ((rhs      vl-expr-p        "The shared RHS among all these assignments")
   (assigns  vl-assignlist-p  "A list of assignments that share this RHS.")
   (warnings vl-warninglist-p "A warnings accumulator to extend."))
  :returns (new-warnings vl-warninglist-p)
  (b* ((assigns (vl-assignlist-fix assigns))
       ((when (or (atom assigns)
                  (atom (cdr assigns))))
        ;; Nothing to do -- there isn't more than one assignment for this RHS.
        (ok))

       ((when (vl-duperhs-too-trivial-p rhs))
        (ok))

       (rhs-names (vl-expr-varnames rhs))
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
  ((alist    vl-duperhs-alist-p  "The duperhs alist we've built for some module.")
   (warnings vl-warninglist-p   "A warnings accumulator to extend."))
  :returns (new-warnings vl-warninglist-p)
  :measure (len (vl-duperhs-alist-fix alist))
  (b* ((alist (vl-duperhs-alist-fix alist))
       ((when (atom alist))
        (ok))
       (rhs      (caar alist))
       (assigns  (cdar alist))
       (warnings (vl-maybe-warn-duperhs rhs assigns warnings)))
    (vl-warnings-for-duperhs-alist (cdr alist) warnings)))

(define vl-module-duperhs-check ((x vl-module-p))
  :short "Look for duplicated rhses in a module, and add warnings about them."
  :returns (new-x "A copy of X, perhaps extended with new warnings."
                  vl-module-p)
  (b* (((vl-module x) x)
       (alist    (vl-make-duperhs-alist x.assigns))
       (warnings (vl-warnings-for-duperhs-alist alist x.warnings)))
    (change-vl-module x :warnings warnings)))

(defprojection vl-modulelist-duperhs-check ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-duperhs-check x))

(define vl-design-duperhs-check ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (new-mods (vl-modulelist-duperhs-check x.mods)))
    (clear-memoize-table 'vl-expr-strip)
    (change-vl-design x :mods new-mods)))

