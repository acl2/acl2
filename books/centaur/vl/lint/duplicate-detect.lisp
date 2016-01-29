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
(include-book "../mlib/writer")
(include-book "../mlib/strip")
(include-book "../mlib/expr-tools")
(local (include-book "../util/arithmetic"))

(defsection duplicate-detect
  :parents (vl-lint)
  :short "Check for instances and assignments that are literally identical."

  :long "<p>This is a heuristic for generating warnings.  We look for
assignments, module instances, and gate instances that are identical up to
<i>stripping</i> as described in @(see stripping-functions).  These sorts of
things might well be copy/paste errors.</p>")

(local (xdoc::set-default-parents duplicate-detect))


(define vl-duplicate-detect-strip-gateinst ((x vl-gateinst-p))
  :returns (stripped-x vl-gateinst-p)
  :short "Strip more from a @(see vl-gateinst) for @(see duplicate-detect)."
  :long "<p>We could just use @(see vl-gateinst-strip) to eliminate attributes
         and location info, but then gates could still differ by names and
         delays.  It seems like we probably still want to warn about things
         like</p>

         @({
             and g1 (o, a, b);
             and g2 (o, a, b);
         })

         <p>Also note that @(see annotate) adds names to gate instances anyway,
         so unnamed gates wouldn't be flagged as duplicates unless we do
         something more here.</p>"
  (change-vl-gateinst (vl-gateinst-strip x)
                      :name nil
                      :delay nil))

(defprojection vl-duplicate-detect-strip-gateinsts ((x vl-gateinstlist-p))
  :returns (stripped-x vl-gateinstlist-p)
  (vl-duplicate-detect-strip-gateinst x))


(define vl-duplicate-detect-strip-modinst ((x vl-modinst-p))
  :returns (stripped-x vl-modinst-p)
  :short "Strip more from a @(see vl-modinst) for @(see duplicate-detect)."
  (change-vl-modinst (vl-modinst-strip x)
                     :instname nil
                     :str nil
                     :delay nil))

(defprojection vl-duplicate-detect-strip-modinsts ((x vl-modinstlist-p))
  :returns (stripped-x vl-modinstlist-p)
  (vl-duplicate-detect-strip-modinst x))

(defprojection vl-duplicate-detect-strip-aliases ((x vl-aliaslist-p))
  :returns (stripped-x vl-aliaslist-p)
  (vl-alias-strip x))

(defprojection vl-duplicate-detect-strip-alwayses ((x vl-alwayslist-p))
  :returns (stripped-x vl-alwayslist-p)
  (vl-always-strip x))

(defprojection vl-duplicate-detect-strip-initials ((x vl-initiallist-p))
  :returns (stripped-x vl-initiallist-p)
  (vl-initial-strip x))

(defprojection vl-duplicate-detect-strip-assigns ((x vl-assignlist-p))
  :returns (stripped-x vl-assignlist-p)
  (vl-assign-strip x))

(defprojection vl-duplicate-detect-strip-finals ((x vl-finallist-p))
  :returns (stripped-x vl-finallist-p)
  (vl-final-strip x))

(defprojection vl-duplicate-detect-strip-properties ((x vl-propertylist-p))
  :returns (stripped-x vl-propertylist-p)
  (vl-property-strip x))

(defprojection vl-duplicate-detect-strip-sequences ((x vl-sequencelist-p))
  :returns (stripped-x vl-sequencelist-p)
  (vl-sequence-strip x))

(defprojection vl-duplicate-detect-strip-assertions ((x vl-assertionlist-p))
  :returns (stripped-x vl-assertionlist-p)
  (vl-assertion-strip x))

(defprojection vl-duplicate-detect-strip-cassertions ((x vl-cassertionlist-p))
  :returns (stripped-x vl-cassertionlist-p)
  (vl-cassertion-strip x))


(define vl-duplicate-warning ((type  stringp)
                              (dupes vl-modelementlist-p))
  :guard (<= 2 (len dupes))
  :returns (warning vl-warning-p)
  (b* ((msg (with-local-ps
              (vl-ps-update-autowrap-col 100)
              (vl-ps-update-autowrap-ind 10)
              (vl-print "Found duplicated ")
              (vl-print-str type)
              (vl-println ":")
              (vl-indent 6)
              (vl-print "  // From ")
              (vl-print-loc (vl-modelement->loc (first dupes)))
              (vl-println "")
              (vl-indent 6)
              (vl-pp-modelement (first dupes))
              (vl-indent 6)
              (vl-print "  // From ")
              (vl-print-loc (vl-modelement->loc (second dupes)))
              (vl-println "")
              (vl-indent 6)
              (vl-pp-modelement (second dupes))
              (if (atom (cddr dupes))
                  ps
                (vl-ps-seq (vl-println "")
                           (vl-indent 6)
                           (vl-print "  // And ")
                           (vl-print-nat (- (len dupes) 2))
                           (vl-print " more."))))))
    (make-vl-warning
     :type :vl-warn-duplicates
     :msg  "~s0"
     :args (list msg dupes)
     :fatalp nil
     :fn __function__)))

(define vl-collect-original-elements-matching-dupe
  ((dupe  vl-modelement-p     "Some element that was duplicated (stripped).")
   (fixed vl-modelementlist-p "Stripped versions of @('orig')")
   (orig  vl-modelementlist-p "Original module elements, before stripping."))
  :guard (same-lengthp fixed orig)
  :returns (matches vl-modelementlist-p "Original elements that match @('dupe').")
  (b* (((when (atom fixed))
        nil)
       (rest  (vl-collect-original-elements-matching-dupe dupe (cdr fixed) (cdr orig)))
       ((when (equal dupe (car fixed)))
        (cons (vl-modelement-fix (car orig)) rest)))
    rest))

(define vl-duplicate-warnings ((dupes vl-modelementlist-p "The duplicated (stripped) elements.")
                               (fixed vl-modelementlist-p "The stripped versions of @('orig').")
                               (orig  vl-modelementlist-p "Original elements (before fixing)."))
  :guard (same-lengthp fixed orig)
  :returns (warnings vl-warninglist-p "Warnings for each duplicate modinst.")
  (b* (((when (atom dupes))
        nil)
       (matches (vl-collect-original-elements-matching-dupe (car dupes) fixed orig))
       ((unless (<= 2 (len matches)))
        (raise "Not enough matches for duplicate?  Jared thinks this should be impossible."))
       (warning (vl-duplicate-warning (case (tag (car dupes))
                                        (:vl-modinst    "module instances")
                                        (:vl-assign     "assignments")
                                        (:vl-gateinst   "gate instances")
                                        (:vl-alias      "aliases")
                                        (:vl-always     "always blocks")
                                        (:vl-initial    "initial blocks")
                                        (:vl-final      "final statements")
                                        (:vl-property   "property declarations")
                                        (:vl-sequence   "sequence declarations")
                                        (:vl-assertion  "immediate assertions")
                                        (:vl-cassertion "concurrent assertions")
                                        (otherwise
                                         (ec-call (symbol-name (tag (car dupes))))))
                                      matches))
       (rest    (vl-duplicate-warnings (cdr dupes) fixed orig)))
    (cons warning rest)))

(define vl-modinstlist-remove-interfaces ((x vl-modinstlist-p)
                                          (ss vl-scopestack-p))
  :returns (filtered-x vl-modinstlist-p)
  :prepwork ((local (in-theory (enable tag-reasoning))))
  (b* (((when (atom x))
        nil)
       (dfn (vl-scopestack-find-definition (vl-modinst->modname (car x)) ss))
       ((when (mbe :logic (vl-interface-p dfn)
                   :exec (eq (tag dfn) :vl-interface)))
        (vl-modinstlist-remove-interfaces (cdr x) ss)))
    (cons (vl-modinst-fix (car x))
          (vl-modinstlist-remove-interfaces (cdr x) ss))))

(define vl-module-duplicate-detect ((x  vl-module-p)
                                    (ss vl-scopestack-p))
  :short "Detect duplicate assignments and instances throughout a module."
  :returns (new-x vl-module-p "Same as @('x'), but perhaps with more warnings.")
  :prepwork (;; BOZO why is this still enabled?
             (local (in-theory (disable acl2::true-listp-append))))
  (b* (((vl-module x) (vl-module-fix x))
       (ss (vl-scopestack-push x ss))

       (modinsts       (vl-modinstlist-remove-interfaces x.modinsts ss))

       (gateinsts-fix  (vl-duplicate-detect-strip-gateinsts x.gateinsts))
       (modinsts-fix   (vl-duplicate-detect-strip-modinsts modinsts))
       (assigns-fix    (vl-duplicate-detect-strip-assigns x.assigns))
       (always-fix     (vl-duplicate-detect-strip-alwayses x.alwayses))
       (initial-fix    (vl-duplicate-detect-strip-initials x.initials))
       (final-fix      (vl-duplicate-detect-strip-finals x.finals))
       (alias-fix      (vl-duplicate-detect-strip-aliases x.aliases))
       (assert-fix     (vl-duplicate-detect-strip-assertions x.assertions))
       (cassert-fix    (vl-duplicate-detect-strip-cassertions x.cassertions))
       (property-fix   (vl-duplicate-detect-strip-properties x.properties))
       (sequence-fix   (vl-duplicate-detect-strip-sequences x.sequences))

       (gateinst-dupes (duplicated-members gateinsts-fix))
       (modinst-dupes  (duplicated-members modinsts-fix))
       (assign-dupes   (duplicated-members assigns-fix))
       (always-dupes   (duplicated-members always-fix))
       (initial-dupes  (duplicated-members initial-fix))
       (final-dupes    (duplicated-members final-fix))
       (alias-dupes    (duplicated-members alias-fix))
       (assert-dupes   (duplicated-members assert-fix))
       (cassert-dupes  (duplicated-members cassert-fix))
       (property-dupes (duplicated-members property-fix))
       (sequence-dupes (duplicated-members sequence-fix))

       (gateinst-warnings (vl-duplicate-warnings gateinst-dupes gateinsts-fix x.gateinsts))
       (modinst-warnings  (vl-duplicate-warnings modinst-dupes modinsts-fix modinsts))
       (assign-warnings   (vl-duplicate-warnings assign-dupes assigns-fix x.assigns))
       (always-warnings   (vl-duplicate-warnings always-dupes always-fix x.alwayses))
       (initial-warnings  (vl-duplicate-warnings initial-dupes initial-fix x.initials))
       (final-warnings    (vl-duplicate-warnings final-dupes final-fix x.finals))
       (alias-warnings    (vl-duplicate-warnings alias-dupes alias-fix x.aliases))
       (assert-warnings   (vl-duplicate-warnings assert-dupes assert-fix x.assertions))
       (cassert-warnings  (vl-duplicate-warnings cassert-dupes cassert-fix x.cassertions))
       (property-warnings (vl-duplicate-warnings property-dupes property-fix x.properties))
       (sequence-warnings (vl-duplicate-warnings sequence-dupes sequence-fix x.sequences))

       (warnings (append gateinst-warnings
                         modinst-warnings
                         assign-warnings
                         always-warnings
                         initial-warnings
                         final-warnings
                         alias-warnings
                         assert-warnings
                         cassert-warnings
                         property-warnings
                         sequence-warnings
                         x.warnings)))

    (change-vl-module x :warnings warnings)))

(defprojection vl-modulelist-duplicate-detect ((x  vl-modulelist-p)
                                               (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-duplicate-detect x ss))

(define vl-design-duplicate-detect
  :short "Top-level @(see duplicate-detect) check."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))
       (ss (vl-scopestack-init x))
       (new-mods (vl-modulelist-duplicate-detect x.mods ss)))
    (vl-scopestacks-free)
    (clear-memoize-table 'vl-expr-strip)
    (change-vl-design x :mods new-mods)))


