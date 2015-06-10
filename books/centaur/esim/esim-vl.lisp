; ESIM Symbolic Hardware Simulator
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


; esim-vl.lisp -- integration of VL and ESIM
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "esim-sexpr-support")
(include-book "vltoe/wirealist")
(local (include-book "std/lists/all-equalp" :dir :system))

(defsection esim-vl
  :parents (acl2::esim vl2014)
  :short "Functions for working with E modules produced by VL.")


(local (defthm consp-of-assoc-equal
         (implies (alistp al)
                  (equal (consp (assoc-equal key al))
                         (if (assoc-equal key al)
                             t
                           nil)))
         :hints(("Goal" :in-theory (enable assoc-equal)))))


(defsection esim-vl-annotations
  :parents (esim-vl)
  :short "Helper for @(see esim-vl-designwires) and @(see esim-vl-wirealist)."

  (defund esim-vl-annotations (mod)
    (declare (xargs :guard t))
    (b* ((name (acl2::gpl :n mod))
         ((unless name)
          (er hard? 'esim-vl-annotations
              "Expected an E module, but this object doesn't even have a :n ~
               field: ~x0.~%" mod))
         (annotations (acl2::gpl :a mod))
         ((unless (alistp annotations))
          (er hard? 'esim-vl-annotations
              "In E module ~s0, the annotations field :a is not an alist."
              name)))
      annotations))

  (local (in-theory (enable esim-vl-annotations)))

  (defthm alistp-of-esim-vl-annotations
    (alistp (esim-vl-annotations mod))))



(defsection esim-vl-designwires
  :parents (esim-vl)
  :short "Produce a flat @(see vl-emodwirelist-p) that contains the E names
of every bit that is visible in the original Verilog module."

  :long "<p>@(call esim-vl-designwires) is given an E module and returns an
@(see vl-emodwirelist-p).</p>

<p>This list should include the E names for every bit that is declared in the
original Verilog module; see VL's @(see designwires) transform.  It should
<b>not</b> include the new, intermediate wire names that VL generates during
transformations like @(see split) and @(see occform).  Note that some of the
names in this list might be unused, and hence might not occur in the @('occs')
of the module.</p>

<p>Run-time checks ensure that the @(':design-wires') attribute of the module
contains a valid @(see vl-emodwirelist-p).  This should work for any E module
produced by VL, but may cause an error if used on other modules.  We @(see
memoize) the function to minimize the expense of these checks.</p>"

  (defund esim-vl-designwires (mod)
    (declare (xargs :guard t))
    (b* ((name        (acl2::gpl :n mod))
         (annotations (esim-vl-annotations mod))
         (lookup      (assoc :design-wires annotations))
         ((unless lookup)
          ;; Print a warning unless it's expected that there aren't any design
          ;; wires here.  We've rigged things up so that all of the VL
          ;; primitives have :x fields, whereas everything else (even generated
          ;; modules like VL_4_BIT_PLUS) has the regular annotations.  So, it
          ;; should be sufficient to just check for :x to decide if this is
          ;; worth warning about.  If you change this, also change
          ;; esim-vl-wirealist below.
          (if (acl2::gpl :x mod)
              nil
            (cw "Note: E module ~s0 has no :design-wires annotation!~%" name)))
         (dwires (cdr lookup))
         ((unless (vl-emodwirelist-p dwires))
          (er hard? 'esim-vl-designwires
              "In E module ~s0, :design-wires fails vl-emodwirelist-p check"
              name)))
      dwires))

  (local (in-theory (enable esim-vl-designwires)))

  (defthm vl-emodwirelist-p-of-esim-vl-designwires
    (vl-emodwirelist-p (esim-vl-designwires mod)))

  (memoize 'esim-vl-designwires))


(defsection esim-vl-wirealist
  :parents (esim-vl)
  :short "Obtain the @(see vl-wirealist-p) for an E module produced by VL."

  :long "<p>@(call esim-vl-wirealist) returns a @('vl-wirealist-p').</p>

<p>This is the \"final\" wirealist for the module, and typically will include
temporary wires introduced by VL.  The wirealist will be @('nil') for certain
primitive modules.</p>

<p>Run-time checks ensure the @(':wire-alist') annotation of the module is a
valid wirealist.  This should work for any E module produced by VL, but it may
cause an error if used on other modules.  We @(see memoize) the function to
minimize the expense of these checks.</p>"

  (defund esim-vl-wirealist (mod)
    (declare (xargs :guard t))
    (b* ((name        (acl2::gpl :n mod))
         (annotations (esim-vl-annotations mod))
         (lookup      (assoc :wire-alist annotations))
         ((unless lookup)
          ;; Print a warning unless it's expected that there isn't a wirealist
          ;; here.  See esim-vl-designwires above which includes an analagous
          ;; case.
          (if (acl2::gpl :x mod)
              nil
            (cw "Note: E module ~s0 has no :wire-alist annotation!~%" name)))
         (walist (cdr lookup))
         ((unless (vl-wirealist-p walist))
          (er hard? 'esim-vl-wirealist
              "In E module ~s0, :wire-alist fails vl-wirealist-p check"
              name)))
      walist))

  (local (in-theory (enable esim-vl-wirealist)))

  (defthm vl-wirealist-p-of-esim-vl-wirealist
    (vl-wirealist-p (esim-vl-wirealist mod)))

  ;; Same rationale as for esim-vl-designwires
  (memoize 'esim-vl-wirealist))




(defsection all-equalp-of-vl-emodwirelist->basenames
  :parents (esim-vl-iopattern-p)
  :short "@(call all-equalp-of-vl-emodwirelist->basenames) ensures that all of
the @(see vl-emodwire-p)s in @('x') have this @('basename')."

  (defun all-equalp-of-vl-emodwirelist->basenames (basename x)
    (declare (xargs :guard (and (stringp basename)
                                (vl-emodwirelist-p x))
                    :verify-guards nil))
    (mbe :logic
         (all-equalp basename (vl-emodwirelist->basenames x))
         :exec
         (if (atom x)
             t
           (and (equal basename (vl-emodwire->basename (car x)))
                (all-equalp-of-vl-emodwirelist->basenames basename (cdr x))))))

  (verify-guards all-equalp-of-vl-emodwirelist->basenames
    :hints(("Goal" :in-theory (disable all-equalp)))))


(defsection esim-vl-iopattern-entry-p
  :parents (esim-vl-iopattern-p)
  :short "@(call esim-vl-iopattern-entry-p) recognize lists of @(see
vl-emodwire-p)s like (A[0] A[1] ... A[N]), i.e., non-empty lists of emodwires
with the same basenames and unique indices."

  (defund esim-vl-iopattern-entry-p (x)
    (declare (xargs :guard t))
    (and (consp x)
         (vl-emodwirelist-p x)
         (true-listp x)
         (let ((basename (vl-emodwire->basename (car x))))
           (all-equalp-of-vl-emodwirelist->basenames basename (cdr x)))
         (uniquep (vl-emodwirelist->indices x))))

  (local (in-theory (enable esim-vl-iopattern-entry-p)))

  (defthm vl-emodwirelist-p-when-esim-vl-iopattern-entry-p
    (implies (esim-vl-iopattern-entry-p x)
             (vl-emodwirelist-p x)))

  (defthm consp-when-esim-vl-iopattern-entry-p
    (implies (esim-vl-iopattern-entry-p x)
             (and (true-listp x)
                  (consp x)))
    :rule-classes :compound-recognizer))


(defsection esim-vl-iopattern-entry->basename
  :parents (esim-vl-iopattern-p)
  :short "@(call esim-vl-iopattern-entry->basename) returns the basename that
is shared by all the members of a @(see esim-vl-iopattern-entry-p)."

  :long "<p>For instance, it returns \"A\" for (A[0] A[1] ... A[N]).</p>"

  (defund esim-vl-iopattern-entry->basename (x)
    (declare (xargs :guard (esim-vl-iopattern-entry-p x)))
    (mbe :logic (string-fix (vl-emodwire->basename (car x)))
         :exec (vl-emodwire->basename (car x))))

  (defthm stringp-of-esim-vl-iopattern-entry->basename
    (stringp (esim-vl-iopattern-entry->basename x))
    :rule-classes :type-prescription))


(deflist esim-vl-iopattern-entrylist-p (x)
  (esim-vl-iopattern-entry-p x)
  :guard t
  :elementp-of-nil nil
  :parents (esim-vl-iopattern-p))

(defprojection esim-vl-iopattern-entrylist->basenames (x)
  (esim-vl-iopattern-entry->basename x)
  :guard (esim-vl-iopattern-entrylist-p x)
  :nil-preservingp nil
  :parents (esim-vl-iopattern-p))

(defsection esim-vl-iopattern-p
  :parents (esim-vl)
  :short "Recognize a good @(':i') or @(':o') pattern for a VL-translated
module."

  :long "<p>@(call esim-vl-iopattern-p) is a basic syntax check to make ensure
that @('x') has the proper shape for a @(':i') or @(':o') field of an E module
that VL produces.</p>

<p>Basically, VL writes out @(':i') and @(':o') fields for an E module as
two-level lists of @(see vl-emodwire-p)s.  For instance the @(':i') pattern for
a module whose input declarations are:</p>

@({
 input [3:0] A;
 input B;
 input [0:3] C;
})

<p>Should look like this:</p>

@({
 :i ((A[0] A[1] A[2] A[3])    ;; lsb first
     (B)
     (C[3] C[2] C[1] C[0]))   ;; lsb first
})

<p>See @(see e-conversion) for details.</p>

<p>We @(see memoize) this function to minimize the expense of these checks.
Note that esim-vl-iopattern-p is nonrecursive, so we should only need two memo
table entries per module, one for the @(':i') and one for the @(':o')
entry.</p>"

  (defund esim-vl-iopattern-p (x)
    (declare (xargs :guard t))
    (and (esim-vl-iopattern-entrylist-p x)
         (uniquep (esim-vl-iopattern-entrylist->basenames x))))

  (memoize 'esim-vl-iopattern-p))



(defsection esim-vl-find-io-main
  :parents (esim-vl-find-io)
  :short "@(call esim-vl-find-io-main) finds the first iopattern entry in
@('x') with this @('basename')."

  (defund esim-vl-find-io-main (basename x)
    (declare (xargs :guard (and (stringp basename)
                                (esim-vl-iopattern-entrylist-p x))))
    (cond ((atom x)
           nil)
          ((equal (esim-vl-iopattern-entry->basename (car x)) basename)
           (llist-fix (car x)))
          (t
           (esim-vl-find-io-main basename (cdr x)))))

  (local (in-theory (enable esim-vl-find-io-main)))

  (defthm vl-emodwirelist-p-of-esim-vl-find-io-main
    (implies (esim-vl-iopattern-entrylist-p x)
             (vl-emodwirelist-p (esim-vl-find-io-main basename x))))

  (defthm true-listp-of-esim-vl-find-io-main
    (true-listp (esim-vl-find-io-main basename x))
    :rule-classes :type-prescription))


(defsection esim-vl-find-io
  :parents (esim-vl)
  :short "Produce an LSB-first list of E wire names corresponding to a
particular input or output of the original Verilog module."

  :long "<p>@(call esim-vl-find-io) returns a @(see vl-emodwirelist-p).</p>

<p>The @('basename') is a string that names a wire in the original Verilog
module.  The @('pat') should be either the @(':i') or @(':o') of an E module
that VL has produced.</p>

<p>Example.  If your Verilog module is something like:</p>

@({
 module mymodule (o, a, b);
   input [3:0] a;
   input b;
   ...
 endmodule
})

<p>Then the resulting @(':i') pattern for the E module @('|*mymodule*|') should
be something like:</p>

@({
 :i ((a[0] a[1] a[2] a[3])
     (b))
})

<p>And here are some examples of using @('esim-vl-find-io'):</p>

@({
 (esim-vl-find-io \"a\" (gpl :i |*mymodule*|)) --> (a[0] a[1] a[2] a[3])
 (esim-vl-find-io \"b\" (gpl :i |*mymodule*|)) --> (b)
 (esim-vl-find-io \"c\" (gpl :i |*mymodule*|)) --> NIL
})

<p>On success the list of returned bits is non-empty.  The least significant
bit comes first.  @('NIL') indicates that the wire was not found.</p>

<p>If @('pat') is not a valid i/o pattern for an E module produced by VL, i.e.,
it does not satisfy @(see esim-vl-iopattern-p), a hard error will be
caused.</p>"

  (local (in-theory (enable esim-vl-iopattern-p)))

  (defund esim-vl-find-io (basename pat)
    (declare (xargs :guard (stringp basename)))
    (if (esim-vl-iopattern-p pat) ;; <-- memoized
        (esim-vl-find-io-main basename pat)
      (er hard? 'esim-vl-find-io
          "This doesn't look like a valid I/O pattern for a VL-translated ~
           module: ~x0" pat)))

  (local (in-theory (enable esim-vl-find-io)))

  (defthm vl-emodwirelist-p-of-esim-vl-find-io
    (vl-emodwirelist-p (esim-vl-find-io basename pat)))

  (defthm true-listp-of-esim-vl-find-io
    (true-listp (esim-vl-find-io basename pat))
    :rule-classes :type-prescription))

