; ESIM Symbolic Hardware Simulator
; Copyright (C) 2010-2012 Centaur Technology
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


; stv-util.lisp -- general utilities for the stv compiler
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "../esim-sexpr-support")
(include-book "cutil/defaggregate" :dir :system)

(cutil::defaggregate stvdata
  (initial inputs outputs internals)
  :tag :stvdata
  :require ((true-list-listp-of-stvdata->initial   (true-list-listp initial))
            (true-list-listp-of-stvdata->inputs    (true-list-listp inputs))
            (true-list-listp-of-stvdata->outputs   (true-list-listp outputs))
            (true-list-listp-of-stvdata->internals (true-list-listp internals)))
  :parents (symbolic-test-vectors)
  :short "Temporary internal representation of STV lines during compilation.")

(cutil::defaggregate compiled-stv
  (nphases            ;; number of phases for this simulation
   out-extract-alists ;; what to extract at times 0...{N-1} from outputs
   int-extract-alists ;; what to extract at times 0...{N-1} from internals
   restrict-alist     ;; (init-state -> sexpr) + (input-bit@phase -> sexpr) alist
   in-usersyms        ;; (simulation var -> bit list) alist for INITIAL+INS
   out-usersyms       ;; (simulation var -> bit list) alist for OUTS+INTS
   expanded-ins       ;; not useful for much
   expanded-outs      ;; not useful for much
   expanded-ints      ;; not useful for much
   )
  :tag :compiled-stv
  :require ((posp-of-compiled-stv->nphases
             (posp nphases)
             :rule-classes :type-prescription))
  :parents (symbolic-test-vectors)
  :short "Compiled form of @(see symbolic-test-vectors).")

(cutil::defaggregate processed-stv
  (mod                ;; module
   user-stv           ;; pre-compilation stv
   compiled-stv       ;; post-compilation stv
   relevant-signals   ;; (out/int sim var bit -> sexpr) alist
   )
  :tag :processed-stv
  :parents (stv-process)
  :short "Representation of a processed STV."

  :long "<p>You should probably read @(see stv-implementation-details) to
understand these fields.</p>

<ul>

<li>The @('mod') is the @(see esim) module for this STV.  We save this in the
processed STV so that we re-simulate it later, if necessary, for @(see
stv-debug).</li>

<li>The @('user-stv') is the user-level, pre-compiled STV.  This may be useful
when generating documentation for STVs.</li>

<li>The @('compiled-stv') is a @(see compiled-stv-p) and should be the compiled
version of the user's STV; see @(see stv-compile).</li>

<li>The @('relevant-signals') is an alist computed by @(see stv-process) that
maps each the bits for each internal/output simulation variable to
already-restricted @(see 4v-sexprs).  That is, these s-expressions are
generally in terms of the input simulation variable bits, and ready to be
evaluated by @(see stv-run).</li>

</ul>

<p>Historically we had another field that could also optionally store
pre-computed snapshots for debugging.  We took this out because it could make
@(see stv-run) a lot slower during GL proofs.  The snapshots were huge, and
this really slowed down GL's gl-concrete-lite check.</p>"

  :require ((compiled-stv-p-of-processed-stv->compiled-stv
             (compiled-stv-p compiled-stv))))


(defund ordered-subsetp (x y)
  ;; BOZO find me a home
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (if (equal (car x) (car y))
               (ordered-subsetp (cdr x) (cdr y))
             (ordered-subsetp x (cdr y))))
    t))

(defund intern-list-in-package-of-symbol (x y)
  ;; BOZO find me a home
  (declare (xargs :guard (and (string-listp x)
                              (symbolp y))))
  (if (atom x)
      nil
    (cons (intern-in-package-of-symbol (car x) y)
          (intern-list-in-package-of-symbol (cdr x) y))))



(defsection stv-number-of-phases
  :parents (symbolic-test-vectors)
  :short "@(call stv-number-of-phases) determines the maximum number of phases
that are used in any line of a symbolic test vector."

  (defund stv-max-phases-in-lines (lines)
    (declare (xargs :guard (true-list-listp lines)))
    (if (atom lines)
        0
      (max (length (cdr (car lines)))
           (stv-max-phases-in-lines (cdr lines)))))

  (defund stv-number-of-phases (stv)
    (declare (xargs :guard (stvdata-p stv)))
    (b* (((stvdata stv) stv))
      (max (stv-max-phases-in-lines stv.inputs)
           (max (stv-max-phases-in-lines stv.outputs)
                (stv-max-phases-in-lines stv.internals))))))


(defsection stv-suffix-signals
  :parents (symbolic-test-vectors)
  :short "@(call stv-suffix-signals) converts @('x'), a list of atoms, into a
list of symbols with the given @('suffix')."

  (defund stv-suffix-signals (x suffix)
    (declare (xargs :guard (and (atom-listp x)
                                (stringp suffix))))
    (if (atom x)
        nil
      (cons (intern$ (str::cat (stringify (car x)) suffix) "ACL2")
            (stv-suffix-signals (cdr x) suffix))))

  (local (in-theory (enable stv-suffix-signals)))

  (defthm symbol-listp-of-stv-suffix-signals
    (symbol-listp (stv-suffix-signals x suffix))))



(defsection safe-pairlis-onto-acc
  :parents (stv-compile)
  :short "@(call safe-pairlis-onto-acc) pairs up @('x') and @('y'), and
accumulates them onto @('acc').  It is \"safe\" in that it causes an error if
@('x') and @('y') aren't the same length."

  (defun safe-pairlis-onto-acc (x y acc)
    (declare (xargs :guard t))
    (mbe :logic
         (revappend (pairlis$ x y) acc)
         :exec
         (b* (((when (and (atom x)
                          (atom y)))
               acc)
              ((when (atom x))
               (er hard? 'safe-pairlis-onto-acc "Too many values!")
               acc)
              ((when (atom y))
               (er hard? 'safe-pairlis-onto-acc "Not enough values!")
               (safe-pairlis-onto-acc (cdr x) nil
                                      (cons (cons (car x) nil) acc))))
           (safe-pairlis-onto-acc (cdr x) (cdr y)
                                  (cons (cons (car x) (car y)) acc))))))



(defsection stv->ins
  :parents (symbolic-test-vectors)
  :short "Get a list of an STV's input simulation variables."

  :long "<p>@(call stv->ins) returns the user-level symbolic variables from the
input and initial lines of a symbolic test vector.  For instance, if you have
an input line like:</p>

@({
 (\"a_bus\"  _ _ _ a1 _ a2 _ _)
})

<p>Then the returned list will include @('a1') and @('a2').</p>"

  (defund stv->ins (x)
    (declare (xargs :guard (processed-stv-p x)))
    (b* (((processed-stv x) x)
         ((compiled-stv cstv) x.compiled-stv))
      (alist-keys cstv.in-usersyms))))


(defsection stv->outs
  :parents (symbolic-test-vectors)
  :short "Get a list of an STV's output simulation variables."

  :long "<p>@(call stv->outs) returns the user-level symbolic variables from
the output and internals lines of a symbolic test vector.  For instance, if you
have an output line like:</p>

@({
 (\"main_result\"  _ _ _ res1 _ res2 _ _)
})

<p>Then the returned list will include @('res1') and @('res2').</p>"

  (defund stv->outs (x)
    (declare (xargs :guard (processed-stv-p x)))
    (b* (((processed-stv x) x)
         ((compiled-stv cstv) x.compiled-stv))
      (alist-keys cstv.out-usersyms))))


(defsection stv->vars
  :parents (symbolic-test-vectors)
  :short "Get a list of an STV's simulation variables (both inputs and
outputs)."
  :long "<p>See @(see stv->ins) and @(see stv->outs).</p>"

  (defund stv->vars (x)
    (declare (xargs :guard (processed-stv-p x)))
    (append (stv->ins x)
            (stv->outs x))))


(defsection stv-out->width
  :parents (symbolic-test-vectors)
  :short "Get the bit-length for a particular output simulation variable."

  :long "<p>@(call stv-out->width) returns the bit-length of an output
simulation variable.  For instance, if you have an STV output line like:</p>

@({
 (\"main_result\"  _ _ _ res1 _ res2 _ _)
})

<p>Then @('(stv-out->width 'res1 stv)') will return the width of
@('main_result'), say 64.  If @('x') isn't one of the STV's outputs, we cause a
runtime error and logically return 0.</p>"

  (defun stv-out->width (x stv)
    (declare (xargs :guard (and (symbolp x)
                                (processed-stv-p stv))))
    (b* (((processed-stv stv) stv)
         ((compiled-stv cstv) stv.compiled-stv)
         (look (hons-assoc-equal x cstv.out-usersyms))
         ((unless look)
          (er hard? 'stv-out->width "Unknown output: ~x0~%" x)
          ;; returning 0 gets us at least a natp type prescription
          0))
      (len (cdr look)))))


(defsection stv-in->width
  :parents (symbolic-test-vectors)
  :short "Get the bit-length for a particular input simulation variable."

  :long "<p>@(call stv-in->width) returns the bit-length of an input simulation
variable.  For instance, if you have an STV input line like:</p>

@({
 (\"a_bus\"  _ _ _ a1 _ a2 _ _)
})

<p>Then @('(stv-in->width 'a1 stv)') will return the width of @('a_bus'), say
128.  If @('x') isn't one of the STV's inputs, we cause a runtime error and
logically return 0.</p>"

  (defun stv-in->width (x stv)
    (declare (xargs :guard (and (symbolp x)
                                (processed-stv-p stv))))
    (b* (((processed-stv stv) stv)
         ((compiled-stv cstv) stv.compiled-stv)
         (look (hons-assoc-equal x cstv.in-usersyms))
         ((unless look)
          (er hard? 'stv-in->width "Unknown input: ~x0~%" x)
          ;; returning 0 gets us at least a natp type prescription
          0))
      (len (cdr look)))))

