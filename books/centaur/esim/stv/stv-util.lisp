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


; stv-util.lisp -- general utilities for the stv compiler
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "../esim-sexpr-support")
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/cat" :dir :system)

(std::defaggregate stvdata
  :parents (symbolic-test-vectors)
  :short "Temporary internal representation of STV lines during compilation."
  :tag :stvdata
  ((inputs    true-list-listp)
   (outputs   true-list-listp)
   (internals true-list-listp)
   (overrides true-list-listp)))

(std::defaggregate compiled-stv
  :parents (symbolic-test-vectors)
  :short "Compiled form of @(see symbolic-test-vectors)."
  :tag :compiled-stv
  ((nphases posp
            "number of phases for this simulation"
            :rule-classes :type-prescription)

   (nst-extract-alists "what to extract at times 0...{N-1} from next-states"
                       true-listp :rule-classes :type-prescription)

   (out-extract-alists "what to extract at times 0...{N-1} from outputs"
                       true-listp :rule-classes :type-prescription)

   (int-extract-alists "what to extract at times 0...{N-1} from internals"
                       true-listp :rule-classes :type-prescription)

   (override-bits      "flat list of state bits involved in overrides, i.e.,
                        just the override_value and override_decision vars"
                       symbol-listp)

   (restrict-alist     "combined alist binding
                          (input-bit@phase &rarr; sexpr) and
                          (override-bit@phase &rarr; sexpr)")

   (in-usersyms        "(simulation var &rarr; bit list) alist for Inputs +
                        Overrides (replacement value insertion)")
   (out-usersyms       "(simulation var &rarr; bit list) alist for Outputs +
                        Internals + Overrides (original value extraction)")

   (expanded-ins       "Input lines with s-expression values, used only so
                        that we can resolve ~s in stv-doc.")

   (override-paths     "Paths being overridden, so we can recreate the cut
                        module as needed."
                       true-listp)

   ))

(std::defaggregate processed-stv
  :parents (stv-process)
  :short "Representation of a processed STV."
  :tag :processed-stv
  ((name               "A name for this STV."
                       symbolp)
   (user-stv           "The user-level, pre-compiled STV.  This may be useful when
                        generating documentation for STVs.")
   (compiled-stv       compiled-stv-p
                       "A @(see compiled-stv-p), should be the compiled version
                        of the user's STV; see @(see stv-compile).")
   (relevant-signals   "(out/int sim var bit &rarr; sexpr) alist"))

  :long "<p>You should probably read @(see stv-implementation-details) to
understand these fields.</p>

<p>The @('relevant-signals') is an alist computed by @(see stv-process) that
maps each the bits for each internal/output simulation variable to
already-restricted @(see 4v-sexprs).  That is, these s-expressions are
generally in terms of the input simulation variable bits, and ready to be
evaluated by @(see stv-run).</p>

<p>Historically we had another field that could also optionally store
pre-computed snapshots for debugging.  We took this out because it could make
@(see stv-run) a lot slower during GL proofs.  The snapshots were huge, and
this really slowed down GL's gl-concrete-lite check.</p>")


(defund ordered-subsetp (x y)
  ;; BOZO find me a home
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (if (equal (car x) (car y))
               (ordered-subsetp (cdr x) (cdr y))
             (ordered-subsetp x (cdr y))))
    t))


(define stv-max-phases-in-lines ((lines true-list-listp))
  :returns (max-phases natp :rule-classes :type-prescription)
  :parents (stv-number-of-phases)
  (if (atom lines)
      0
    (max (length (cdr (car lines)))
         (stv-max-phases-in-lines (cdr lines)))))

(define stv-number-of-phases ((stv stvdata-p))
  :returns (num-phases natp :rule-classes :type-prescription)
  :parents (symbolic-test-vectors)
  :short "Maximum length of any line of an STV (i.e., how many phases we are
going to simulate."

  (b* (((stvdata stv) stv))
    (max (stv-max-phases-in-lines stv.inputs)
         (max (stv-max-phases-in-lines stv.outputs)
              (max (stv-max-phases-in-lines stv.internals)
                   (stv-max-phases-in-lines stv.overrides))))))


(define stv-suffix-signals ((x atom-listp)
                            (suffix stringp))
  :returns (symbols symbol-listp)
  :parents (symbolic-test-vectors)
  :short "Convert a list of atoms into a list of symbols with some suffix."
  ;; BOZO do we really need to support atom-listps?
  (if (atom x)
      nil
    (cons (intern$ (str::cat (stringify (car x)) suffix) "ACL2")
          (stv-suffix-signals (cdr x) suffix))))


(define safe-pairlis-onto-acc (x y acc)
  :parents (stv-compile)
  :short "Just @(see pairlis$) onto an accumulator, but for safety cause an
error if the lists to pair up aren't the same length."
  :enabled t
  (mbe :logic
       (revappend (pairlis$ x y) acc)
       :exec
       (b* (((when (and (atom x)
                        (atom y)))
             acc)
            ((when (atom x))
             (raise "Too many values!")
             acc)
            ((when (atom y))
             (raise "Not enough values!")
             (safe-pairlis-onto-acc (cdr x) nil
                                    (cons (cons (car x) nil) acc))))
         (safe-pairlis-onto-acc (cdr x) (cdr y)
                                (cons (cons (car x) (car y)) acc)))))


(define stv->ins ((x processed-stv-p))
  :returns (inputs "Should be a symbol-listp in practice.") ;; BOZO strengthen
  :parents (symbolic-test-vectors)
  :short "Get a list of an STV's input simulation variables."

  :long "<p>We collect simulation variables from all input and initial lines.
For instance, if you have an input line like:</p>

@({
 (\"a_bus\"  _ _ _ a1 _ a2 _ _)
})

<p>Then the returned list will include @('a1') and @('a2').</p>"

  (b* (((processed-stv x) x)
       ((compiled-stv cstv) x.compiled-stv))
    (alist-keys cstv.in-usersyms)))


(define stv->outs ((x processed-stv-p))
  :returns (outputs "Should be a symbol-listp in practice.") ;; BOZO strengthen
  :parents (symbolic-test-vectors)
  :short "Get a list of an STV's output simulation variables."

  :long "<p>We collect simulation variables from all output and internals
lines.  For instance, if you have an output line like:</p>

@({
 (\"main_result\"  _ _ _ res1 _ res2 _ _)
})

<p>Then the returned list will include @('res1') and @('res2').</p>"

  (b* (((processed-stv x) x)
       ((compiled-stv cstv) x.compiled-stv))
    (alist-keys cstv.out-usersyms)))


(define stv->vars ((x processed-stv-p))
  :returns (vars "Should be a symbol-listp in practice.") ;; BOZO strengthen
  :parents (symbolic-test-vectors)
  :short "Get a list of an STV's simulation variables (both inputs and
outputs)."

  (append (stv->ins x)
          (stv->outs x)))


(define stv-out->width ((x   symbolp)
                        (stv processed-stv-p))
  ;; BOZO fix this up to guarantee posp?
  :returns (width natp :rule-classes :type-prescription)
  :parents (symbolic-test-vectors)
  :short "Get the bit-length for a particular output simulation variable."

  :long "<p>For instance, if you have an STV output line like:</p>

@({
 (\"main_result\"  _ _ _ res1 _ res2 _ _)
})

<p>Then @('(stv-out->width 'res1 stv)') will return the width of
@('main_result'), say 64.</p>

<p>If @('x') isn't one of the STV's outputs, we cause a runtime error and
logically return 0.</p>"

  (b* (((processed-stv stv) stv)
       ((compiled-stv cstv) stv.compiled-stv)
       (look (hons-assoc-equal x cstv.out-usersyms))
       ((unless look)
        (raise "Unknown output: ~x0~%" x)
        ;; returning 0 gets us at least a natp type prescription
        0))
    (len (cdr look))))


(define stv-in->width ((x   symbolp)
                       (stv processed-stv-p))
  ;; BOZO fix this up to guarantee posp?
  :returns (width natp :rule-classes :type-prescription)
  :parents (symbolic-test-vectors)
  :short "Get the bit-length for a particular input simulation variable."

  :long "<p>For instance, if you have an STV input line like:</p>

@({
 (\"a_bus\"  _ _ _ a1 _ a2 _ _)
})

<p>Then @('(stv-in->width 'a1 stv)') will return the width of @('a_bus'), say
128.</p>

<p>If @('x') isn't one of the STV's inputs, we cause a runtime error and
logically return 0.</p>"

  (b* (((processed-stv stv) stv)
       ((compiled-stv cstv) stv.compiled-stv)
       (look (hons-assoc-equal x cstv.in-usersyms))
       ((unless look)
        (raise "Unknown input: ~x0~%" x)
        ;; returning 0 gets us at least a natp type prescription
        0))
    (len (cdr look))))

