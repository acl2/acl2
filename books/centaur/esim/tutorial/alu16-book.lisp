; Centaur Hardware Verification Tutorial for ESIM/VL2014
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


; alu16-book.lisp
;
; This file is a cleaned up version of alu16.lsp which is a certifiable ACL2
; book.
;
; This file has no comments to explain what is happening.  If you are just
; starting the tutorial, please start with alu16.lsp instead; it contains lots
; of explanation and also covers other interactive/debugging features.
;
; I don't do the full multiplier proof here, but instead only prove it
; multiplies when the arguments are under 2^8.  This lets this file be
; certified in a reasonable amount of time, even on a modest machine.

(in-package "ACL2")

; Added by Matt K., May 2015.  Improvement observed when certification used
; the :delay strategy:
; 133.73 sec. vs. 140.53 sec.
(value-triple (set-gc-strategy :delay))

(include-book "intro")

(value-triple
 ;; [Jared]: Matt K. had once commented out the following line, but I think
 ;; it's nicer to leave this here to make it explicit to remind us of how it
 ;; works.  At the time of this writing, I believe that the above call of
 ;; set-gc-strategy installs a 4 GB ceiling.  However, in some cases it may be
 ;; important to set a larger ceiling:
 (set-max-mem (* 4 (expt 2 30))))


; NOTE ---- ESIM is still available but it is no longer being actively
; maintained.  The successor of ESIM is SVEX.  If you don't already have
; projects based on ESIM, you should probably skip this tutorial and learn
; about SVEX instead.



(defmodules *alu16-translation*
  (vl2014::make-vl-loadconfig
   :start-files (list "alu16.v")))

(defconst *alu16*
  (b* ((good  (vl2014::vl-translation->good *alu16-translation*))
       (mods  (vl2014::vl-design->mods good))
       (alu16 (vl2014::vl-find-module "alu16" mods))
       ((unless alu16)
        (er hard? '*alu16* "Failed to translate alu16?"))
       (esim  (vl2014::vl-module->esim alu16))
       ((unless (good-esim-modulep esim))
        (er hard? '*alu16* "Failed to produce a good esim module")))
    esim))

(defstv alu16-test-vector
  :mod *alu16*
  :inputs '(("opcode" op)
            ("abus"   a)
            ("bbus"   b))
  :outputs '(("out"    res))
  :parents (esim-tutorial) ;; xdoc stuff, not needed
  )

(defconst *op-plus*    0)
(defconst *op-minus*   1)
(defconst *op-bitand*  2)
(defconst *op-bitor*   3)
(defconst *op-bitxor*  4)
(defconst *op-min*     5)
(defconst *op-count*   6)
(defconst *op-mult*    7)

(defmacro alu16-default-bindings ()
  `(gl::auto-bindings (:nat op 3)
                      (:mix (:nat a 16)
                            (:nat b 16))))

(defmacro alu16-basic-result ()
  `(let* ((in-alist (alu16-test-vector-autoins))
          (out-alist (stv-run (alu16-test-vector) in-alist))
          (res       (cdr (assoc 'res out-alist))))
     res))

(defmacro alu16-thm (name &key opcode spec (g-bindings '(alu16-default-bindings)))
  `(def-gl-thm ,name
     :hyp (and (alu16-test-vector-autohyps)
               (equal op ,opcode))
     :concl (equal (alu16-basic-result) ,spec)
     :g-bindings ,g-bindings))

(alu16-thm alu16-plus-correct
           :opcode *op-plus*
           :spec (mod (+ a b) (expt 2 16)))

(alu16-thm alu16-minus-correct
           :opcode *op-minus*
           :spec (mod (- a b) (expt 2 16)))

(alu16-thm alu16-bitand-correct
           :opcode *op-bitand*
           :spec (logand a b))

(alu16-thm alu16-bitor-correct
           :opcode *op-bitor*
           :spec (logior a b))

(alu16-thm alu16-bitxor-correct
           :opcode *op-bitxor*
           :spec (logxor a b))

(alu16-thm alu16-min-correct
           :opcode *op-min*
           :spec (min a b))


(defun buggy-logcount (a)
  (+ (logbit 0 a)
     (logbit 1 a)
     (logbit 2 a)
     (logbit 3 a)
     (logbit 4 a)
     (logbit 5 a)
     (logbit 6 a)
     (logbit 3 a) ;; <-- 3 instead of 7
     (logbit 8 a)
     (logbit 9 a)
     (logbit 10 a)
     (logbit 11 a)
     (logbit 12 a)
     (logbit 13 a)
     (logbit 14 a)
     (logbit 15 a)))

(alu16-thm alu16-count-buggy
           :opcode *op-count*
           :spec (buggy-logcount a))

(def-gl-thm alu16-mult-partially-correct
  :hyp (and (alu16-test-vector-autohyps)
            (equal op *op-mult*)
            (< a (expt 2 8))
            (< b (expt 2 8)))
  :concl (equal (alu16-basic-result)
                (mod (* a b) (expt 2 16)))
  :g-bindings (alu16-default-bindings))
