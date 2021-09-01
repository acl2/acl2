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
;
; NOTE: The tutorial starts with intro.lisp.



; counter.lisp
;
; This is a trivial base-10 counter module that will let us talk about state
; and multi-phase simulations.  We assume you have already worked through
; alu16.lsp so we won't explain preliminary things.

(in-package "ACL2")

; Added by Matt K., May 2015.  Improvement observed when certification used
; the :delay strategy:
; 133.09 sec. vs. 139.82 sec.
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




;; For interactive use, you'll probably want to run (plev)
#||
(plev)
||#


; Get counter.v loaded, inspect what we've loaded...

(defmodules *counter-translation*
  (vl2014::make-vl-loadconfig
   :start-files (list "counter.v")))

; (vl2014::vl-ppcs-modulelist (vl2014::vl-translation->mods *counter-translation*))

(defconst *counter-vl*
  (vl2014::vl-find-module "counter"
                      (vl2014::vl-design->mods
                       (vl2014::vl-translation->good *counter-translation*))))

; (vl2014::vl-ppcs-module *counter-vl*)



; Extract the ESIM module for counter.

(defconst *counter*
  (vl2014::vl-module->esim *counter-vl*))


(defstv counter-run         ;; name for this test vector
  :mod *counter*            ;; the module this vector pertains to

  :inputs
  '(("clk"    0 ~)  ; clk will toggle

   ;             cyc 1    cyc 2   cyc 3   cyc 4
   ;             ___     ___     ___     ___     ___ ...
   ;     clk ___|  .|___|  .|___|  .|___|  .|___|
   ;           ^   .   ^   .   ^   .   ^   .   ^
   ;           |   .   |   .   |   .   |   .   |
    ("reset"  r0   _  r1   _  r2   _  r3   _  r4   _)  ; vars to let us control these
    ("inc"    i0   _  i1   _  i2   _  i3   _  i4   _)  ; inputs at before each posedge
    )

  :outputs
   ;             cyc 1    cyc 2   cyc 3   cyc 4
   ;             ___     ___     ___     ___     ___ ...
   ;     clk ___|  .|___|  .|___|  .|___|  .|___|
   ;           |   .   |   .   |   .   |   .   |
   ;           v   .   v   .   v   .   v   .   v
  '(("out"    o0   _  o1   _  o2   _  o3   _  o4 _))   ; extract out before each posedge

  :overrides
  '(("out"    init _))  ; initial value for the counter


  ;; I'll use this as a chance to also show off the documentation features.
  :labels '(c0  c1 c1  c2 c2  c3 c3  c4 c4  c5)
  :parents (esim-tutorial)
  :short "Running the counter module"
  :long "<p>This is a demo of the defstv documentation stuff.  You can see what
it generates by going to the counter-run page in the XDOC manual; see
centaur/README.html if you don't know where to look.</p>")


; Some basic examples of running the counter.

#||

(stv-run (counter-run)
         '((init . 0)   ; Never reset, always increment, start counter off at 0.
           (r0 . 0)
           (r1 . 0)     ; We see that it properly counts up, i.e., the outputs
           (r2 . 0)     ; are 0, 1, 2, 3, and 4.
           (r3 . 0)
           (r4 . 0)
           (i0 . 1)
           (i1 . 1)
           (i2 . 1)
           (i3 . 1)
           (i4 . 1)))

(stv-run (counter-run)
         '((init . 8)   ; Same as above (never reset, always increment) except we
           (r0 . 0)     ; start at 8 instead of 0.
           (r1 . 0)
           (r2 . 0)     ; We see the counter go up to 9 and then wrap back down
           (r3 . 0)     ; to zero.
           (r4 . 0)
           (i0 . 1)
           (i1 . 1)
           (i2 . 1)
           (i3 . 1)
           (i4 . 1)))

(stv-run (counter-run)   ; This time we won't bother to initialize the counter, so
         '((r0 . 1)    ; its starting value is X.  But, we assert reset for cycle
           (r1 . 0)    ; zero, and then leave it deasserted for the remainder of
           (r2 . 0)    ; the simulation.
           (r3 . 0)
           (r4 . 0)    ; Since we didn't initialize the counter, we see that in
           (i1 . 1)    ; cycle 0 it is X.  But then, we see that reset clears it
           (i2 . 1)    ; to zero, and we start counting up as normal.
           (i3 . 1)
           (i4 . 1)))

(stv-run (counter-run)
         '((r0 . 0)    ; Here we never assert reset and always increment.
           (r1 . 0)    ; But we don't initialize the counter so we just get X.
           (r2 . 0)
           (r3 . 0)
           (r4 . 0)
           (i0 . 1)
           (i1 . 1)
           (i2 . 1)
           (i3 . 1)
           (i4 . 1)))

||#


; Lets do some proofs.  I think of this as, "output 4 is correct, assuming
; there are no resets."

(def-gl-thm counter-output4-correct-unless-reset
  :hyp (and (counter-run-autohyps)
            (< init 10) ;; note that this hyp is necessary!
            (= r0 0)
            (= r1 0)
            (= r2 0)
            (= r3 0)
            (= r4 0))
  :concl (b* ((outs        (stv-run (counter-run) (counter-run-autoins)))
              ;; Fancy B* binder that extracts o4 from outs.
              ((assocs o4) outs))
           (equal o4
                  (mod (+ init i0 i1 i2 i3)
                       10)))
  :g-bindings (counter-run-autobinds))


; BOZO this is as much of a tutorial as there is, so far.

