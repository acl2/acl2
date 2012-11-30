; Centaur Hardware Verification Tutorial
; Copyright (C) 2012 Centaur Technology
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
;
; NOTE: The tutorial starts with intro.lisp.



; counter.lisp
;
; This is a trivial base-10 counter module that will let us talk about state
; and multi-phase simulations.  We assume you have already worked through
; alu16.lsp so we won't explain preliminary things.

(in-package "ACL2")
(include-book "intro")
(value-triple (set-max-mem (* 3 (expt 2 30))))


;; For interactive use, you'll probably want to run (plev)
#||
(plev)
||#


; Get counter.v loaded, inspect what we've loaded...

(defmodules *counter-translation*
  :start-files (list "counter.v"))

; (vl::vl-ppcs-modulelist (vl::vl-translation->mods *counter-translation*))

(defconst *counter-vl*
  (vl::vl-find-module "counter" (vl::vl-translation->mods *counter-translation*)))

; (vl::vl-ppcs-module *counter-vl*)



; Extract the ESIM module for counter.

(defconst *counter*
  (vl::vl-module->esim *counter-vl*))



(defstv counter-run         ;; name for this test vector
  :mod *counter*            ;; the module this vector pertains to

  :initial
  '(("out"    init))  ; initial value for the counter

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

  ;; I'll use this as a chance to also show off the documentation features.
  :labels '(c0  c1 c1  c2 c2  c3 c3  c4 c4)
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

