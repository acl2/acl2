
;  sra-vw-flat-sim.lisp                      Vivek & Warren

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; (ld "sra-vw-flat-sim.lisp" :ld-pre-eval-print t)
; (certify-book "sra-vw-flat-sim" ?)

; Here are some notes concerning our simulation system.

; Preparation Steps:

;  1.   Parse and translate hierarchical SPICE format into hierarchical VWSIM format
;  2a.  Process simulation control statements
;  2b.  Topologically sort and flatten design
;  3.   Create symbolic circuit representation in sparse-matrix format
;  4.   Fold constants (except for trig functions) in symbolic sparse-matrices
;  4a.    Replace reference node, GND, and its derivative with constant 0
;  4b.    If fixed-interval (not variable-time) simulation, replace
;         $HN$ with constant time step
;  5.   Find and sort, in order of reference, all unique
;       subexpressions for one-pass evaluation
;  6.  Create list containing all-names ($time$,
;      $hn$, x-names, dp-x-names) and subexpressions list
;  7.   Convert all entries in subexpressions list into vw-eval-subterms
;  8.   Initialize A-sym-subterm with position of each symbolic matrix entry in Step 6
;  9.   Declare and initialize array to store intermediate expression (evaluation) results
; 10.   Set up the DZ solver for simulation.

; Simulation Steps:

;; Note: assume all constants are already folded away.

;  1.  Extend records with $r-time$, $r-hn$, $time$, $hn$.
;  2.  Seed evaluation array (STV) with $time$,
;      $hn$, and all-names values from R.
;  3.  Perform one-pass evaluation of all symbolic circuit expressions
;      and store the results in STV.
;  4.  Fill A-num with new values (stored in STV). If any value
;      differs from previous A-num value, mark LU-redo-p.
;  5.  Call matrix-decompose if LU-redo-p flag set.
;  6.  Call matrix-solve code.
;  7.  Update R with x-names values.
;  8.  Calculate dp-x-names values.
;  9.  Update R with dp-x-names values.
; 10.  Repeat until time exhausted

; Data structures

; We have 5 STOBJs that hold the entire simulation state.

; 1. rtime
;      - A STOBJ with fields storing the list of rational times and their
;      - deltas, both in reverse order.
; 2. rec
;      - A single-field STOBJ; the field is an array-based simulation
;      - record that stores the value of each variable at each time
;      - step.
; 3. st-vals
;      - A single-field STOBJ; the field is an array that stores the
;      - results of evaluating every symbolic subterm
; 4. Abr
;      - A multiple-field STOBJ; each field stores a part of the
;      - simulation state
; 5. dz
;      - A multiple-field STOBJ for matrix equation solving.

; Here we define the step to ready a model for VWSIM.
;   Spice-syntax ASCII source file
;   Parsed circuit-model source translated into S-expressions
;   Flattened circuit-model source, substitutions create S-expression
;   Identify each primitive (e.g., resistor, JJ) and name connections
;   For each name, create corresponding derivative name
;   Allocate array (with size # of names) for storing component tags

;; This version of VWSIM uses a STOBJ and sparse representation to
;; store the matrices.  Here, we use the "dz" solver as the underlying
;; linear system solver in the hopes of creating a faster VWSIM
;; simulator.

(in-package "ACL2")

(include-book "constants")
(include-book "names-and-indices")
(include-book "sra-matrix-defuns")
(include-book "vw-flat-hdl")
(include-book "vw-eval-ar")
(include-book "rtime")

; Helps immensely with admitting vw-eval-fold-b-sym:
(local (in-theory (disable member-equal)))

#||
(defun save-fields (args)
  ;; read until first keyword argument
  ;; ((b-sym (1 2 3 4 5)))
  (strip-cars (cdr args)))

(defmacro defstobj-save (&rest args)
  `(progn (defstobj ,@args)
          ,(save-fields args)))
||#

(defstobj Abr
  ;; The Abr STOBJ stores the simulator state. The first few fields
  ;; are the symbolic A and b matrices that are evaluated and used to
  ;; solve for the unknown voltages, currents, and/or phases of the
  ;; circuit.

  ;; To perform a simulation, all unique symbolic entries (terms) in
  ;; the A and b matrices are gathered. From these symbolic terms, a
  ;; list of all of their unique subterms is generated. During a
  ;; simulation, these terms are evaluated in one pass. The results
  ;; are stored in the STV array. We provide a mapping in b-sym-to-stv
  ;; and A-sym-to-stv, which provide the index of each term's
  ;; evaluated value in the STV array.

  (dim-Abr
   ;; The dimension of all of the square matrices and the b vector.
   :type (integer 0 *)
   :initially 0)

  (b-sym
   ;; The symbolic b vector.
   :type (array (satisfies vw-eval-termp)
                (0))
   :resizable t)

  (b-sym-fold
   ;; The symbolic b vector, where each entry is constant-folded.
   :type (array (satisfies vw-eval-termp)
                (0))
   :resizable t)

  (b-sym-fold-to-stv
   ;; The mapping of each term in b-sym-fold to the index/location of
   ;; its evaluated value in the STV array.
   :type (array (satisfies natp)
                (0))
   :initially 0
   :resizable t)

  (A-sym
   ;; The symbolic A matrix in sparse format.
   :type (array (satisfies sra-term-rowp)
                (0))
   :resizable t)

  (A-sym-fold
   ;; The symbolic A matrix in sparse format, where each entry is
   ;; constant-folded
   :type (array (satisfies sra-term-rowp)
                (0))
   :resizable t)

  (A-sym-fold-to-stv
   ;; The mapping of each term (the CDR of each sparse entry) in
   ;; A-sym-fold to the index/location of the term's evaluated value
   ;; in the STV array.
   :type (array (satisfies sra-nat-rowp)
                (0))
   :resizable t)

  (A-num
   ;; The rational/double-float A matrix in sparse format, where each
   ;; entry is the result of evaluating its corresponding term in
   ;; A-sym.
   :type (array (satisfies sra-rational-rowp)
                (0))
   :resizable t)

  (flat-occs
   ;; The list of all device occurrences in the flattened netlist.
   :type t
   :initially nil)

  (ref-node
   ;; The reference node.
   :type (satisfies symlp)
   :initially gnd)

  (time-start
   ;; The time to start the simulation.
   :type rational
   :initially 0)

  (hn
   ;; The current time step increment for the simulation.
   :type rational
   :initially 0)

  (time-stop
   ;; The time to end the simulation.
   :type rational
   :initially 0)

  (sim-type
   ;; The simulation type: voltage or phase.
   :type symbol
   :initially voltage)

  (equations
   ;; Prevent simulation and return the symbolic matrix equations.
   :type symbol
   :initially nil)

  (alter-values-alist
   ;; The association list of extra simulation variables that can be
   ;; used to vary device parameter values.
   :type (satisfies record-entries-consp)
   :initially nil)

  (hrchl-netlist
   ;; The heirarchical netlist (possibly parsed from a .cir file) in
   ;; native VWSIM format.
   :type t
   :initially nil)

  (x-names
   ;; The list of simulation variable names corresponding to each
   ;; entry in the x vector.
   :type (satisfies syml-listp)
   :initially nil)

  (dp-x-names
   ;; The variable names for the derivatives (d/dt) of each entry in
   ;; x-names.
   :type (satisfies symbol-listp)
   :initially nil)

  (load-sim
   ;; Indicate whether the simulation is being resumed from a previous
   ;; simulation.
   :type symbol
   :initially nil)

  (prints
   ;; The SPICE .print requests in the .cir file.
   :type t
   :initially nil)

  (cir-concat-char
   ;; The separator character used in the .cir file for flattened
   ;; occurrence references.  e.g., ".print RR1|XLAT|TOP"
   :type character
   :initially #\|)

  (vw-concat-char
   ;; The separator used in the VWSIM file for flattened occurrence
   ;; references.
   :type character
   :initially #\/)

  (current-time
   ;; The current simulation time.
   :type rational
   :initially 0)

  (all-rec-names
   ;; The list of variable names, in order, in the record.
   :type (satisfies symbol-listp)
   :initially nil)

  (subterms-to-stv-alist
   ;; The mapping of each symbolic subterm to the index of its
   ;; evaluated value in the STV array.
   :type (satisfies alistp)
   :initially nil)

  (all-stv-subterms
   ;; The list of compressed (for speed) subterms that are evaluated
   ;; every simulation step.
   :type t
   :initially nil)

  (x-names-offset
   ;; The starting index of node & branch names in REC STOBJ
   :type (integer 0 *)
   :initially 0)

  (dp-x-names-offset
   ;; The starting index of the node & branch DERIVATIVE names in REC
   ;; STOBJ
   :type (integer 0 *)
   :initially 0)

  (ref-node-offset
   ;; The index of reference node (zero volts/phase) in REC STOBJ
   :type (integer 0 *)
   :initially 0)

  (dp-ref-node-offset
   ;; The index of reference node's DERIVATIVE in REC STOBJ
   :type (integer 0 *)
   :initially 0)

  :renaming
  ((update-dim-Abr               !dim-Abr)
   (update-b-symi                !b-symi)
   (update-b-sym-foldi           !b-sym-foldi)
   (update-b-sym-fold-to-stvi    !b-sym-fold-to-stvi)
   (update-A-symi                !A-symi)
   (update-A-sym-foldi           !A-sym-foldi)
   (update-A-sym-fold-to-stvi    !A-sym-fold-to-stvi)
   (update-A-numi                !A-numi)

   (update-flat-occs             !flat-occs)
   (update-ref-node              !ref-node)
   (update-time-start            !time-start)
   (update-hn                    !hn)
   (update-time-stop             !time-stop)
   (update-sim-type              !sim-type)
   (update-equations             !equations)
   (update-alter-values-alist    !alter-values-alist)
   (update-hrchl-netlist         !hrchl-netlist)
   (update-x-names               !x-names)
   (update-dp-x-names            !dp-x-names)
   (update-load-sim              !load-sim)
   (update-prints                !prints)
   (update-cir-concat-char       !cir-concat-char)
   (update-vw-concat-char        !vw-concat-char)
   (update-current-time          !current-time)
   (update-all-rec-names         !all-rec-names)
   (update-subterms-to-stv-alist !subterms-to-stv-alist)
   (update-all-stv-subterms      !all-stv-subterms)
   (update-x-names-offset        !x-names-offset)
   (update-dp-x-names-offset     !dp-x-names-offset)
   (update-ref-node-offset       !ref-node-offset)
   (update-dp-ref-node-offset    !dp-ref-node-offset))

  :inline t
  :non-memoizable t
  )

; Some facts about ``Abr'' STOBJ accessor, updater, resizer, length,
; and recognizer functions.

; b-sym
;-----------------
(defthm length-b-symi
  (implies (and (natp i)
                (< i (b-sym-length Abr)))
           (equal (b-sym-length (!b-symi i row Abr))
                  (b-sym-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-b-symi
  (and (equal (b-sym-fold-length (!b-symi i expr Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (!b-symi i expr Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (!b-symi i expr Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (!b-symi i expr Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (!b-symi i expr Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (!b-symi i expr Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm b-symp-!b-symi
  (implies (and (b-symp l)
                (vw-eval-termp entry))
           (b-symp (!nth i entry l)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm Abrp-!b-symi
  (implies (and (Abrp Abr)
                (vw-eval-termp entry))
           (Abrp (!b-symi i entry Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

; b-sym-fold
;-----------------
(defthm length-b-sym-foldi
  (implies (and (natp i)
                (< i (b-sym-fold-length Abr)))
           (equal (b-sym-fold-length (!b-sym-foldi i row Abr))
                  (b-sym-fold-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-b-sym-foldi
  (and (equal (b-sym-length (!b-sym-foldi i expr Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-to-stv-length (!b-sym-foldi i expr Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (!b-sym-foldi i expr Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (!b-sym-foldi i expr Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (!b-sym-foldi i expr Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (!b-sym-foldi i expr Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm b-sym-foldp-!b-sym-foldi
  (implies (and (b-sym-foldp l)
                (vw-eval-termp entry))
           (b-sym-foldp (!nth i entry l)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm Abrp-!b-sym-foldi
  (implies (and (Abrp Abr)
                (vw-eval-termp entry))
           (Abrp (!b-sym-foldi i entry Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

; b-sym-fold-to-stv
;-----------------
(defthm length-b-sym-fold-to-stvi
  (implies (and (natp i)
                (< i (b-sym-fold-to-stv-length Abr)))
           (equal (b-sym-fold-to-stv-length (!b-sym-fold-to-stvi i row Abr))
                  (b-sym-fold-to-stv-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-b-sym-fold-to-stvi
  (and (equal (b-sym-length (!b-sym-fold-to-stvi i expr Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (!b-sym-fold-to-stvi i expr Abr))
              (b-sym-fold-length Abr))
       (equal (A-sym-length (!b-sym-fold-to-stvi i expr Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (!b-sym-fold-to-stvi i expr Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (!b-sym-fold-to-stvi i expr Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (!b-sym-fold-to-stvi i expr Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm b-sym-foldp-!b-sym-fold-to-stvi
  (implies (and (b-sym-fold-to-stvp l)
                (<= i (len l))
                (natp entry))
           (b-sym-fold-to-stvp (!nth i entry l)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm Abrp-!b-sym-fold-to-stvi
  (implies (and (Abrp Abr)
                (<= i (b-sym-fold-to-stv-length Abr))
                (natp entry))
           (Abrp (!b-sym-fold-to-stvi i entry Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

; A-sym
;-----------------
(defthm length-A-symi
  (implies (and (natp i)
                (force (< i (A-sym-length Abr))))
           (equal (A-sym-length (!A-symi i row Abr))
                  (A-sym-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-A-symi
  (and (equal (b-sym-length (!A-symi i expr Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (!A-symi i expr Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (!A-symi i expr Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-fold-length (!A-symi i expr Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (!A-symi i expr Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (!A-symi i expr Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm A-symp-!A-symi
  (implies (and (A-symp l)
                (sra-term-rowp entry))
           (A-symp (!nth i entry l)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm Abrp-!A-symi
  (implies (and (Abrp Abr)
                (sra-term-rowp entry))
           (Abrp (!A-symi i entry Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

; A-sym-fold
;-----------------
(defthm length-A-sym-foldi
  (implies (and (natp i)
                (< i (A-sym-fold-length Abr)))
           (equal (A-sym-fold-length (!A-sym-foldi i row Abr))
                  (A-sym-fold-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-A-sym-foldi
  (and (equal (b-sym-length (!A-sym-foldi i expr Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (!A-sym-foldi i expr Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (!A-sym-foldi i expr Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (!A-sym-foldi i expr Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-to-stv-length (!A-sym-foldi i expr Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (!A-sym-foldi i expr Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm A-sym-foldp-!A-sym-foldi
  (implies (and (A-sym-foldp l)
                (sra-term-rowp entry))
           (A-sym-foldp (!nth i entry l)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm Abrp-!A-sym-foldi
  (implies (and (Abrp Abr)
                (sra-term-rowp entry))
           (Abrp (!A-sym-foldi i entry Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

; A-sym-fold-to-stv
;-----------------
(defthm length-A-sym-fold-to-stvi
  (implies (and (natp i)
                (< i (A-sym-fold-to-stv-length Abr)))
           (equal (A-sym-fold-to-stv-length (!A-sym-fold-to-stvi i row Abr))
                  (A-sym-fold-to-stv-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-A-sym-fold-to-stvi
  (and (equal (b-sym-length (!A-sym-fold-to-stvi i expr Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (!A-sym-fold-to-stvi i expr Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (!A-sym-fold-to-stvi i expr Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (!A-sym-fold-to-stvi i expr Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (!A-sym-fold-to-stvi i expr Abr))
              (A-sym-fold-length Abr))
       (equal (A-num-length (!A-sym-fold-to-stvi i expr Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm A-sym-fold-to-stvp-!A-sym-fold-to-stvi
  (implies (and (A-sym-fold-to-stvp l)
                (sra-nat-rowp entry))
           (A-sym-fold-to-stvp (!nth i entry l)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm Abrp-!A-sym-fold-to-stvi
  (implies (and (Abrp Abr)
                (sra-nat-rowp entry))
           (Abrp (!A-sym-fold-to-stvi i entry Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

; A-num
;-----------------
(defthm length-A-numi
  (implies (and (natp i)
                (< i (A-num-length Abr)))
           (equal (A-num-length (!A-numi i row Abr))
                  (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-A-numi
  (and (equal (b-sym-length (!A-numi i expr Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (!A-numi i expr Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (!A-numi i expr Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (!A-numi i expr Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (!A-numi i expr Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (!A-numi i expr Abr))
              (A-sym-fold-to-stv-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm A-nump-!A-numi
  (implies (and (A-nump l)
                (sra-rational-rowp entry))
           (A-nump (!nth i entry l)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm Abrp-!A-numi
  (implies (and (Abrp Abr)
                (sra-rational-rowp entry))
           (Abrp (!A-numi i entry Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

; dim-Abr
;-----------------

(defthm non-interference-!dim-Abr
  ;; this lemma SHOULD prove non-interference properties for all STOBJ
  ;; fields. We should explore how to do this.
  (and (equal (A-num-length (!dim-Abr v Abr))
              (A-num-length Abr))
       (equal (A-sym-length (!dim-Abr v Abr))
              (A-sym-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm Abrp-!dim-Abr
  (implies (and (Abrp Abr)
                (natp v))
           (Abrp (!dim-Abr v Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

; alter-values-alist
;-----------------

(defthm record-entries-consp-alter-values-alist
  (implies (Abrp Abr)
           (and (symbol-num-list-alistp (alter-values-alist abr))
                (alist-entry-consp (alter-values-alist Abr))
                ;; (record-entries-consp (alter-values-alist Abr))
                ))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

; Some facts about ``Abr'' STOBJ resize functions

(defthm resize-b-sym-length
  (implies (natp size)
           (equal (b-sym-length (resize-b-sym size Abr))
                  size))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-resize-b-sym
  (and (equal (b-sym-fold-length (resize-b-sym size Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (resize-b-sym size Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (resize-b-sym size Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (resize-b-sym size Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (resize-b-sym size Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (resize-b-sym size Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm resize-b-sym-fold-length
  (implies (natp size)
           (equal (b-sym-fold-length (resize-b-sym-fold size Abr))
                  size))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-resize-b-sym-fold
  (and (equal (b-sym-length (resize-b-sym-fold size Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-to-stv-length (resize-b-sym-fold size Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (resize-b-sym-fold size Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (resize-b-sym-fold size Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (resize-b-sym-fold size Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (resize-b-sym-fold size Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm resize-b-sym-fold-to-stv-length
  (implies (natp size)
           (equal (b-sym-fold-to-stv-length (resize-b-sym-fold-to-stv size Abr))
                  size))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-resize-b-sym-fold-to-stv
  (and (equal (b-sym-length (resize-b-sym-fold-to-stv size Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (resize-b-sym-fold-to-stv size Abr))
              (b-sym-fold-length Abr))
       (equal (A-sym-length (resize-b-sym-fold-to-stv size Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (resize-b-sym-fold-to-stv size Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (resize-b-sym-fold-to-stv size Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (resize-b-sym-fold-to-stv size Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm resize-A-sym-length
  (implies (natp size)
           (equal (A-sym-length (resize-A-sym size Abr))
                  size))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-resize-A-sym
  (and (equal (b-sym-length (resize-A-sym size Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (resize-A-sym size Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (resize-A-sym size Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-fold-length (resize-A-sym size Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (resize-A-sym size Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (resize-A-sym size Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm resize-A-sym-fold-length
  (implies (natp size)
           (equal (A-sym-fold-length (resize-A-sym-fold size Abr))
                  size))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-resize-A-sym-fold
  (and (equal (b-sym-length (resize-A-sym-fold size Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (resize-A-sym-fold size Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (resize-A-sym-fold size Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (resize-A-sym-fold size Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-to-stv-length (resize-A-sym-fold size Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (resize-A-sym-fold size Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm resize-A-sym-fold-to-stv-length
  (implies (natp size)
           (equal (A-sym-fold-to-stv-length (resize-A-sym-fold-to-stv size Abr))
                  size))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-resize-A-sym-fold-to-stv
  (and (equal (b-sym-length (resize-A-sym-fold-to-stv size Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (resize-A-sym-fold-to-stv size Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (resize-A-sym-fold-to-stv size Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (resize-A-sym-fold-to-stv size Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (resize-A-sym-fold-to-stv size Abr))
              (A-sym-fold-length Abr))
       (equal (A-num-length (resize-A-sym-fold-to-stv size Abr))
              (A-num-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm resize-A-num-length
  (implies (natp size)
           (equal (A-num-length (resize-A-num size Abr))
                  size))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm other-lengths-resize-A-num
  (and (equal (b-sym-length (resize-A-num size Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (resize-A-num size Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (resize-A-num size Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (resize-A-num size Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (resize-A-num size Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (resize-A-num size Abr))
              (A-sym-fold-to-stv-length Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

; Some facts about ``Abr'' STOBJ accessor functions

(defthm vw-eval-termp-nth-b-symp
  (implies (b-symp b)
           (vw-eval-termp (nth i b)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm vw-eval-termp-b-symi
  (implies (Abrp Abr)
           (vw-eval-termp (b-symi i Abr))))

(defthm vw-eval-termp-nth-b-sym-foldp
  (implies (b-sym-foldp b)
           (vw-eval-termp (nth i b)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm vw-eval-termp-b-sym-foldi
  (implies (Abrp Abr)
           (vw-eval-termp (b-sym-foldi i Abr))))

(defthm natp-nth-b-sym-fold-to-stvp
  (implies (and (b-sym-fold-to-stvp b)
                (natp i)
                (< i (len b)))
           (natp (nth i b)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm natp-b-sym-fold-to-stvi
  (implies (and (Abrp Abr)
                (natp i)
                (< i (b-sym-fold-to-stv-length Abr)))
           (natp (b-sym-fold-to-stvi i Abr))))

(defthm sra-term-rowp-nth-A-symp
  (implies (A-symp A)
           (sra-term-rowp (nth i A)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm sra-term-rowp-A-symi
  (implies (Abrp A)
           (sra-term-rowp (A-symi i A))))

(defthm sra-term-rowp-nth-A-sym-foldp
  (implies (A-sym-foldp A)
           (sra-term-rowp (nth i A)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm sra-term-rowp-A-sym-foldi
  (implies (Abrp Abr)
           (sra-term-rowp (A-sym-foldi i Abr))))

(defthm sra-nat-rowp-nth-A-sym-fold-to-stvp
  (implies (A-sym-fold-to-stvp A)
           (sra-nat-rowp (nth i A)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm sra-nat-rowp-A-sym-fold-to-stvi
  (implies (Abrp Abr)
           (sra-nat-rowp (A-sym-fold-to-stvi i Abr))))

(defthm sra-nat-rowp-nth-A-nump
  (implies (A-nump A)
           (sra-rational-rowp (nth i A)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm sra-rational-rowp-A-numi
  (implies (Abrp Abr)
           (sra-rational-rowp (A-numi i Abr))))

(defthm Abrp-!current-time
  (implies (and (Abrp Abr)
                (rationalp new-time))
           (Abrp (!current-time new-time Abr)))
  :hints
  (("Goal" :in-theory (enable !current-time Abrp nth-theory-lemmas))))

(defthm !current-time-does-not-change-access
  (and (equal (A-sym-fold-to-stvi i (!current-time new-time Abr))
              (A-sym-fold-to-stvi i Abr))
       (equal (A-numi i (!current-time new-time Abr))
              (A-numi i Abr)))
  :hints
  (("Goal" :in-theory (enable A-sym-fold-to-stvi
                              A-numi
                              nth-theory-lemmas))))

(defthm !current-time-does-not-change-length
  (and (equal (A-sym-length (!current-time new-time Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (!current-time new-time Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (!current-time new-time Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (!current-time new-time Abr))
              (A-num-length Abr))
       (equal (b-sym-fold-length (!current-time new-time Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (!current-time new-time Abr))
              (b-sym-fold-to-stv-length Abr)))
  :hints
  (("Goal" :in-theory (enable A-sym-fold-to-stv-length
                              A-num-length
                              b-sym-fold-length
                              b-sym-fold-to-stv-length
                              nth-theory-lemmas))))

(defthm symbolp-sim-type
  (implies (Abrp Abr)
           (symbolp (sim-type Abr)))
  :hints
  (("Goal" :in-theory (enable Abrp))))

(defthm symlp-ref-node
  (implies (Abrp Abr)
           (symlp (ref-node Abr)))
  :hints
  (("Goal" :in-theory (enable Abrp))))

(defthm Abrp-!ref-node
  (implies (and (Abrp Abr)
                (symlp x))
           (Abrp (!ref-node x Abr)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(in-theory (disable ref-node sim-type))

(deftheory Abr-theory-defuns
  '(;; Some Abr accessors and updaters.
    b-symi b-sym-foldi b-sym-fold-to-stvi
    A-symi A-sym-foldi A-sym-fold-to-stvi
    A-numi alter-values-alist

    !b-symi !b-sym-foldi !b-sym-fold-to-stvi
    !A-symi !A-sym-foldi !A-sym-fold-to-stvi
    !A-numi !current-time !dim-Abr

    b-sym-length b-sym-fold-length b-sym-fold-to-stv-length
    A-sym-length A-sym-fold-length
    A-sym-fold-to-stv-length A-num-length

    resize-b-sym resize-b-sym-fold
    resize-b-sym-fold-to-stv resize-A-sym
    resize-A-sym-fold resize-A-sym-fold-to-stv
    resize-A-num

    Abrp))

(in-theory (disable Abr-theory-defuns))

;; Define a theory for Abr-theory-lemmas?

;;;;

(defun init-all (i Abr)
  ;; Initialize simulation state
  (declare (xargs :guard (and (natp i)
                              (< i (expt 2 60))
                              (<= i (b-sym-length              Abr))
                              (<= i (b-sym-fold-length         Abr))
                              (<= i (b-sym-fold-to-stv-length  Abr))
                              (<= i (A-sym-length              Abr))
                              (<= i (A-sym-fold-length         Abr))
                              (<= i (A-sym-fold-to-stv-length  Abr))
                              (<= i (A-num-length              Abr))
                              )
                  :stobjs Abr))
  (b* ((i (the (unsigned-byte 60) i))
       ((if (mbe :logic (zp i)
                 :exec  (= i 0)))
        Abr)
       (i-1 (the (unsigned-byte 60) (1- i)))
       (Abr (!b-symi             i-1 ''0 Abr))
       (Abr (!b-sym-foldi        i-1 ''0 Abr))
       (Abr (!b-sym-fold-to-stvi i-1   0 Abr))
       (Abr (!A-symi             i-1 NIL Abr))
       (Abr (!A-sym-foldi        i-1 NIL Abr))
       (Abr (!A-sym-fold-to-stvi i-1 NIL Abr))
       (Abr (!A-numi             i-1 NIL Abr)))
    (init-all i-1 Abr)))

(defthm all-lengths-unchanged-init-all
  (implies (and (<= i (b-sym-length              Abr))
                (<= i (b-sym-fold-length         Abr))
                (<= i (b-sym-fold-to-stv-length  Abr))
                (<= i (A-sym-length              Abr))
                (<= i (A-sym-fold-length         Abr))
                (<= i (A-sym-fold-to-stv-length  Abr))
                (<= i (A-num-length              Abr)))
           (and (equal (b-sym-length (init-all i Abr))
                       (b-sym-length             Abr))
                (equal (b-sym-fold-length (init-all i Abr))
                       (b-sym-fold-length             Abr))
                (equal (b-sym-fold-to-stv-length (init-all i Abr))
                       (b-sym-fold-to-stv-length             Abr))
                (equal (A-sym-length (init-all i Abr))
                       (A-sym-length             Abr))
                (equal (A-sym-fold-length (init-all i Abr))
                       (A-sym-fold-length             Abr))
                (equal (A-sym-fold-to-stv-length (init-all i Abr))
                       (A-sym-fold-to-stv-length             Abr))
                (equal (A-num-length (init-all i Abr))
                       (A-num-length             Abr)))))

(defun resize-Abr-arrays (size Abr)
  (declare (xargs :guard (and (natp size)
                              (< size *2^60*))
                  :stobjs Abr))
  (b* ((Abr (!dim-Abr size Abr))
       ;; Set sizes
       (Abr (resize-b-sym             size Abr))
       (Abr (resize-b-sym-fold        size Abr))
       (Abr (resize-b-sym-fold-to-stv size Abr))
       (Abr (resize-A-sym             size Abr))
       (Abr (resize-A-sym-fold        size Abr))
       (Abr (resize-A-sym-fold-to-stv size Abr))
       (Abr (resize-A-num             size Abr)))
    Abr))

(defthm all-lengths-changed-to-size-resize-Abr-arrays
  (implies (natp size)
           (and (equal (b-sym-length (resize-Abr-arrays size Abr))
                       size)
                (equal (b-sym-fold-length (resize-Abr-arrays size Abr))
                       size)
                (equal (b-sym-fold-to-stv-length (resize-Abr-arrays size Abr))
                       size)
                (equal (A-sym-length (resize-Abr-arrays size Abr))
                       size)
                (equal (A-sym-fold-length (resize-Abr-arrays size Abr))
                       size)
                (equal (A-sym-fold-to-stv-length (resize-Abr-arrays size Abr))
                       size)
                (equal (A-num-length (resize-Abr-arrays size Abr))
                       size))))

(in-theory (disable resize-Abr-arrays))

(defun Abr-size-and-init (size Abr)
  (declare (xargs :guard (and (natp size)
                              (< size *2^60*))
                  :stobjs Abr))
  (b* (;; Set sizes
       (Abr (resize-Abr-arrays size Abr))
       ;; Initialize
       (Abr (init-all size Abr)))
      Abr))

(defthm all-lengths-changed-to-size-Abr-size-and-init
  (implies (and (natp size)
                (< size *2^60*))
           (and (equal (b-sym-length (Abr-size-and-init size Abr))
                       size)
                (equal (b-sym-fold-length (Abr-size-and-init size Abr))
                       size)
                (equal (b-sym-fold-to-stv-length (Abr-size-and-init size Abr))
                       size)
                (equal (A-sym-length (Abr-size-and-init size Abr))
                       size)
                (equal (A-sym-fold-length (Abr-size-and-init size Abr))
                       size)
                (equal (A-sym-fold-to-stv-length (Abr-size-and-init size Abr))
                       size)
                (equal (A-num-length (Abr-size-and-init size Abr))
                       size))))

(in-theory (disable Abr-size-and-init))


; Functions to insert equation tags into matrices

(defun sum-expr-into-b-sym (i expr Abr)
  "Install tag in b vector."
  (declare (xargs :guard (and (natp i)
                              (< i (b-sym-length Abr))
                              (vw-eval-termp expr))
                  :stobjs Abr))
  (b* ((entry (b-symi i Abr))
       (new-entry
        (if (equal entry ''0)
            expr
          (list 'f+ expr entry)))
       (Abr (!b-symi i new-entry Abr)))
    Abr))

(defthm b-sym-size-is-unchanged
  (implies (and (natp i)
                (< i (b-sym-length Abr)))
           (equal (b-sym-length (sum-expr-into-b-sym i expr Abr))
                  (b-sym-length Abr))))

(defthm sum-expr-into-b-sym-all-other-lengths-unchanged
  (and (equal (b-sym-fold-length (sum-expr-into-b-sym i expr Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (sum-expr-into-b-sym i expr Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-length (sum-expr-into-b-sym i expr Abr))
              (A-sym-length Abr))
       (equal (A-sym-fold-length (sum-expr-into-b-sym i expr Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (sum-expr-into-b-sym i expr Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (sum-expr-into-b-sym i expr Abr))
              (A-num-length Abr))))

(defthm Abrp-sum-expr-into-b-sym
  (implies (and (Abrp Abr)
                (vw-eval-termp expr))
           (Abrp (sum-expr-into-b-sym i expr Abr))))

(in-theory (disable sum-expr-into-b-sym))

; Need theorems for (see below) corresponding to above theorems

;   A-sym

(defun sum-expr-into-A-sym (i j expr Abr)
  "Install tag in A matrix."
  (declare (xargs :guard (and (natp i)
                              (natp j)
                              (vw-eval-termp expr)
                              (< i (A-sym-length Abr))
                              (< j (A-sym-length Abr)))
                  :stobjs Abr))
  (b* ((row (A-symi i Abr))
       (entry (sra-rget j row ''0))
       (new-entry
        (if (equal entry ''0)
            expr
          (list 'f+ expr entry)))
       (new-row (sra-rput j row new-entry))
       (Abr (!A-symi i new-row Abr)))
    Abr))

(defthm Abrp-sum-expr-into-A-sym
  (implies (and (Abrp Abr)
                (natp j)
                (< i (A-sym-length Abr))
                (vw-eval-termp expr))
           (Abrp (sum-expr-into-A-sym i j expr Abr))))

(defthm sum-expr-into-A-sym-size-unchanged
  (implies
   (and (natp i)
        (< i (A-sym-length Abr)))
   (equal (A-sym-length (sum-expr-into-A-sym i j expr Abr))
          (A-sym-length Abr))))

(defthm sum-expr-into-A-sym-everything-else-unchanged
  (and (equal (b-sym-length (sum-expr-into-A-sym i j expr Abr))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (sum-expr-into-A-sym i j expr Abr))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (sum-expr-into-A-sym i j expr Abr))
              (b-sym-fold-to-stv-length Abr))
       (equal (A-sym-fold-length (sum-expr-into-A-sym i j expr Abr))
              (A-sym-fold-length Abr))
       (equal (A-sym-fold-to-stv-length (sum-expr-into-A-sym i j expr Abr))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-num-length (sum-expr-into-A-sym i j expr Abr))
              (A-num-length Abr))))

(in-theory (disable sum-expr-into-A-sym))

; Functions for adding component tags to symbolic matrices A and b.

; We start with the voltage-source tag.

(defun add-voltage-source-tag-to-Ab (x-names occ sim-type Abr)
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrencep occ)
                              (symbolp sim-type))
                  :stobjs Abr
                  :guard-hints
                  (("Goal" :in-theory (e/d (occurrencep)
                                           (not no-duplicatesp-equal
                                                rfix member-equal nth abrp))))))
  (case-match occ
    ((& 'v (node+ node-) (branch) (voltage-equation))
     (b* (((unless (and (member-eq branch x-names)
                        (member-eq node+  x-names)
                        (member-eq node-  x-names)))
           (prog2$
            (cw "add-voltage-source-tag-to-Ab: ~
                 Invalid branch/node name: ~p0.~%" occ)
            Abr))

          ;; No check is performed on input-source equation.

          (branch-index (pos branch x-names))
          (node+-index  (pos node+  x-names))
          (node--index  (pos node-  x-names))

          (Abr (sum-expr-into-A-sym node+-index branch-index ''1 Abr))
          (Abr (sum-expr-into-A-sym node--index branch-index ''-1 Abr))

          (Abr (sum-expr-into-A-sym branch-index node+-index ''1 Abr))
          (Abr (sum-expr-into-A-sym branch-index node--index ''-1 Abr))

          (Abr (sum-expr-into-b-sym
                branch-index
                ;; We should think a bit.  We don't have unadorned names
                ;; any more.  It would be good to find a short,
                ;; de-reference name.
                (if (eq sim-type 'voltage)
                    voltage-equation
                  `(f+ (f- ,node+ ,node-)
                       (f+ (f* (f/ $hn$ '2)
                               (f- ,(dp node+) ,(dp node-)))
                           (f* (f/ (f* *pi* $hn$)
                                   *Phi0*)
                               ,voltage-equation))))
                Abr)))
       Abr))
    (& (prog2$ (cw "add-voltage-source-tag-to-Ab: ~
                    Unexpected exit!~%") Abr))))

(defthm Abrp-add-voltage-source-tag-to-Ab
  (implies (and (Abrp Abr)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr))
                (occurrencep occ))
           (Abrp (add-voltage-source-tag-to-Ab x-names occ sim-type
                                               Abr))))

(defthm add-voltage-source-tag-to-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (add-voltage-source-tag-to-Ab
                              x-names occ sim-type Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (add-voltage-source-tag-to-Ab
                                   x-names occ sim-type Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (add-voltage-source-tag-to-Ab
                                          x-names occ sim-type Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (add-voltage-source-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (add-voltage-source-tag-to-Ab
                                   x-names occ sim-type Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (add-voltage-source-tag-to-Ab
                                          x-names occ sim-type Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (add-voltage-source-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-num-length Abr)))))

(in-theory (disable add-voltage-source-tag-to-Ab))

; Here is the current-source tag.

(defun add-current-source-tag-to-Ab (x-names occ sim-type Abr)
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrencep occ)
                              (symbolp sim-type))
                  :stobjs Abr
                  :guard-hints
                  (("Goal" :in-theory (e/d (occurrencep)
                                           (not no-duplicatesp-equal
                                                rfix member-equal)))))
           (ignorable sim-type))
  (case-match occ
    ((& 'i (node+ node-) (branch) (current-equation))
     (b* (((unless (and (member-eq branch x-names)
                        (member-eq node+  x-names)
                        (member-eq node-  x-names)))
           (prog2$
            (cw "add-current-source-tag-to-Ab: ~
                 Invalid branch/node name: ~p0.~%" occ)
            Abr))

          (branch-index (pos branch x-names))
          (node+-index  (pos node+  x-names))
          (node--index  (pos node-  x-names))

          (Abr (sum-expr-into-A-sym node+-index branch-index ''1 Abr))
          (Abr (sum-expr-into-A-sym node--index branch-index ''-1 Abr))
          (Abr (sum-expr-into-A-sym branch-index branch-index ''1 Abr))

          (Abr (sum-expr-into-b-sym
                branch-index current-equation Abr)))
       Abr))
    (& (prog2$ (cw "add-current-source-tag-to-Ab: ~
                    Unexpected exit!~%") Abr))))

(defthm Abrp-add-current-source-tag-to-Ab
  (implies (and (Abrp Abr)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr))
                (occurrencep occ))
           (Abrp (add-current-source-tag-to-Ab x-names occ sim-type
                                               Abr))))

(defthm add-current-source-tag-to-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (add-current-source-tag-to-Ab
                              x-names occ sim-type Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (add-current-source-tag-to-Ab
                                   x-names occ sim-type Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (add-current-source-tag-to-Ab
                                          x-names occ sim-type Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (add-current-source-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (add-current-source-tag-to-Ab
                                   x-names occ sim-type Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (add-current-source-tag-to-Ab
                                          x-names occ sim-type Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (add-current-source-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-num-length Abr)))))

(in-theory (disable add-current-source-tag-to-Ab))


(defun add-phase-source-tag-to-Ab (x-names occ sim-type Abr)
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrencep occ)
                              (symbolp sim-type))
                  :stobjs Abr
                  :guard-hints
                  (("Goal" :in-theory (e/d (occurrencep)
                                           (not no-duplicatesp-equal
                                                rfix member-equal)))))
           (ignorable sim-type))
  (case-match occ
    ((& 'p (node+ node-) (branch) (phase-equation))
     (b* (((unless (and (member-eq branch x-names)
                        (member-eq node+  x-names)
                        (member-eq node-  x-names)))
           (prog2$
            (cw "add-phase-source-tag-to-Ab: ~
                 Invalid branch/node name: ~p0.~%" occ)
            Abr))

          (branch-index (pos branch x-names))
          (node+-index  (pos node+  x-names))
          (node--index  (pos node-  x-names))

          (Abr (sum-expr-into-A-sym node+-index branch-index ''1 Abr))
          (Abr (sum-expr-into-A-sym node--index branch-index ''-1 Abr))
          (Abr (sum-expr-into-A-sym branch-index node+-index ''1 Abr))
          (Abr (sum-expr-into-A-sym branch-index node--index ''-1 Abr))

          (Abr (sum-expr-into-b-sym
                branch-index
                (if (eq sim-type 'voltage)
                    `(f- (f* (f* (f/ *phi0* (f* '2 *pi*))
                                 (f/ '2 $hn$))
                             (f- ,phase-equation
                                 ;; We do not store the phase in a
                                 ;; voltage-based simulation. We
                                 ;; rewrite the phase-equation in
                                 ;; terms of (- $time$ $hn$) to
                                 ;; calculate phi_{n-1}.
                                 ,(phase-equation-at-$time$-$hn$
                                   phase-equation)))
                         (f- ,node+ ,node-))
                  phase-equation)
                Abr)))
       Abr))
    (& (prog2$ (cw "add-phase-source-tag-to-Ab:  Unexpected exit!~%") Abr))))

(defthm Abrp-add-phase-source-tag-to-Ab
  (implies (and (Abrp Abr)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr))
                (occurrencep occ))
           (Abrp (add-phase-source-tag-to-Ab x-names occ sim-type
                                             Abr))))

(defthm add-phase-source-tag-to-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (add-phase-source-tag-to-Ab
                              x-names occ sim-type Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (add-phase-source-tag-to-Ab
                                   x-names occ sim-type Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (add-phase-source-tag-to-Ab
                                          x-names occ sim-type Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (add-phase-source-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (add-phase-source-tag-to-Ab
                                   x-names occ sim-type Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (add-phase-source-tag-to-Ab
                                          x-names occ sim-type Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (add-phase-source-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-num-length Abr)))))

(in-theory (disable add-phase-source-tag-to-Ab))

; Next is the resistor.

(defun add-resistor-tag-to-Ab (x-names occ sim-type Abr)
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrencep occ)
                              (symbolp sim-type))
                  :stobjs Abr
                  :guard-hints
                  (("Goal" :in-theory (e/d (occurrencep)
                                           (not no-duplicatesp-equal
                                                rfix member-equal nth))))))
  (case-match occ
    ((& 'r (node+ node-) (&) (resistance))
     (b* (((unless (and (member-eq node+  x-names)
                        (member-eq node-  x-names)))
           (prog2$
            (cw "add-resistor-tag-to-Ab: ~
                 Invalid branch/node name: ~p0.~%" occ)
            Abr))

          ;; We do not anticipate time-varying component values; even
          ;; though our simulator is coded in a manner that might
          ;; tolerate such, but we are uncertain of the mathematical
          ;; implications.  Here, we require that a resistor provides
          ;; non-zero (positive) resistance, but this check does
          ;; permit positive, non-zero, time-varying resistance.

          (node+-index  (pos node+  x-names))
          (node--index  (pos node-  x-names))

          ;;((unless (vw-eval-termp resistance))
          ;; Abr)
          (G `(f-1/x ,resistance))
          (G- `(f0- ,G))

          (phi0/piRhn `(f/ *phi0* (f* *pi* (f* ,resistance $hn$))))
          (phi0/piRhn- `(f0- ,phi0/piRhn))

          ;; Note for Warren: please review this and associated 2x2
	  ;; stamps in vwsim-builders-manual.pdf
	  (Abr
	   (sum-expr-into-A-sym
	    node+-index node+-index
	    (if (eq sim-type 'voltage) G phi0/piRhn)
	    Abr))
          (Abr
	   (sum-expr-into-A-sym
	    node+-index  node--index
	    (if (eq sim-type 'voltage) G- phi0/piRhn-)
	    Abr))
          (Abr
	   (sum-expr-into-A-sym
	    node--index node+-index
	    (if (eq sim-type 'voltage) G- phi0/piRhn-)
	    Abr))
          (Abr
	   (sum-expr-into-A-sym
	    node--index node--index
	    (if (eq sim-type 'voltage) G phi0/piRhn)
	    Abr))

          (phi0/2piR `(f/ *phi0* (f* '2 (f* *pi* ,resistance))))

          (b-term `(f* ,phi0/2piR (f+ (f* (f/ '2 $hn$) (f- ,node+ ,node-))
				      (f- ,(dp node+) ,(dp node-)))))
	  (b-term- `(f0- ,b-term))

          (Abr
	   (if (eq sim-type 'voltage)
	       Abr
	     (sum-expr-into-b-sym node+-index b-term Abr)))
	  (Abr
	   (if (eq sim-type 'voltage)
	       Abr
	     (sum-expr-into-b-sym node--index b-term- Abr)))

          )
       Abr))
    (& (prog2$ (cw "add-resistor-tag-to-Ab:  Unexpected exit!~%") Abr))))

(defthm Abrp-add-resistor-tag-to-Ab
  (implies (and (Abrp Abr)
                (occurrencep occ)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr)))
           (Abrp (add-resistor-tag-to-Ab x-names occ sim-type
                                         Abr))))

(defthm add-resistor-tag-to-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (add-resistor-tag-to-Ab
                              x-names occ sim-type Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (add-resistor-tag-to-Ab
                                   x-names occ sim-type Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (add-resistor-tag-to-Ab
                                          x-names occ sim-type Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (add-resistor-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (add-resistor-tag-to-Ab
                                   x-names occ sim-type Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (add-resistor-tag-to-Ab
                                          x-names occ sim-type Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (add-resistor-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-num-length Abr)))))

(in-theory (disable add-resistor-tag-to-Ab))

;  Capacitor
(defun add-capacitor-tag-to-Ab (x-names occ sim-type  Abr)
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrencep occ)
                              (symbolp sim-type))
                  :stobjs Abr
                  :guard-hints
                  (("Goal" :in-theory (e/d (occurrencep)
                                           (not no-duplicatesp-equal
                                                rfix member-equal))))))
  (case-match occ
    ((& 'c (node+ node-) (branch) (capacitance))
     (b* (((unless (and (member-eq branch x-names)
                        (member-eq node+  x-names)
                        (member-eq node-  x-names)))
           (prog2$
            (cw "add-capacitor-tag-to-Ab: ~
                 Invalid branch/node name: ~p0.~%" occ)
            Abr))

          (branch-index (pos branch x-names))
          (node+-index  (pos node+  x-names))
          (node--index  (pos node-  x-names))

          (Abr (sum-expr-into-A-sym node+-index branch-index ''1 Abr))
          (Abr (sum-expr-into-A-sym node--index branch-index ''-1 Abr))

          (Abr (sum-expr-into-A-sym branch-index node+-index ''1 Abr))
          (Abr (sum-expr-into-A-sym branch-index node--index ''-1 Abr))

          (Abr (sum-expr-into-A-sym
                branch-index branch-index
                (if (eq sim-type 'voltage)
                    `(f0- (f/ $hn$ (f* '2 ,capacitance)))
                  `(f0- (f/ (f* *pi* (f* $hn$ $hn$))
                            (f* '2 (f* ,capacitance *Phi0*)))))
                Abr))

          (Abr (sum-expr-into-b-sym
                branch-index
                (if (eq sim-type 'voltage)
                    `(f+ (f- ,node+ ,node-)
                         (f* (f/ $hn$ (f* '2 ,capacitance))
                             ,branch))
                  `(f+ (f- ,node+ ,node-)
                       (f+ (f* $hn$ (f- ,(dp node+) ,(dp node-)))
                           (f* (f/ (f* *pi* (f* $hn$ $hn$))
                                   (f* '2 (f* ,capacitance *Phi0*)))
                               ,branch))))
                Abr)))
       Abr))
    (& (prog2$ (cw "add-capacitor-tag-to-Ab:  Unexpected exit!~%") Abr))))

(defthm Abrp-add-capacitor-tag-to-Ab
  (implies (and (Abrp Abr)
                (occurrencep occ)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr)))
           (Abrp (add-capacitor-tag-to-Ab x-names occ sim-type
                                          Abr))))

(defthm add-capacitor-tag-to-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (add-capacitor-tag-to-Ab
                              x-names occ sim-type Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (add-capacitor-tag-to-Ab
                                   x-names occ sim-type Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (add-capacitor-tag-to-Ab
                                          x-names occ sim-type Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (add-capacitor-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (add-capacitor-tag-to-Ab
                                   x-names occ sim-type Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (add-capacitor-tag-to-Ab
                                          x-names occ sim-type Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (add-capacitor-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-num-length Abr)))))

(in-theory (disable add-capacitor-tag-to-Ab))

; Inductor

(defun add-inductor-tag-to-Ab (x-names occ sim-type  Abr)
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrencep occ)
                              (symbolp sim-type))
                  :stobjs Abr
                  :guard-hints
                  (("Goal" :in-theory (e/d (occurrencep)
                                           (not no-duplicatesp-equal
                                                rfix member-equal))))))
  (case-match occ
    ((& 'l (node+ node-) (branch) (inductance))
     (b* (((unless (and (member-eq branch x-names)
                        (member-eq node+  x-names)
                        (member-eq node-  x-names)))
           (prog2$
            (cw "add-inductor-tag-to-Ab:  Invalid branch/node name: ~p0.~%"
                occ)
            Abr))

          (branch-index (pos branch x-names))
          (node+-index  (pos node+  x-names))
          (node--index  (pos node-  x-names))

          (Abr (sum-expr-into-A-sym node+-index branch-index ''1 Abr))
          (Abr (sum-expr-into-A-sym node--index branch-index ''-1 Abr))

          (Abr (sum-expr-into-A-sym branch-index node+-index ''1 Abr))
          (Abr (sum-expr-into-A-sym branch-index node--index ''-1 Abr))

          (Abr (sum-expr-into-A-sym
              branch-index branch-index (if (eq sim-type 'voltage)
                  `(f0- (f/ (f* '2 ,inductance) $hn$))
                `(f0- (f/ (f* '2 (f* *pi* ,inductance))
                          *Phi0*)))
              Abr))

          (Abr
           (if (eq sim-type 'voltage)
               (sum-expr-into-b-sym branch-index
                                    `(f- (f- ,node- ,node+)
                                         (f* (f/ (f* '2 ,inductance) $hn$)
                                             ,branch))
                                    Abr)
                 Abr)))
       Abr))
    (& (prog2$ (cw "add-inductor-tag-to-Ab:  Unexpected exit!~%") Abr))))

(defthm Abrp-add-inductor-tag-to-Ab
  (implies (and (Abrp Abr)
                (occurrencep occ)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr)))
           (Abrp (add-inductor-tag-to-Ab x-names occ sim-type
                                          Abr))))

(defthm add-inductor-tag-to-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (add-inductor-tag-to-Ab
                              x-names occ sim-type Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (add-inductor-tag-to-Ab
                                   x-names occ sim-type Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (add-inductor-tag-to-Ab
                                          x-names occ sim-type Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (add-inductor-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (add-inductor-tag-to-Ab
                                   x-names occ sim-type Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (add-inductor-tag-to-Ab
                                          x-names occ sim-type Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (add-inductor-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-num-length Abr)))))

(in-theory (disable add-inductor-tag-to-Ab))

; Josephson Junction

(defun add-B-tag-to-Ab (x-names occ sim-type  Abr)
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrencep occ)
                              (symbolp sim-type))
                  :stobjs Abr
                  :guard-hints
                  (("Goal" :in-theory (e/d (occurrencep)
                                           (not no-duplicatesp-equal
                                                rfix member-equal
                                                nth abrp))))))
  ;; Our JJ model is based on Joey Delport's dissertation and papers.
  ;; We believe Delport's JJ model does not include the hysteresis
  ;; that appears in voltage-current graphs documenting JJ behavior.

  (case-match occ
    ((& 'b (node+ node-) (branch)
        (icrit ; Josephson Junction
         area  ; JJ area
         vg    ; Vgap
         rn    ; JJ normal resistance
         r0    ; JJ subgap resistance
         cap   ; C - shunt capacitance in JJ RCSJ model
         ))

     (b* (((unless (and (member-eq branch x-names)
                        (member-eq node+  x-names)
                        (member-eq node-  x-names)))
           (prog2$
            (cw "add-B-tag-to-Ab:  Invalid branch/node name: ~p0.~%" occ)
            Abr))

          ;; Using the AREA parameter, we adjust other JJ parameters

          (r0 `(f/ ,r0 ,area))
          (rn  `(f/ ,rn  ,area))
          (icrit `(f* ,icrit ,area))
          (cap `(f* ,cap ,area))

; Note: the modeling equations for Josephon junctions (JJ) are
; complex.  Our approach follows that of Delport, where we have
; different equations for three regions depending on the voltage
; across a JJ.  Three different model equations are selected based on
; the junction voltage.  WARNING: a JJ operates the same way
; independent of the voltage polarity, so we must be careful!

          (branch-index (pos branch x-names))
          (node+-index  (pos node+  x-names))
          (node--index  (pos node-  x-names))

          ;; Here, we have chosen to name three voltage regions
          ;; as they pertain to the voltage, Vjj, across a JJ:
          ;; We let "G" abbreviate "conductance"

          ;; G<Gap-DV: when Vjj < Vgap - DeltaV/2
          ;; G_in_Gap: when Vgap - DeltaV/2 <= Vjj < Vgap + DeltaV/2
          ;; G>Gap+DV: when Vgap + DeltaV/2 <= Vjj

          (2C-over-hn `(f/ (f* '2 ,cap) $hn$))
          (Vgap-DV `(f- ,vg (f/ *DeltaV* '2))) ;!sign independent
          (Vgap+DV `(f+ ,vg (f/ *DeltaV* '2))) ;!sign independent

          ;; Maybe memoize this next group of expressions
          (2e/h_bar `(f/ (f* '2 *e_C*) *h_bar*))
          (hn/2 `(f/ $hn$ '2))
          (hn/2*2e/h_bar `(f* ,hn/2 ,2e/h_bar))
          (hn/2*2e/h_bar- `(f0- ,hn/2*2e/h_bar))

          ;; Conductances in three regions
          (GT `(f/ ,icrit (f* *Icfact* *DeltaV*)))

          (G<Gap-DV `(f+ (f-1/x ,r0) ,2C-over-hn))
          (G_in_Gap `(f+ ,GT ,2C-over-hn))
          (G>Gap+DV `(f+ (f-1/x ,rn) ,2C-over-hn))

          ;; Currents in three regions
          (It<Gap-DV ''0)
          (It_in_Gap `(f* ,Vgap-DV (f- (f/ '1 ,r0) ,GT)))
          (It>Gap+DV `(f+ (f/ ,icrit *Icfact*)
                          (f- (f/ ,Vgap-DV ,r0)
                              (f/ ,Vgap+DV ,rn))))

          (v-n-1  `(f-     ,node+      ,node-)) ; Works for voltage and phase
          (vp-n-1 `(f- ,(dp node+) ,(dp node-))) ; Works for voltage and phase

          ;; Something for Warren and Vivek to consider:

          ;; Delport chooses to keep vp-n-1 at 0 for the first 3-4 (4?)
          ;; iterations.
          ;; 1. Is this a good idea? Are there better (or worse) ways
          ;;    to deal with this? Which way is ``correct''?
          ;; 2. If we choose to follow Delport's approach, we clearly
          ;;    need to store the first 3/4 values of the derivative
          ;;    as 0. Do we do this in xp-updates? Does forcing the
          ;;    derivative to be 0 cause inconsisties for the stamps
          ;;    of other components? Do we force ALL derivatives to be
          ;;    0 for the first 3/4 iterations?

          (vGn (if (eq sim-type 'voltage) ; Voltage guess
                   `(f+ ,v-n-1
                        (f* $hn$ ,vp-n-1))
                 `(f+ ,branch
                      (f* $hn$ ,(dp branch)))))

          (phiGn (if (eq sim-type 'voltage) ; Phase guess
                     `(f+ ,branch
                          (f* ,hn/2*2e/h_bar
                              (f+ ,v-n-1 ,vGn)))
                   `(f+ ,v-n-1
                        (f* ,hn/2*2e/h_bar
                            (f+ ,branch ,vGn)))))

          #||
          ;; This made things work more like JoSIM. ;
          ;; We need to understand JoSIM's startup procedure. ;
          (phiGn (if (eq sim-type 'voltage)      ; Phase guess ;
          `(if (f< $time$ (f* '3 $hn$))  ; to zero for three steps ;
          '0 ;
          (f+ ,branch ;
          (f* ,hn/2*2e/h_bar ;
          (f+ ,v-n-1 ,vGn)))) ;
          `(f+ ,v-n-1 ;
          (f* ,hn/2*2e/h_bar ;
          (f+ ,branch ,vGn))))) ;
          ||#

          (Is (if (eq sim-type 'voltage)
                  `(f+ (f0- (f* ,icrit (f-sin ,phiGn)))
                       (f+ (f* ,2C-over-hn ,v-n-1)
                           (f* ,cap ,vp-n-1)))
                `(f+ (f0- (f* ,icrit (f-sin ,phiGn)))
                     (f+ (f* ,2C-over-hn ,branch)
                         (f* ,cap ,(dp branch))))))

          ;; Here we deal with the sign of the voltage gap.
          (junction-conductance `(if (f< (f-abs ,vGn) ,Vgap-DV)
                                     ,G<Gap-DV
                                   (if (f< (f-abs ,vGn) ,Vgap+DV)
                                       ,G_in_Gap
                                     ,G>Gap+DV)))
          (junction-conductance- `(f0- ,junction-conductance))

          ;; Again, we deal with the sign of the voltage gap.
          (transistion-current `(if (f< (f-abs ,vGn) ,Vgap-DV)
                                    ,It<Gap-DV
                                  (if (f< (f-abs ,vGn) ,Vgap+DV)
                                      ,It_in_Gap
                                    ,It>Gap+DV)))

          ;; Finally, we set the sign of the transistion current based
          ;; on the sign of the voltage gap.
          (transistion-current-with-sign
           `(if (f< ,vGn '0)
                (f0- ,transistion-current)
              ,transistion-current))

          (Is-It `(f- ,Is ,transistion-current-with-sign))
          (Is-It- `(f0- ,Is-It))

          (Abr (if (eq sim-type 'voltage)
                   (b* ((Abr
                         (sum-expr-into-A-sym node+-index
                                              node+-index
                                              junction-conductance
                                              Abr))
                        (Abr
                         (sum-expr-into-A-sym node+-index
                                              node--index
                                              junction-conductance-
                                              Abr))
                        (Abr
                         (sum-expr-into-A-sym node--index
                                              node+-index
                                              junction-conductance-
                                              Abr))
                        (Abr
                         (sum-expr-into-A-sym node--index
                                              node--index
                                              junction-conductance
                                              Abr))
                        (Abr
                         (sum-expr-into-A-sym branch-index
                                              node+-index
                                              hn/2*2e/h_bar-
                                              Abr))
                        (Abr
                         (sum-expr-into-A-sym branch-index
                                              node--index
                                              hn/2*2e/h_bar
                                              Abr))
                        (Abr
                         (sum-expr-into-A-sym branch-index
                                              branch-index
                                              ''1 Abr)))
                     Abr)

                 (b* ((Abr (sum-expr-into-A-sym node+-index
                                                branch-index
                                                junction-conductance
                                                Abr))
                      (Abr (sum-expr-into-A-sym node--index
                                                branch-index
                                                junction-conductance-
                                                Abr))
                      (Abr (sum-expr-into-A-sym branch-index
                                                node+-index ''1
                                                Abr))
                      (Abr (sum-expr-into-A-sym branch-index
                                                node--index
                                                ''-1 Abr))
                      (Abr (sum-expr-into-A-sym branch-index
                                                branch-index
                                                hn/2*2e/h_bar-
                                                Abr)))
                   Abr)))

          (Abr (if (eq sim-type 'voltage)
                   ;; JJ b voltage
                   (b* ((Abr (sum-expr-into-b-sym node+-index Is-It Abr))
                        (Abr (sum-expr-into-b-sym node--index Is-It- Abr))
                        (Abr (sum-expr-into-b-sym
                              branch-index `(f+ ,branch
                                                (f* ,hn/2*2e/h_bar ,v-n-1))
                              Abr)))
                     Abr)
                 ;; JJ Abr phase
                 (b* ((Abr (sum-expr-into-b-sym node+-index Is-It Abr))
                      (Abr (sum-expr-into-b-sym node--index Is-It- Abr))
                      (Abr (sum-expr-into-b-sym
                            branch-index `(f+ ,v-n-1
                                              (f* ,hn/2*2e/h_bar ,branch))
                            Abr)))
                   Abr))))
       Abr))
    (& (prog2$ (cw "add-B-tag-to-Ab:  Unexpected exit!~%") Abr))))

(defthm Abrp-add-b-tag-to-Ab
  (implies (and (Abrp Abr)
                (occurrencep occ)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr)))
           (Abrp (add-b-tag-to-Ab x-names occ sim-type
                                          Abr))))

(defthm add-b-tag-to-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (add-b-tag-to-Ab
                              x-names occ sim-type Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (add-b-tag-to-Ab
                                   x-names occ sim-type Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (add-b-tag-to-Ab
                                          x-names occ sim-type Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (add-b-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (add-b-tag-to-Ab
                                   x-names occ sim-type Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (add-b-tag-to-Ab
                                          x-names occ sim-type Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (add-b-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-num-length Abr)))))

(in-theory (disable add-b-tag-to-Ab))

; The transmission line

(defun t-triples (pos0-index neg0-index pos1-index neg1-index
                             br0-index br1-index sim-type impedance)
  (declare (xargs :guard t))
  (list (list pos0-index br0-index ''1)
        (list neg0-index br0-index ''-1)
        (list pos1-index br1-index ''1)
        (list neg1-index br1-index ''-1)
        (list br0-index  pos0-index ''1)
        (list br0-index  neg0-index ''-1)
        (list br1-index  pos1-index ''1)
        (list br1-index  neg1-index ''-1)
        (list br0-index br0-index
              (if (eq sim-type 'voltage)
                  `(f0- ,impedance)
                `(f0- (f/ (f* *pi* (f* $hn$ ,impedance))
                          *phi0*))))
        (list br1-index br1-index
              (if (eq sim-type 'voltage)
                  `(f0- ,impedance)
                `(f0- (f/ (f* *pi* (f* $hn$ ,impedance))
                          *phi0*))))))

(defun good-triples-p (trips size)
  (declare (xargs :guard (natp size)))
  (cond ((atom trips) (null trips))
        (t (let ((trip (car trips)))
             (and (true-listp trip)
                  (equal (len trip) 3)
                  (natp (car trip))
                  (< (car trip) size)
                  (natp (cadr trip))
                  (< (cadr trip) size)
                  (vw-eval-termp (caddr trip))
                  (good-triples-p (cdr trips) size))))))

(defun sum-expr-into-A-sym-lst (trips Abr)
  (declare (xargs :guard (good-triples-p trips (A-sym-length Abr))
                  :stobjs Abr))
  (cond
   ((endp trips) Abr)
   (t (let* ((trip (car trips))
             (Abr (sum-expr-into-A-sym
                   (car trip) (cadr trip) (caddr trip) Abr)))
        (sum-expr-into-A-sym-lst (cdr trips) Abr)))))

(defun add-T-tag-to-Ab (x-names occ sim-type  Abr)
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrencep occ)
                              (symbolp sim-type))
                  :stobjs Abr
                  :guard-hints
                  (("Goal" :do-not-induct t :in-theory (e/d (occurrencep)
                                           (not no-duplicatesp-equal
                                                rfix member-equal)))))
           (ignorable sim-type ))
  (case-match occ
    ((& 't (pos0 neg0  pos1 neg1) (br0 br1)
        ;; Delay concerns the end-to-end signal propagation time
        (delay
         ;; The impedance is a complex-load that the physical
         ;; implemention will hopefully provide.
         impedance))
     (b* (((unless (and (member-eq pos0 x-names)
                        (member-eq neg0 x-names)
                        (member-eq pos1 x-names)
                        (member-eq neg1 x-names)
                        (member-eq br0  x-names)
                        (member-eq br1  x-names)))
           (prog2$
            (cw "add-T-tag-to-Ab:  Invalid branch/node name: ~p0.~%" occ)
            Abr))

          (pos0-index (pos pos0 x-names))
          (neg0-index (pos neg0 x-names))
          (pos1-index (pos pos1 x-names))
          (neg1-index (pos neg1 x-names))
          (br0-index  (pos br0  x-names))
          (br1-index  (pos br1  x-names))

          (trips (t-triples pos0-index neg0-index pos1-index neg1-index
                            br0-index br1-index sim-type impedance))

          (Abr (sum-expr-into-A-sym-lst trips Abr))

          ;; $hn$ can vary during the simulation cycle. Therefore, we
          ;; provide the delay to the vw-eval "back" function, which
          ;; will determine how to get previous values out of the
          ;; record.
          (Abr (sum-expr-into-b-sym
                br0-index
                (if (eq sim-type 'voltage)
                    `(f+ (f- (back ,pos1 ,delay)
                             (back ,neg1 ,delay))
                         (f* ,impedance (back ,br1 ,delay)))
                  `(f+ (f- ,pos0 ,neg0)
                       (f+ (f* (f/ $hn$ '2)
                               (f+ (f- ,(dp pos0) ,(dp neg0))
                                   (f- (back ,(dp pos1) ,delay)
                                       (back ,(dp neg1) ,delay))))
                           (f* (f/ (f* *pi* (f* $hn$ ,impedance))
                                   *phi0*)
                               (back ,br1 ,delay)))))
                Abr))
          (Abr (sum-expr-into-b-sym
                br1-index
                (if (eq sim-type 'voltage)
                    `(f+ (f- (back ,pos0 ,delay)
                             (back ,neg0 ,delay))
                         (f* ,impedance
                             (back ,br0 ,delay)))
                  `(f+ (f- ,pos1 ,neg1)
                       (f+ (f* (f/ $hn$ '2)
                               (f+ (f- ,(dp pos1) ,(dp neg1))
                                   (f- (back ,(dp pos0) ,delay)
                                       (back ,(dp neg0) ,delay))))
                           (f* (f/ (f* *pi* (f* $hn$ ,impedance))
                                   *phi0*)
                               (back ,br0 ,delay)))))
                Abr)))
       Abr))
    (& (prog2$ (cw "add-T-tag-to-Ab:  Unexpected exit!~%") Abr))))

(defthm Abrp-add-T-tag-to-Ab
  (implies (and (Abrp Abr)
                (occurrencep occ)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr)))
           (Abrp (add-T-tag-to-Ab x-names occ sim-type
                                          Abr))))

(defthm add-T-tag-to-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (add-T-tag-to-Ab
                              x-names occ sim-type Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (add-T-tag-to-Ab
                                   x-names occ sim-type Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (add-T-tag-to-Ab
                                          x-names occ sim-type Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (add-T-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (add-T-tag-to-Ab
                                   x-names occ sim-type Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (add-T-tag-to-Ab
                                          x-names occ sim-type Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (add-T-tag-to-Ab
                              x-names occ sim-type Abr))
               (A-num-length Abr)))))

(in-theory (disable add-T-tag-to-Ab))

; Mutual inductance (aka transformer)

(defun triples (br0-index br1-index
                           sim-type M)
  (declare (xargs :guard t))
  (list (list br0-index  br1-index
              (if (eq sim-type 'voltage)
                  `(f0- (f/ (f* '2 ,M) $hn$))
                `(f0- (f/ (f* '2 (f* *pi* ,M)) *phi0*))))

        (list br1-index  br0-index
              (if (eq sim-type 'voltage)
                  `(f0- (f/ (f* '2 ,M) $hn$))
                `(f0- (f/ (f* '2 (f* *pi* ,M)) *phi0*))))))

(defun add-K-tag-to-Ab-help (inductor0 inductor1)
  (declare (xargs :guard (and (occurrencep inductor0)
                              (occurrencep inductor1))
                  :guard-hints
                  (("Goal" :in-theory (e/d (occurrencep)
                                           (no-duplicatesp-equal))))))
       (b* ((br0-inductance0 (cdddr inductor0))
            (br1-inductance1 (cdddr inductor1))
            (br0 (caar br0-inductance0))
            (br1 (caar br1-inductance1))
            (inductance0 (caadr br0-inductance0))
            (inductance1 (caadr br1-inductance1)))
         (list br0 br1 inductance0 inductance1)))

(defthm car-add-K-tag-to-Ab-help
  (implies (and (occurrencep inductor0)
                (occurrencep inductor1)
                (equal (cadr inductor0) 'l))
           (and (symbolp (car (add-K-tag-to-Ab-help inductor0 inductor1)))
                (symlp (car (add-K-tag-to-Ab-help inductor0 inductor1)))))
  :hints
  (("Goal" :in-theory (e/d (occurrencep)
                           (no-duplicatesp-equal member-equal)))))

(defthm cadr-add-K-tag-to-Ab-help
  (implies (and (occurrencep inductor0)
                (occurrencep inductor1)
                (equal (cadr inductor1) 'l))
           (and (symbolp (cadr (add-K-tag-to-Ab-help inductor0 inductor1)))
                (symlp (cadr (add-K-tag-to-Ab-help inductor0 inductor1)))))
  :hints
  (("Goal" :in-theory (e/d (occurrencep)
                           (no-duplicatesp-equal member-equal)))))

(defthm caddr-add-K-tag-to-Ab-help
  (implies (and (occurrencep inductor0)
                (occurrencep inductor1)
                (equal (cadr inductor0) 'l))
           (vw-eval-termp (caddr (add-K-tag-to-Ab-help inductor0 inductor1))))
  :hints
  (("Goal" :in-theory (e/d (occurrencep)
                           (no-duplicatesp-equal member-equal)))))

(defthm cadddr-add-K-tag-to-Ab-help
  (implies (and (occurrencep inductor0)
                (occurrencep inductor1)
                (equal (cadr inductor1) 'l))
           (vw-eval-termp (cadddr (add-K-tag-to-Ab-help inductor0 inductor1))))
  :hints
  (("Goal" :in-theory (e/d (occurrencep)
                           (no-duplicatesp-equal member-equal)))))

(in-theory (disable add-K-tag-to-Ab-help))

(defun add-K-tag-to-Ab (x-names occ occs sim-type  Abr)
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrencep occ)
                              (occurrencesp occs)
                              (symbolp sim-type))
                  :stobjs Abr
                  :guard-hints
                  (("Goal" :do-not-induct t
                    :in-theory
                    (disable no-duplicatesp-equal member-equal nth)))))
  (case-match occ
    ((& 'k (inductor0-name inductor1-name)
        ;; Coupling factor; typically 10% to 60%
        (coupling-factor))
     (b* ((ctx 'add-K-tag-to-Ab)
          (inductor0 (assoc inductor0-name occs))
          (inductor1 (assoc inductor1-name occs))
          ;; can this check be proved away???
          ((unless (and (occurrencep inductor0)
                        (occurrencep inductor1)
                        (equal (cadr inductor0) 'l)
                        (equal (cadr inductor1) 'l)))
           (prog2$ (er hard? ctx
                       "Ill-formed mutual inductance. The specified ~
                        inductors do not exist in the netlist: ~p0.~%" occ)
                   Abr))
          (br-inductance (add-K-tag-to-Ab-help inductor0 inductor1))
          (br0 (car br-inductance))
          (br1 (cadr br-inductance))
          (inductance0 (caddr br-inductance))
          (inductance1 (cadddr br-inductance))

          ;; can this check also be proved away???
          ((unless (and (vw-eval-termp br1)
                        (vw-eval-termp br0)))
           Abr)

          ((unless (and (member-eq br0 x-names)
                        (member-eq br1 x-names)))
           (prog2$ (er hard? ctx
                       "Invalid branch/node name: ~p0.~%" occ)
                   Abr))

          (br0-index  (pos br0  x-names))
          (br1-index  (pos br1  x-names))

          ; mutual coupling
          (M `(f* ,coupling-factor (f-sqrt (f* ,inductance0 ,inductance1))))

          (trips (triples br0-index br1-index sim-type M))
          (Abr (sum-expr-into-A-sym-lst trips Abr))

          (Abr (if (eq sim-type 'voltage)
                   (b* ((Abr (sum-expr-into-b-sym
                              br0-index
                              `(f0- (f* (f/ (f* '2 ,M) $hn$) ,br1))
                              Abr))
                        (Abr (sum-expr-into-b-sym
                              br1-index
                              `(f0- (f* (f/ (f* '2 ,M) $hn$) ,br0))
                              Abr)))
                     Abr)
                 Abr))
          )
       Abr))
    (& (prog2$ (er hard? 'add-K-tag-to-Ab
                       "add-K-tag-to-Ab:  Unexpected exit!~%")
               Abr))))

(defthm Abrp-add-K-tag-to-Ab
  (implies (and (Abrp Abr)
                (occurrencep occ)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr)))
           (Abrp (add-K-tag-to-Ab x-names occ occs sim-type
                                  Abr)))
  :hints
  (("Goal" :in-theory (disable Abrp member-equal no-duplicatesp-equal))))

(defthm add-K-tag-to-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (add-K-tag-to-Ab x-names occ occs sim-type
                                              Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (add-K-tag-to-Ab x-names occ occs sim-type
                                                   Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (add-K-tag-to-Ab x-names occ occs sim-type
                                                          Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (add-K-tag-to-Ab x-names occ occs sim-type
                                              Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (add-K-tag-to-Ab x-names occ occs sim-type
                                                   Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (add-K-tag-to-Ab x-names occ occs sim-type
                                                          Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (add-K-tag-to-Ab x-names occ occs sim-type
                                              Abr))
               (A-num-length Abr))))
  :hints
  (("Goal" :in-theory (disable member-equal no-duplicatesp-equal))))

(in-theory (disable add-K-tag-to-Ab))

(defun add-component-to-Ab
    (x-names     ; The x vector; this list has our node and branch names
     occ         ; Occurrence (component) to "stamp" into matrices A and b
     occs        ; Original list of occurrences
     sim-type    ; Simulation type:  voltage or phase
     Abr         ; The A matrix and be vector
     )
  "Add a component, and its associated stamps, to the A and b matrices."
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrencep occ)
                              (occurrencesp occs)
                              (symbolp sim-type))
                  :stobjs Abr))
  (declare (ignorable x-names sim-type))
  (case-match occ
    ((& 'v . &)
     (add-voltage-source-tag-to-Ab x-names occ sim-type Abr))

    ((& 'i . &)
     (add-current-source-tag-to-Ab x-names occ sim-type Abr))

    ((& 'p . &)
     (add-phase-source-tag-to-Ab x-names occ sim-type Abr))

    ((& 'r . &)
     (add-resistor-tag-to-Ab x-names occ sim-type  Abr))

    ((& 'c . &)
     (add-capacitor-tag-to-Ab x-names occ sim-type  Abr))

    ((& 'l . &)
     (add-inductor-tag-to-Ab x-names occ sim-type  Abr))

    ((& 'b . &)
     (add-B-tag-to-Ab x-names occ sim-type  Abr))

    ((& 't . &)
     (add-T-tag-to-Ab x-names occ sim-type  Abr))

    ((& 'k . &)
     (add-K-tag-to-Ab x-names occ occs sim-type  Abr))

    (&
     (prog2$ (cw "add-component-to-Ab:  Unrecognized component!~%")
            Abr))
    ))

(defthm Abrp-add-component-to-Ab
  (implies (and (Abrp Abr)
                (occurrencep occ)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr)))
           (Abrp (add-component-to-Ab x-names occ occs sim-type
                                      Abr)))
  :hints
  (("Goal" :in-theory (disable Abrp member-equal no-duplicatesp-equal))))

(defthm add-component-to-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (add-component-to-Ab x-names occ occs sim-type Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (add-component-to-Ab x-names occ occs sim-type Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (add-component-to-Ab x-names occ occs sim-type Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (add-component-to-Ab x-names occ occs sim-type Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (add-component-to-Ab x-names occ occs sim-type Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (add-component-to-Ab x-names occ occs sim-type Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (add-component-to-Ab x-names occ occs sim-type Abr))
               (A-num-length Abr)))))

(in-theory (disable add-component-to-Ab))

(defun create-symbolic-Ab (x-names occs orig-occs sim-type Abr)
  ;; Creates the symbolic A and b matrices, which are stored in the
  ;; Abr STOBJ.
  (declare (xargs :guard (and (syml-listp x-names)
                              (< (len x-names) *2^60*)
                              (= (len x-names) (b-sym-length Abr))
                              (= (len x-names) (A-sym-length Abr))
                              (occurrence-listp occs)
                              (occurrencesp orig-occs)
                              (symbolp sim-type))
                  :stobjs Abr
                  :guard-hints
                  (("Goal" :in-theory (e/d (occurrence-listp)
                                           (member-equal no-duplicatesp-equal
                                                         occurrencep))))
                  ))
  (if (atom occs)
      Abr
    (b* ((Abr
          (add-component-to-Ab x-names (car occs) orig-occs sim-type
                               Abr)))
      (create-symbolic-Ab x-names (cdr occs) orig-occs sim-type
                          Abr))))

(defthm Abrp-create-symbolic-Ab
  (implies (and (Abrp Abr)
                (occurrence-listp occs)
                (equal (len x-names) (b-sym-length Abr))
                (equal (len x-names) (A-sym-length Abr)))
           (Abrp (create-symbolic-Ab
                  x-names occs orig-occs sim-type
                   Abr)))
  :hints
  (("Goal" :in-theory (e/d (occurrence-listp)
                           (Abrp occurrencep member-equal
                                 no-duplicatesp-equal)))))

(defthm create-symbolic-Ab-lengths-unchanged
  (implies
   (and (equal (len x-names) (b-sym-length Abr))
        (equal (len x-names) (A-sym-length Abr)))
   (and (equal (b-sym-length (create-symbolic-Ab x-names occs orig-occs sim-type
                                                 Abr))
               (b-sym-length Abr))
        (equal (b-sym-fold-length (create-symbolic-Ab x-names occs orig-occs sim-type
                                                      Abr))
               (b-sym-fold-length Abr))
        (equal (b-sym-fold-to-stv-length (create-symbolic-Ab x-names occs orig-occs sim-type
                                                             Abr))
               (b-sym-fold-to-stv-length Abr))
        (equal (A-sym-length (create-symbolic-Ab x-names occs orig-occs sim-type
                                                 Abr))
               (A-sym-length Abr))
        (equal (A-sym-fold-length (create-symbolic-Ab x-names occs orig-occs sim-type
                                                      Abr))
               (A-sym-fold-length Abr))
        (equal (A-sym-fold-to-stv-length (create-symbolic-Ab x-names occs orig-occs sim-type
                                                             Abr))
               (A-sym-fold-to-stv-length Abr))
        (equal (A-num-length (create-symbolic-Ab x-names occs orig-occs sim-type
                                                 Abr))
               (A-num-length Abr))))
  :hints
  (("Goal" :induct t :in-theory (disable occurrencep))))

(in-theory (disable create-symbolic-Ab))

(defthm more-help-with-hons-assoc-equal-on-symbol-rational-list-alistp
  (implies (and (symbol-rational-list-alistp r)
                (alist-entry-consp r)
                (not (consp (cddr (hons-assoc-equal name r)))))
           (not (cddr (hons-assoc-equal name r)))))

(defun-inline xp-deriv (Vn Vn-1 dpn-1 hn)
  (declare (xargs :guard (and (rationalp Vn)
                              (rationalp Vn-1)
                              (rationalp dpn-1)
                              (rationalp hn)
                              (< 0 hn))))
  (let* ((V-diff (f- Vn Vn-1))
         (V-diff*2 (f+ V-diff V-diff)))
    (f- (f/ V-diff*2 hn)
        dpn-1)))

(defthm rationalp-xp-deriv
  (implies (and (rationalp Vn)
                (rationalp Vn-1)
                (rationalp dpn-1)
                (rationalp hn))
           (rationalp (xp-deriv Vn Vn-1 dpn-1 hn))))

(in-theory (disable xp-deriv))

(defun xp-updates (r x-names dp-x-names hn)
  "This function updates the derivative records.  Note, this function
   assumes that the records at the current time (Tn) have already been
   updated for the node and branch values while the most recent values
   for the derivative names (xp-names) have not yet been updated with
   time Tn values.  We only update the derivatives identified in list
   X-NAMES, which must be correspondence with DP-X-NAMES."
  (declare (xargs :guard (and (symbol-rational-list-alistp r)
                              (alist-entry-consp r)
                              (syml-listp x-names)
                              (symbol-listp x-names)
                              (symbol-listp dp-x-names)
                              (all-hons-assoc-cddr x-names r)
                              (all-hons-assoc-equal dp-x-names r)
                              (= (len x-names)
                                 (len dp-x-names))
                              (rationalp hn)
                              (< 0 hn))
                  :verify-guards nil))
  (if (atom x-names)
      r
    (b* ((r1 (xp-updates r (cdr x-names) (cdr dp-x-names) hn))
         (name (car x-names))
         (name-record (hons-get name r1))
         (x-list (cdr name-record))

         (Vn   (car x-list))
         (rest (cdr x-list))
         (Vn-1 (car rest))

         ;; DP records are one shorter than the records above
         (dp-x-name (car dp-x-names))
         (dp-x-name-record (hons-get dp-x-name r1))

         (dpn-1-list (cdr dp-x-name-record))
         (dpn-1 (car dpn-1-list))

         ;; Calculate the derivatives
         (dpn      (xp-deriv Vn Vn-1 dpn-1 hn))
         (extended-record (cons dpn dpn-1-list)))
      (hons-acons dp-x-name extended-record r1))))

(defthm hons-assoc-equal-xp-updates
  (implies (hons-assoc-equal x r)
           (hons-assoc-equal x (xp-updates r x-names dp-x-names hn))))

(defthm all-hons-assoc-equal-xp-updates
  (implies (all-hons-assoc-equal xs r)
           (all-hons-assoc-equal xs (xp-updates r x-names dp-x-names hn))))

(defthm hons-assoc-equal-cddr-xp-updates
  (implies (cddr (hons-assoc-equal x r))
           (and (hons-assoc-equal x (xp-updates r x-names dp-x-names hn))
                (cddr (hons-assoc-equal x (xp-updates r x-names dp-x-names hn))))))

(defthm all-hons-assoc-cddr-xp-updates
  (implies (all-hons-assoc-cddr xs r)
           (all-hons-assoc-cddr xs (xp-updates r x-names dp-x-names hn))))

(defthm alist-entry-consp-xp-updates
  (implies (alist-entry-consp r)
           (alist-entry-consp (xp-updates r x-names dp-x-names hn))))

(defthm symbol-rational-list-alistp-xp-updates
  (implies (and (symbol-listp dp-x-names)
                (symbol-rational-list-alistp r)
                (alist-entry-consp r)
                (all-hons-assoc-equal dp-x-names r)
                (all-hons-assoc-cddr x-names r)
                (= (len x-names)
                   (len dp-x-names))
                (rationalp hn))
           (symbol-rational-list-alistp (xp-updates r x-names dp-x-names hn))))

(encapsulate
  ()

  (local
   (defthm help-with-hons-assoc-equal-on-symbol-rational-list-alistp
     (implies (and (symbol-rational-list-alistp r)
                   (not (consp (cdr (hons-assoc-equal name r)))))
              (not (cdr (hons-assoc-equal name r))))))

  (local
   (defthm more-more-help-with-hons-assoc-equal-on-symbol-rational-list-alistp
     (implies (and (symbol-rational-list-alistp r)
                   (cddr (hons-assoc-equal name r)))
              (consp (cddr (hons-assoc-equal name r))))))
  (verify-guards xp-updates))

(in-theory (disable xp-updates))

; the new array-based approach using the ST-VALS STOBJ starts here.

(defun sra-nat-rowp-cdr-in-bounds (row max)
  (declare (xargs :guard (and (sra-nat-rowp row)
                              (natp max))))
  (if (atom row)
      t
    (let* ((pair (car row))
           (val  (cdr pair)))
      (and (< val max)
           (sra-nat-rowp-cdr-in-bounds (cdr row) max)))))

(defun sra-rows-columns-samep (r1 r2)
  (declare (xargs :guard (and (sra-rowp r1)
                              (sra-rowp r2))))
  (if (atom r1)
      (atom r2)
    (if (atom r2)
        nil
      (let* ((r1-pair (car r1))
             (r2-pair (car r2)))
        (and (= (car r1-pair)
                (car r2-pair))
             (sra-rows-columns-samep (cdr r1)
                                     (cdr r2)))))))

(defun A-sym-fold-to-stv-good-map-help (i n Abr max)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n)
                              (= n (A-sym-fold-to-stv-length Abr))
                              (natp max))
                  :stobjs Abr))
  (if (zp (- n i))
      t
    (let ((row (A-sym-fold-to-stvi i Abr)))
      (and (sra-nat-rowp-cdr-in-bounds row max)
           (A-sym-fold-to-stv-good-map-help (1+ i) n Abr max)))))

(defun A-sym-fold-to-stv-good-map (Abr max)
  (declare (xargs :guard (natp max)
                  :stobjs Abr))
  (A-sym-fold-to-stv-good-map-help 0 (A-sym-fold-to-stv-length Abr)
                                   Abr
                                   max))

(defun all-A-fields-in-Abr-columns-samep-help (i n Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n)
                              (= n (A-sym-length Abr))
                              (= n (A-sym-fold-length Abr))
                              (= n (A-sym-fold-to-stv-length Abr))
                              (= n (A-num-length Abr)))
                  :stobjs Abr))
  (if (zp (- n i))
      t
    (let ((A-sym-row             (A-symi i Abr))
          (A-sym-fold-row        (A-sym-foldi i Abr))
          (A-sym-fold-to-stv-row (A-sym-fold-to-stvi i Abr))
          (A-num-row             (A-numi i Abr)))
      (and (sra-rows-columns-samep A-sym-row A-sym-fold-row)
           (sra-rows-columns-samep A-sym-row A-sym-fold-to-stv-row)
           (sra-rows-columns-samep A-sym-row A-num-row)
           (all-A-fields-in-Abr-columns-samep-help (1+ i) n Abr)))))

#||
(defthm generalize-to-any-index-all-A-fields-in-Abr-columns-samep-help
  (implies (and (natp i)
                (natp n)
                (natp j)
                (<= i j)
                (< j n)
                (all-A-fields-in-Abr-columns-samep-help i n Abr))
           (and (sra-rows-columns-samep (a-symi j abr) (A-sym-foldi j Abr))
                (sra-rows-columns-samep (a-symi j abr) (A-sym-fold-to-stvi j Abr))
                (sra-rows-columns-samep (a-symi j abr)
                                        (a-numi j abr)))))
||#

(defun all-A-fields-in-Abr-columns-samep (Abr)
  (declare (xargs :guard (and (= (A-sym-length Abr)
                                 (A-sym-fold-length Abr))
                              (= (A-sym-length Abr)
                                 (A-sym-fold-to-stv-length Abr))
                              (= (A-sym-length Abr)
                                 (A-num-length Abr)))
                  :stobjs Abr))
  (all-A-fields-in-Abr-columns-samep-help 0 (A-sym-length Abr) Abr))

#||
(defthm any-index-all-A-fields-in-Abr-columns-samep
  (implies (and (natp j)
                (< j (A-sym-length Abr))
                (all-A-fields-in-Abr-columns-samep Abr))
           (and (sra-rows-columns-samep (a-symi j abr) (A-sym-foldi j Abr))
                (sra-rows-columns-samep (a-symi j abr) (A-sym-fold-to-stvi j Abr))
                (sra-rows-columns-samep (a-symi j abr)
                                        (a-numi j abr))))
  :hints
  (("Goal" :use ((:instance
                  generalize-to-any-index-all-A-fields-in-Abr-columns-samep-help
                  (i 0) (n (A-sym-length Abr)))))))
||#

(in-theory (disable all-A-fields-in-Abr-columns-samep))

(defun A-num-row-changedp (stv-indices-row A-num-row
                                           st-vals)
  ;; stv-indices-row: a sparse row of (column . stv-index) pairs
  ;; A-num-row:       a sparse row of (column . rational)  pairs
  ;; stv-indices-row and A-num-row have the same column indices.
  ;; Abr:             STOBJ
  ;; st-vals:         STOBJ that holds STV array
  (declare (xargs :guard (and (sra-nat-rowp stv-indices-row)
                              (sra-rational-rowp A-num-row)
                              (sra-rows-columns-samep stv-indices-row
                                                      A-num-row)
                              (sra-nat-rowp-cdr-in-bounds stv-indices-row
                                                          (stvl st-vals)))
                  :guard-hints (("Goal" :in-theory
                                 (enable stv-theory-lemmas
                                         sra-rational-rowp
                                         )))
                  :stobjs (st-vals)
                  ))
  (if (atom stv-indices-row)
      nil
    (b* ((A-num-row-entry (car A-num-row))
         (A-num-value     (cdr A-num-row-entry))

         (stv-indices-row-entry (car stv-indices-row))
         (stv-index         (cdr stv-indices-row-entry))

         (new-A-num-value  (stvi stv-index st-vals)))
      (if (not (= A-num-value new-A-num-value))
          t
        (A-num-row-changedp (cdr stv-indices-row)
                            (cdr A-num-row)
                            st-vals)))))

(in-theory (disable A-num-row-changedp))

(defun st-vals-to-A-num-row (stv-indices-row st-vals)
  ;; stv-indices-row: a sparse row of (column . stv-index) pairs
  ;; A-num-row:       a sparse row of (column . rational)  pairs
  ;; Abr:             STOBJ
  ;; st-vals:         STOBJ that holds STV array
  (declare (xargs :guard (and (sra-nat-rowp stv-indices-row)
                              (sra-nat-rowp-cdr-in-bounds stv-indices-row
                                                          (stvl st-vals)))
                  :guard-hints (("Goal" :in-theory
                                 (enable stv-theory-lemmas)))
                  :stobjs (st-vals)))
  (if (atom stv-indices-row)
      nil
    (b* ((stv-indices-row-entry (car stv-indices-row))
         (A-col-index       (car stv-indices-row-entry))
         (stv-index         (cdr stv-indices-row-entry))
         (new-A-num-value  (stvi stv-index st-vals)))
      (cons (cons A-col-index new-A-num-value)
            (st-vals-to-A-num-row (cdr stv-indices-row)
                                  st-vals)))))

(defthm sra-rowp-st-vals-to-A-num-row
  (implies (sra-rowp stv-indices-row)
           (sra-rowp (st-vals-to-A-num-row stv-indices-row st-vals))))

(defthm sra-rational-rowp-st-vals-to-A-num-row
  (implies (and (st-valsp st-vals)
                (sra-nat-rowp stv-indices-row)
                (sra-nat-rowp-cdr-in-bounds stv-indices-row
                                            (stvl st-vals)))
           (sra-rational-rowp (st-vals-to-A-num-row stv-indices-row st-vals)))
  :hints
  (("Goal" :in-theory (enable sra-rational-rowp))))

(defthm sra-rows-columns-samep-st-vals-to-A-num-row
  (sra-rows-columns-samep
   stv-indices-row
   (st-vals-to-A-num-row stv-indices-row st-vals)))

(in-theory (disable sra-rows-columns-samep st-vals-to-A-num-row))

(defun all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi (i n Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n)
                              (= n (A-sym-fold-to-stv-length Abr))
                              (= n (A-num-length Abr)))
                  :stobjs Abr))
  (if (zp (- n i))
      t
    (let ((A-sym-fold-to-stv-row (A-sym-fold-to-stvi i Abr))
          (A-num-row             (A-numi i Abr)))
      (and (sra-rows-columns-samep A-sym-fold-to-stv-row A-num-row)
           (all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi (1+ i) n Abr)))))

(defthm A-sym-fold-to-stvi-unchanged-by-!A-numi
  (equal (A-sym-fold-to-stvi i (!A-numi j v Abr))
         (A-sym-fold-to-stvi i Abr))
  :hints
  (("Goal" :in-theory (enable A-sym-fold-to-stvi
                              !A-numi
                              nth-theory-lemmas))))

(defthm A-numi-!A-numi
    ;; Similar to NTH-!NTH lemma
    (equal (A-numi m (!A-numi n val Abr))
           (if (equal (nfix m) (nfix n))
               val
             (A-numi m Abr)))
    :hints
    (("Goal" :in-theory (enable A-numi !A-numi nth-theory-lemmas))))

(defun stv-vals-to-A-num (i n LU-redo-p Abr st-vals)
  ;; Store the result of evaluating the sparse symbolic A matrix in
  ;; A-num. If any item in A-num is changed, we set the LU-redo-p
  ;; flag.
  (declare (xargs :measure (nfix (- n i))
                  :guard   (and (natp i)
                                (natp n)
                                (<= i n)
                                (= n (A-sym-fold-to-stv-length Abr))
                                (= n (A-num-length Abr))
                                (all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi
                                 i n Abr)
                                (a-sym-fold-to-stv-good-map-help
                                 i n Abr (stvl st-vals)))
                  :verify-guards nil
                  :stobjs (Abr st-vals)))
  (if (zp (- n i))
      (mv Abr LU-redo-p)
    (b* ((stv-indices-row (A-sym-fold-to-stvi i Abr))
         (A-num-row (A-numi i Abr)) ;; an alist with increasing indices
         ;; we check if any of the entries in the ith row of A-num
         ;; change given the new evaluation results in st-vals. We do
         ;; this to avoid unnecessary CONSing, which would be needed
         ;; to rebuild the A-num row if it did not change.
         (A-num-row-changed (A-num-row-changedp
                             stv-indices-row
                             A-num-row
                             st-vals)))
      (if A-num-row-changed
          (b* ((Abr
                 (!A-numi
                  i
                  (st-vals-to-A-num-row stv-indices-row st-vals)
                  Abr)))
            (stv-vals-to-A-num (1+ i) n t Abr st-vals))
        (stv-vals-to-A-num (1+ i) n LU-redo-p Abr st-vals)))))

(defthm stv-vals-to-A-num-Abr-lengths
  (and (equal (A-sym-fold-to-stv-length
               (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))
              (A-sym-fold-to-stv-length Abr))
       (equal (A-sym-fold-length (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))
              (A-sym-fold-length Abr))
       (equal (A-sym-length (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))
              (A-sym-length Abr))
       (equal (b-sym-length (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))
              (b-sym-length Abr))
       (equal (b-sym-fold-length (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-length (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))
              (b-sym-fold-length Abr))
       (equal (b-sym-fold-to-stv-length (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))
              (b-sym-fold-to-stv-length Abr))))

(defthm stv-vals-to-A-num-A-num-length
  (implies (and (natp i)
                (= n (A-sym-fold-to-stv-length Abr))
                (= n (A-num-length Abr)))
           (equal (A-num-length (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))
                  (A-num-length Abr))))

(defthm all-sra-rows-columns-samep-a-sym-fold-to-stvi-a-numi/update-below
  (implies (and (all-sra-rows-columns-samep-a-sym-fold-to-stvi-a-numi n len abr)
                (<= 0 i)
                (natp n)
                (< i n))
           (all-sra-rows-columns-samep-a-sym-fold-to-stvi-a-numi
            n
            len
            (!a-numi i who-cares abr))))

(defthm a-sym-fold-to-stv-good-map-help/update-below
  (implies
   (and
    (a-sym-fold-to-stv-good-map-help n len1 abr len2)
    (integerp n)
    (natp i)
    (< i n))
   (a-sym-fold-to-stv-good-map-help n
                                    len1
                                    (!a-numi i who-cares abr)
                                    len2)))

(verify-guards stv-vals-to-a-num
; Force us to prove a suitable lemma, even though this proof has gone through
; using two levels of induction.  Note that the :hints and :otf-flg no longer
; have any effect, given the lemmas above.
  :hints (("Goal" :do-not-induct t))
  :otf-flg t)

(defthm a-num-length-stv-vals-to-a-num
  ;; The number of rows in STOBJ field A-NUM remains the same after
  ;; calling STV-VALS-TO-A-NUM
  (implies (and (natp i)
                (= n (A-sym-fold-to-stv-length Abr))
                (= n (A-num-length Abr)))
           (equal (A-num-length (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))
                  (A-num-length Abr))))

(defthm A-sym-fold-to-stv-length-stv-vals-to-a-num
  ;; The number of rows in STOBJ field A-SYM-FOLD-TO-STV remains the
  ;; same after calling STV-VALS-TO-A-NUM
  (implies (and (natp i)
                (= n (A-sym-fold-to-stv-length Abr))
                (= n (A-num-length Abr)))
           (equal (a-sym-fold-to-stv-length (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))
                  (a-sym-fold-to-stv-length Abr))))

(defthm all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi-stv-vals-to-A-num-general-lemma-lemma

; This proves by induction, thanks to separating abr1 and abr2.  But it's not a
; good rewrite rule, because abr2 is a free variable in the hypotheses.

  (implies
   (and (natp i)
        (natp n)
        (<= i n)
        (natp j)
        (<= j n)
        (= n (A-sym-fold-to-stv-length Abr))
        (= n (A-num-length Abr))
        (equal (a-sym-fold-to-stvi i abr1)
               (a-sym-fold-to-stvi i abr2)))
   (equal (a-sym-fold-to-stvi i
                              (car (stv-vals-to-a-num j (a-num-length abr)
                                                      lu-redo-p abr1 st-vals)))
          (a-sym-fold-to-stvi i abr2)))
  :rule-classes nil)

(defthm all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi-stv-vals-to-A-num-general-lemma
  (implies
   (and (natp i)
        (<= i (A-num-length Abr))
        (natp j)
        (<= j (A-num-length Abr))
        (equal (A-sym-fold-to-stv-length Abr)
               (A-num-length Abr)))
   (equal (a-sym-fold-to-stvi i
                              (car (stv-vals-to-a-num j (a-num-length abr)
                                                      lu-redo-p abr st-vals)))
          (a-sym-fold-to-stvi i abr)))
  :hints (("Goal"
           :use
           ((:instance
             all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi-stv-vals-to-A-num-general-lemma-lemma
             (abr1 abr)
             (abr2 abr)
             (n (A-num-length Abr)))))))

; Start proof of a-sym-fold-to-stv-good-map-help-stv-vals-to-A-num.

(defthm length-a-numi-better
  (implies (force (and (natp i) (< i (a-num-length abr))))
           (equal (a-num-length (!a-numi i row abr))
                  (a-num-length abr)))
  :hints (("goal" :in-theory (enable nth-theory-lemmas))))

; This suffices for the next.
(defthm stv-vals-to-a-num-preserves-sra-rows-columns-samep-lemma
  (implies
   (and
    (natp i)
    (<= 0 (a-num-length abr))
    (< i (a-num-length abr))
    (natp j)
    (<= j (a-num-length abr))
    (equal (a-sym-fold-to-stv-length abr)
           (a-num-length abr))
    (sra-rows-columns-samep (a-sym-fold-to-stvi i abr)
                            (a-numi i abr))
    (equal len (a-num-length abr)))
   (sra-rows-columns-samep
    (a-sym-fold-to-stvi i abr)
    (a-numi i
            (car (stv-vals-to-a-num j len
                                    lu-redo-p abr st-vals))))))

; This suffices for the next.
(defthm stv-vals-to-a-num-preserves-sra-rows-columns-samep
  (implies
   (and
    (natp i)
    (<= 0 (a-num-length abr))
    (< i (a-num-length abr))
    (natp j)
    (<= j (a-num-length abr))
    (equal (a-sym-fold-to-stv-length abr)
           (a-num-length abr))
    (all-sra-rows-columns-samep-a-sym-fold-to-stvi-a-numi i (a-num-length abr)
                                                          abr))
   (sra-rows-columns-samep
    (a-sym-fold-to-stvi i abr)
    (a-numi i
            (car (stv-vals-to-a-num j (a-num-length abr)
                                    lu-redo-p abr st-vals))))))

(defthm all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi-stv-vals-to-A-num-general
  ;; For each row in STOBJ fields A-NUM and A-SYM-FOLD-TO-STV, the
  ;; column indices remain the same after calling STV-VALS-TO-A-NUM
  (implies (and (natp i)
                (natp n)
                (<= i n)
                (natp j)
                (<= j n)
                (= n (A-sym-fold-to-stv-length Abr))
                (= n (A-num-length Abr))
                (all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi
                 i n Abr))
           (all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi
            i n (car (stv-vals-to-A-num j n LU-redo-p Abr st-vals)))))

(defthm all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi-stv-vals-to-A-num
  ;; For each row in STOBJ fields A-NUM and A-SYM-FOLD-TO-STV, the
  ;; column indices remain the same after calling STV-VALS-TO-A-NUM
  (implies (and (natp i)
                (natp n)
                (<= i n)
                (= n (A-sym-fold-to-stv-length Abr))
                (= n (A-num-length Abr))
                (all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi
                 i n Abr))
           (all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi
            i n (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals)))))

; Start proof of a-sym-fold-to-stv-good-map-help-stv-vals-to-A-num.

(defthm a-sym-fold-to-stv-good-map-help-stv-vals-to-A-num-general
   (implies (and (natp i)
                 (natp n)
                 (<= i n)
                 (natp j)
                 (<= j n)
                 (= n (A-sym-fold-to-stv-length Abr))
                 (= n (A-num-length Abr))
                 (a-sym-fold-to-stv-good-map-help
                  i n Abr stvl))
            (a-sym-fold-to-stv-good-map-help
             i n (car (stv-vals-to-A-num j n LU-redo-p Abr st-vals))
             stvl)))

(defthm a-sym-fold-to-stv-good-map-help-stv-vals-to-A-num
  (implies (and (natp i)
                (natp n)
                (<= i n)
                (= n (A-sym-fold-to-stv-length Abr))
                (= n (A-num-length Abr))
                (a-sym-fold-to-stv-good-map-help
                 i n Abr (stvl st-vals)))
           (a-sym-fold-to-stv-good-map-help
            i n (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals))
            (stvl st-vals))))

(defun vw-eval-fold-b-sym (i n a Abr)
  ;; Folds constants in each entry of b-sym and stores the folded
  ;; entries in b-sym-fold.
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (symbol-rational-list-alistp a)
                              (alist-entry-consp a)
                              (= n (b-sym-length Abr))
                              (= n (b-sym-fold-length Abr))
                              (<= i n))
                  :stobjs Abr))
  (if (zp (- n i))
      Abr
    (let* ((new-term (vw-eval-fold (b-symi i Abr) a))
           (Abr (!b-sym-foldi i new-term Abr)))
      (vw-eval-fold-b-sym (1+ i) n a Abr))))

(defun vw-eval-fold-A-sym (i n a Abr)
  ;; Folds constants in each entry of A-sym and stores the result in
  ;; A-sym-fold.
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (symbol-rational-list-alistp a)
                              (alist-entry-consp a)
                              (= n (A-sym-length Abr))
                              (= n (A-sym-fold-length Abr))
                              (<= i n))
                  :stobjs Abr))
  (if (zp (- n i))
      Abr
    (let* ((new-row (sra-vw-eval-fold-row (A-symi i Abr) a))
           (Abr (!A-sym-foldi i new-row Abr)))
      (vw-eval-fold-A-sym (1+ i) n a Abr))))

(defun remove-assoc-items (items alst)
  (declare (xargs :guard (and (symbol-listp items)
                              (symbol-alistp alst))))
  (if (atom alst)
      nil
    (let ((name (caar alst)))
      (if (member name items)
          (remove-assoc-items items (cdr alst))
        (cons (car alst)
              (remove-assoc-items items (cdr alst)))))))

(defun cdr-true-list-alistp (l)
  (declare (xargs :guard t))
  (if (atom l)
      t
    (let ((entry (car l)))
      (and (consp entry)
           (true-listp (cdr entry))
           (cdr-true-list-alistp (cdr l))))))

(defun reverse-records (l acc)
  (declare (xargs :guard (and (cdr-true-list-alistp l)
                              (true-listp acc))))
  (if (atom l)
      (reverse acc)
    (b* ((entry (car l))
         (var   (car entry))
         (rev-rest (reverse (cdr entry)))
         (new-list (cons var rev-rest)))
      (reverse-records (cdr l)
                       (cons new-list acc)))))

(defun sra-row-remove-last-col (row dim-Abr-1)
  (declare (xargs :guard (and (natp dim-Abr-1)
                              (sra-rowp row))))
  (if (atom row)
      nil
    ;; assuming row is sorted from smallest to largest indices
    (let* ((pair (car row))
           (col (car pair))
           (val (cdr pair)))
      ;; remove the dim-Abr-1 column, if it exists.
      (if (= col dim-Abr-1)
          (sra-row-remove-last-col (cdr row) dim-Abr-1)
      (cons (cons col val)
            (sra-row-remove-last-col (cdr row) dim-Abr-1))))))

(encapsulate
  ()
  (local
   (defthm sra-row-remove-last-col-maintains-order
    (implies (and (sra-rowp row)
                  (consp (sra-row-remove-last-col (cdr row) a)))
             (< (car (car row))
                (car (car (sra-row-remove-last-col (cdr row) a)))))))

  (defthm sra-rowp-sra-row-remove-last-col
    (implies (sra-rowp row)
             (sra-rowp (sra-row-remove-last-col row dim-Abr-1)))))

(defthm sra-rational-rowp-sra-row-remove-last-col
  (implies (sra-rational-rowp row)
           (sra-rational-rowp (sra-row-remove-last-col row dim-Abr-1)))
  :hints
  (("Goal" :in-theory (enable sra-rational-rowp))))

(defthm sra-term-rowp-sra-row-remove-last-col
  (implies (sra-term-rowp row)
           (sra-term-rowp (sra-row-remove-last-col row dim-Abr-1)))
  :hints
  (("Goal" :in-theory (enable sra-term-rowp))))

(defun remove-last-col-A-num (i n Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (= n (A-num-length Abr))
                              (<= i n))
                  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      Abr
    (let* ((row (A-numi i Abr))
           ;; we assume that the last row of ``A-num'' has been
           ;; removed and ``n'' is the new A-num-length.
           (new-row (sra-row-remove-last-col row n))
           (Abr (!A-numi i new-row Abr)))
      (remove-last-col-A-num (1+ i) n Abr))))

(defun remove-last-col-A-sym (i n Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (= n (A-sym-length Abr))
                              (<= i n))
                  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      Abr
    (let* ((row (A-symi i Abr))
           (new-row (sra-row-remove-last-col row n))
           (Abr (!A-symi i new-row Abr)))
      (remove-last-col-A-sym (1+ i) n Abr))))

(defthm A-sym-length-remove-last-col-A-sym
  (implies (and (natp i)
                ;; (natp n) ;; <- this hypothesis prevents proving the
                ;; theorem. Specifically, (integerp n)
                (<= n (A-sym-length Abr)))
           (equal (A-sym-length (remove-last-col-A-sym i n Abr))
                  (A-sym-length Abr))))

(defthm A-num-length-remove-last-col-A-sym
  (equal (A-num-length (remove-last-col-A-sym i n Abr))
         (A-num-length Abr)))

;; Helper functions for preparing matrices for floating-point mode.

(defun r2f-sra-rational-row (r)
  (declare (xargs :guard (sra-rational-rowp r)
                  :guard-hints
                  (("Goal" :in-theory (enable sra-rational-rowp)))))
  (if (atom r)
      nil
    (let* ((pair (car r))
           (key (car pair))
           (val (cdr pair)))
      (cons (cons key (r2f val))
            (r2f-sra-rational-row (cdr r))))))

(defthm sra-rowp-r2f-sra-rational-row
  (implies (sra-rowp r)
           (sra-rowp (r2f-sra-rational-row r))))

(defthm sra-rational-rowp-r2f-sra-rational-row
  (implies (sra-rational-rowp r)
           (sra-rational-rowp (r2f-sra-rational-row r)))
  :hints
  (("Goal" :in-theory (enable sra-rational-rowp))))

(defun r2f-sra-term-row (r)
  (declare (xargs :guard (sra-term-rowp r)
                  :guard-hints
                  (("Goal" :in-theory (enable sra-term-rowp)))))
  (if (atom r)
      nil
    (let* ((pair (car r))
           (key (car pair))
           (val (cdr pair)))
      (cons (cons key (r2f-term val))
            (r2f-sra-term-row (cdr r))))))

(defthm sra-rowp-r2f-sra-row
  (implies (sra-rowp r)
           (sra-rowp (r2f-sra-term-row r))))

(defthm sra-term-rowp-r2f-sra-row
  (implies (sra-term-rowp r)
           (sra-term-rowp (r2f-sra-term-row r)))
  :hints
  (("Goal" :in-theory (enable sra-term-rowp))))

(defun r2f-b-sym-fold (i n Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (= n (b-sym-fold-length Abr))
                              (<= i n))
                  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      Abr
    (let* ((r2f-val (r2f-term (b-sym-foldi i Abr)))
           (Abr (!b-sym-foldi i r2f-val Abr)))
      (r2f-b-sym-fold (1+ i) n Abr))))

(defun r2f-A-num (i n Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (= n (A-num-length Abr))
                              (<= i n))
                  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      Abr
    (let* ((row (A-numi i Abr))
           (r2f-row (r2f-sra-rational-row row))
           (Abr (!A-numi i r2f-row Abr)))
      (r2f-A-num (1+ i) n Abr))))

(defun r2f-A-sym-fold (i n Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (= n (A-sym-fold-length Abr))
                              (<= i n))
                  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      Abr
    (let* ((row (A-sym-foldi i Abr))
           (r2f-row (r2f-sra-term-row row))
           (Abr (!A-sym-foldi i r2f-row Abr)))
      (r2f-A-sym-fold (1+ i) n Abr))))

;; The following events help read and update the arrays in Abr in list
;; format

; b-sym
; ---------------------------------------------------

(defun b-sym-help (i n Abr)
  (declare (xargs :guard (and (natp i)
			      (natp n)
			      (= n (b-sym-length Abr))
			      (<= i n))
		  :measure (nfix (- n i))
		  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      nil
    (cons (b-symi i Abr)
	  (b-sym-help (1+ i) n Abr))))

(defun b-sym (Abr)
  ;; read b-sym field in Abr into a list.
  (declare (xargs :guard t
		  :stobjs Abr))
  (b-sym-help 0 (b-sym-length Abr) Abr))

(defun !b-sym-help (i l Abr)
  (declare (xargs :stobjs Abr
                  :guard (and (vw-eval-term-listp l)
                              (natp i)
                              (<= (+ i (len l)) (b-sym-length abr)))
                  :measure (nfix (- (b-sym-length abr) i))))
  (cond
   ((not (mbt (and (true-listp l)
                   (natp i)
                   (<= (+ i (len l)) (b-sym-length abr))))) ; impossible
    abr)
   ((endp l) Abr)
   (t (let ((Abr (!b-symi i (car l) Abr)))
        (!b-sym-help (1+ i) (cdr l) Abr)))))

(defun !b-sym (l Abr)
  ;; update b-sym field in Abr with a list of terms
  (declare (xargs :guard (vw-eval-term-listp l)
                  :stobjs Abr))
  (let* ((len (len l))
         (Abr (if (= len (b-sym-length abr))
                  Abr
                (resize-b-sym len Abr))))
    (!b-sym-help 0 l Abr)))


; b-sym-fold
; ---------------------------------------------------

(defun b-sym-fold-help (i n Abr)
  (declare (xargs :guard (and (natp i)
			      (natp n)
			      (= n (b-sym-fold-length Abr))
			      (<= i n))
		  :measure (nfix (- n i))
		  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      nil
    (cons (b-sym-foldi i Abr)
	  (b-sym-fold-help (1+ i) n Abr))))

(defun b-sym-fold (Abr)
  ;; read b-sym-fold field in Abr into a list.
  (declare (xargs :guard t
		  :stobjs Abr))
  (b-sym-fold-help 0 (b-sym-fold-length Abr) Abr))

(defun !b-sym-fold-help (i l Abr)
  (declare (xargs :stobjs Abr
                  :guard (and (vw-eval-term-listp l)
                              (natp i)
                              (<= (+ i (len l)) (b-sym-fold-length abr)))
                  :measure (nfix (- (b-sym-fold-length abr) i))))
  (cond
   ((not (mbt (and (true-listp l)
                   (natp i)
                   (<= (+ i (len l)) (b-sym-fold-length abr))))) ; impossible
    abr)
   ((endp l) Abr)
   (t (let ((Abr (!b-sym-foldi i (car l) Abr)))
        (!b-sym-fold-help (1+ i) (cdr l) Abr)))))

(defun !b-sym-fold (l Abr)
  ;; update b-sym-fold field in Abr with a list of terms
  (declare (xargs :guard (vw-eval-term-listp l)
                  :stobjs Abr))
  (let* ((len (len l))
         (Abr (if (= len (b-sym-fold-length abr))
                  Abr
                (resize-b-sym-fold len Abr))))
    (!b-sym-fold-help 0 l Abr)))

; b-sym-fold-to-stv
; ---------------------------------------------------

(defun b-sym-fold-to-stv-help (i n Abr)
  (declare (xargs :guard (and (natp i)
			      (natp n)
			      (= n (b-sym-fold-to-stv-length Abr))
			      (<= i n))
		  :measure (nfix (- n i))
		  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      nil
    (cons (b-sym-fold-to-stvi i Abr)
	  (b-sym-fold-to-stv-help (1+ i) n Abr))))

(defun b-sym-fold-to-stv (Abr)
  ;; read b-sym-fold-to-stv field in Abr into a list.
  (declare (xargs :guard t
		  :stobjs Abr))
  (b-sym-fold-to-stv-help 0 (b-sym-fold-to-stv-length Abr) Abr))

(defun !b-sym-fold-to-stv-help (i l Abr)
  (declare (xargs :stobjs Abr
                  :guard (and (nat-listp l)
                              (natp i)
                              (<= (+ i (len l)) (b-sym-fold-to-stv-length abr)))
                  :measure (nfix (- (b-sym-fold-to-stv-length abr) i))))
  (cond
   ((not (mbt (and (true-listp l)
                   (natp i)
                   (<= (+ i (len l)) (b-sym-fold-to-stv-length abr))))) ; impossible
    abr)
   ((endp l) Abr)
   (t (let ((Abr (!b-sym-fold-to-stvi i (car l) Abr)))
        (!b-sym-fold-to-stv-help (1+ i) (cdr l) Abr)))))

(defun !b-sym-fold-to-stv (l Abr)
  ;; update b-sym-fold-to-stv field in Abr with a list of terms
  (declare (xargs :guard (nat-listp l)
                  :stobjs Abr))
  (let* ((len (len l))
         (Abr (if (= len (b-sym-fold-to-stv-length abr))
                  Abr
                (resize-b-sym-fold-to-stv len Abr))))
    (!b-sym-fold-to-stv-help 0 l Abr)))

; A-num
; ---------------------------------------------------

(defun A-num-help (i n Abr)
  (declare (xargs :guard (and (natp i)
			      (natp n)
			      (= n (A-num-length Abr))
			      (<= i n))
		  :measure (nfix (- n i))
		  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      nil
    (cons (A-numi i Abr)
	  (A-num-help (1+ i) n Abr))))

(defun A-num (Abr)
  (declare (xargs :guard t
		  :stobjs Abr))
  (A-num-help 0 (A-num-length Abr) Abr))

(defun !A-num-help (i l Abr)
  (declare (xargs :stobjs Abr
                  :guard (and (list-of-sra-rational-rowp l)
                              (natp i)
                              (<= (+ i (len l)) (A-num-length abr)))
                  :measure (nfix (- (A-num-length abr) i))))
  (cond
   ((not (mbt (and (list-of-sra-rational-rowp l)
                   (natp i)
                   (<= (+ i (len l)) (A-num-length abr))))) ; impossible
    abr)
   ((endp l) Abr)
   (t (let ((Abr (!A-numi i (car l) Abr)))
        (!A-num-help (1+ i) (cdr l) Abr)))))

(defun !A-num (l Abr)
  ;; Update A-num field in Abr with a matrix (in list format) of
  ;; sparse rows with rational entries.
  (declare (xargs :guard (list-of-sra-rational-rowp l)
                  :stobjs Abr))
  (let* ((len (len l))
         (Abr (if (= len (A-num-length abr))
                  Abr
                (resize-A-num len Abr))))
    (!A-num-help 0 l Abr)))

; A-sym
; ---------------------------------------------------

(defun A-sym-help (i n Abr)
  (declare (xargs :guard (and (natp i)
			      (natp n)
			      (= n (A-sym-length Abr))
			      (<= i n))
		  :measure (nfix (- n i))
		  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      nil
    (cons (A-symi i Abr)
	  (A-sym-help (1+ i) n Abr))))

(defun A-sym (Abr)
  (declare (xargs :guard t
		  :stobjs Abr))
  (A-sym-help 0 (A-sym-length Abr) Abr))

(defun !A-sym-help (i l Abr)
  (declare (xargs :stobjs Abr
                  :guard (and (list-of-sra-term-rowp l)
                              (natp i)
                              (<= (+ i (len l)) (A-sym-length abr)))
                  :measure (nfix (- (A-sym-length abr) i))))
  (cond
   ((not (mbt (and (list-of-sra-term-rowp l)
                   (natp i)
                   (<= (+ i (len l)) (A-sym-length abr))))) ; impossible
    abr)
   ((endp l) Abr)
   (t (let ((Abr (!A-symi i (car l) Abr)))
        (!A-sym-help (1+ i) (cdr l) Abr)))))

(defun !A-sym (l Abr)
  ;; Update A-sym field in Abr with a matrix (in list format) of
  ;; sparse rows with rational entries.
  (declare (xargs :guard (list-of-sra-term-rowp l)
                  :stobjs Abr))
  (let* ((len (len l))
         (Abr (if (= len (A-sym-length abr))
                  Abr
                (resize-A-sym len Abr))))
    (!A-sym-help 0 l Abr)))

; A-sym-fold
; ---------------------------------------------------

(defun A-sym-fold-help (i n Abr)
  (declare (xargs :guard (and (natp i)
			      (natp n)
			      (= n (A-sym-fold-length Abr))
			      (<= i n))
		  :measure (nfix (- n i))
		  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      nil
    (cons (A-sym-foldi i Abr)
	  (A-sym-fold-help (1+ i) n Abr))))

(defun A-sym-fold (Abr)
  (declare (xargs :guard t
		  :stobjs Abr))
  (A-sym-fold-help 0 (A-sym-fold-length Abr) Abr))

(defun !A-sym-fold-help (i l Abr)
  (declare (xargs :stobjs Abr
                  :guard (and (list-of-sra-term-rowp l)
                              (natp i)
                              (<= (+ i (len l)) (A-sym-fold-length abr)))
                  :measure (nfix (- (A-sym-fold-length abr) i))))
  (cond
   ((not (mbt (and (list-of-sra-term-rowp l)
                   (natp i)
                   (<= (+ i (len l)) (A-sym-fold-length abr))))) ; impossible
    abr)
   ((endp l) Abr)
   (t (let ((Abr (!A-sym-foldi i (car l) Abr)))
        (!A-sym-fold-help (1+ i) (cdr l) Abr)))))

(defun !A-sym-fold (l Abr)
  ;; Update A-sym-fold field in Abr with a matrix (in list format) of
  ;; sparse rows with rational entries.
  (declare (xargs :guard (list-of-sra-term-rowp l)
                  :stobjs Abr))
  (let* ((len (len l))
         (Abr (if (= len (A-sym-fold-length abr))
                  Abr
                (resize-A-sym-fold len Abr))))
    (!A-sym-fold-help 0 l Abr)))

; A-sym-fold-to-stv
; ---------------------------------------------------

(defun A-sym-fold-to-stv-help (i n Abr)
  (declare (xargs :guard (and (natp i)
			      (natp n)
			      (= n (A-sym-fold-to-stv-length Abr))
			      (<= i n))
		  :measure (nfix (- n i))
		  :stobjs Abr))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      nil
    (cons (A-sym-fold-to-stvi i Abr)
	  (A-sym-fold-to-stv-help (1+ i) n Abr))))

(defun A-sym-fold-to-stv (Abr)
  (declare (xargs :guard t
		  :stobjs Abr))
  (A-sym-fold-to-stv-help 0 (A-sym-fold-to-stv-length Abr) Abr))

(defun !A-sym-fold-to-stv-help (i l Abr)
  (declare (xargs :stobjs Abr
                  :guard (and (list-of-sra-nat-rowp l)
                              (natp i)
                              (<= (+ i (len l)) (A-sym-fold-to-stv-length abr)))
                  :measure (nfix (- (A-sym-fold-to-stv-length abr) i))))
  (cond
   ((not (mbt (and (list-of-sra-nat-rowp l)
                   (natp i)
                   (<= (+ i (len l)) (A-sym-fold-to-stv-length abr))))) ; impossible
    abr)
   ((endp l) Abr)
   (t (let ((Abr (!A-sym-fold-to-stvi i (car l) Abr)))
        (!A-sym-fold-to-stv-help (1+ i) (cdr l) Abr)))))

(defun !A-sym-fold-to-stv (l Abr)
  ;; Update A-sym-fold-to-stv field in Abr with a matrix (in list format) of
  ;; sparse rows with rational entries.
  (declare (xargs :guard (list-of-sra-nat-rowp l)
                  :stobjs Abr))
  (let* ((len (len l))
         (Abr (if (= len (A-sym-fold-to-stv-length abr))
                  Abr
                (resize-A-sym-fold-to-stv len Abr))))
    (!A-sym-fold-to-stv-help 0 l Abr)))

(defun add-sra-term-rows (a b)
  ;; Add two sparse rows
  (declare (xargs :guard (and (sra-rowp a)    ;; try sra-term-rowp
			      (sra-rowp b))))
  (if (atom b)
      a
    (let* ((pair (car b))
	   (col  (car pair))
	   (val-b  (cdr pair))
	   (val-a (sra-rget col a ''0))
	   (new-val (if (equal val-a ''0)
			val-b
		      (list 'f+ val-a val-b)))
	   (a    (sra-rput col a new-val)))
      (add-sra-term-rows a (cdr b)))))

(defun xp-rec-updates (x-i dp-x-i cycle nvars hn rec)
  "This function updates the derivative records.  Note, this function
   assumes that the records at the current time (Tn) have already been
   updated for the node and branch values while the most recent values
   for the derivative names (xp-names) have not yet been updated with
   time Tn values.  We only update the derivatives identified in list
   X-NAMES, which must be correspondence with DP-X-NAMES."
  (declare (type (unsigned-byte 60) x-i dp-x-i cycle nvars)
           (xargs :measure (nfix (- nvars dp-x-i))
                  :guard (and (<= (* (1+ cycle) nvars) (arl rec))
                              (< x-i dp-x-i)
                              (<= dp-x-i nvars)
                              (rationalp hn)
                              (< 0 hn)
                              (< 0 cycle)
                              (<= (arl rec) *2^60*))
                  :guard-hints (("Goal" :in-theory (enable ar-theory-lemmas)))
                  :stobjs rec))
  (if (zp (- nvars dp-x-i))
      rec
    (b* ((Vn (ari x-i cycle nvars rec))
         (Vn-1 (ari x-i (1- cycle) nvars rec))
         (dpn-1 (ari dp-x-i (1- cycle) nvars rec))
         ;; Calculate the derivatives
         (dpn (xp-deriv Vn Vn-1 dpn-1 hn))
         (rec (!ari dp-x-i cycle nvars dpn rec)))
      (xp-rec-updates (1+ x-i) (1+ dp-x-i) cycle nvars hn rec))))

(defun rec-values-reversed (i ncycles nvars rec)
  (declare (xargs :guard (and (natp i)
                              (natp ncycles)
                              (natp nvars)
                              (< i nvars)
                              (<= (* ncycles nvars) (arl rec))
                              (< nvars *2^60*)
                              (<= (arl rec) *2^60*))
                  :guard-hints (("Goal" :nonlinearp t))
                  :stobjs rec))
  (cond ((zp ncycles) nil)
        (t (let ((ncycles (1- ncycles)))
             (cons (ari i ncycles nvars rec)
                   (rec-values-reversed i ncycles nvars rec))))))

(defun output-rec-as-alist-1 (names i ncycles nvars rec)
  (declare (xargs :guard (and (symbol-listp names)
                              (natp i)
                              (natp ncycles)
                              (natp nvars)
                              (<= nvars (arl rec))
                              (<= (+ i (len names)) nvars)
                              (<= (* ncycles nvars) (arl rec))
                              (< nvars *2^60*)
                              (<= (arl rec) *2^60*))
                  :stobjs rec))
  (if (atom names)
      nil
    (let* ((name (car names))
           (values (rec-values-reversed i ncycles nvars rec)))
      (cons (cons name values)
            (output-rec-as-alist-1 (cdr names) (1+ i) ncycles nvars rec)))))

(encapsulate
()

(local (include-book "arithmetic-5/top" :dir :system))

(defun output-rec-as-alist (names nvars rec)
  (declare (xargs :guard (and (symbol-listp names)
                              (consp names)
                              (natp nvars)
                              (<= (len names) nvars)
                              (<= nvars (arl rec))
                              (< nvars *2^60*)
                              (<= (arl rec) *2^60*))
                  :stobjs rec))
  (let ((ncycles (floor (arl rec) nvars)))
    (output-rec-as-alist-1 names 0 ncycles nvars rec)))
)

(defun sra-gather-terms (row)
  (declare (xargs :guard (sra-term-rowp row)
                  :guard-hints
                  (("Goal" :in-theory (enable sra-term-rowp)))))
  (if (atom row)
      nil
    (let* ((pair (car row))
           (term (cdr pair)))
      (cons term (sra-gather-terms (cdr row))))))

(defthm vw-eval-term-listp-sra-gather-terms
  (implies (sra-term-rowp row)
           (vw-eval-term-listp (sra-gather-terms row)))
  :hints
  (("Goal" :in-theory (enable sra-term-rowp))))

(defun gather-terms-A-sym-fold (i n Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n)
                              (= n (A-sym-fold-length Abr)))
                  :stobjs Abr))
  (if (zp (- n i))
      nil
    (let* ((row (A-sym-foldi i Abr))
           (terms (sra-gather-terms row)))
      (append terms
              (gather-terms-A-sym-fold (1+ i) n Abr)))))

(defthm vw-eval-term-listp-append
  (implies (and (vw-eval-term-listp l1)
                (vw-eval-term-listp l2))
           (vw-eval-term-listp (append l1 l2))))

(defthm vw-eval-term-listp-gather-terms-A-sym-fold
  (implies (Abrp Abr)
           (vw-eval-term-listp (gather-terms-A-sym-fold i n Abr))))

(defun gather-terms-b-sym-fold (i n Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n)
                              (= n (b-sym-fold-length Abr)))
                  :stobjs Abr))
  (if (zp (- n i))
      nil
    (let ((term (b-sym-foldi i Abr)))
      (cons term
            (gather-terms-b-sym-fold (1+ i) n Abr)))))

(defthm vw-eval-term-listp-gather-terms-b-sym-fold
  (implies (Abrp Abr)
           (vw-eval-term-listp (gather-terms-b-sym-fold i n Abr))))

(defun init-b-sym-fold-to-stv (i n terms-to-stv Abr)
  (declare (xargs :measure (nfix (- n i ))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n)
                              (= n (b-sym-fold-length Abr))
                              (= n (b-sym-fold-to-stv-length Abr))
                              (vw-eval-term-nat-alistp terms-to-stv))
                  :stobjs Abr))
  (if (zp (- n i))
      Abr
    (let* ((term (b-sym-foldi i Abr))
           (index-or-nil (cdr (hons-get term terms-to-stv))))
      (if index-or-nil
          (let ((Abr (!b-sym-fold-to-stvi i index-or-nil Abr)))
            (init-b-sym-fold-to-stv (1+ i) n terms-to-stv Abr))
        (prog2$ (cw "init-b-sym-fold-to-stv: bad STV mapping provided!.~%")
                Abr)))))

(defun A-sym-row-to-stv (row terms-to-stv)
  (declare (xargs :guard (sra-term-rowp row)
                  :guard-hints
                  (("Goal" :in-theory (enable sra-term-rowp)))))
  (if (atom row)
      nil
    (let* ((pair (car row))
           (col (car pair))
           (term (cdr pair))
           (index-or-nil (cdr (hons-get term terms-to-stv))))
      (if index-or-nil
          (cons (cons col index-or-nil)
                (A-sym-row-to-stv (cdr row) terms-to-stv))
        (prog2$ (cw "A-sym-row-to-stv: bad STV mapping provided!.~%")
                nil)))))

(defthm sra-rowp-A-sym-row-to-stv
  (implies (sra-rowp row)
           (sra-rowp (A-sym-row-to-stv row terms-to-stv))))

(defthm sra-nat-row-elements-p-A-sym-row-to-stv
  (implies (vw-eval-term-nat-alistp terms-to-stv)
           (sra-nat-row-elements-p (A-sym-row-to-stv row terms-to-stv))))

(defun init-A-sym-fold-to-stv (i n terms-to-stv Abr)
  (declare (xargs :measure (nfix (- n i ))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n)
                              (= n (A-sym-fold-length Abr))
                              (= n (A-sym-fold-to-stv-length Abr))
                              (vw-eval-term-nat-alistp terms-to-stv))
                  :stobjs Abr))
  (if (zp (- n i))
      Abr
    (let* ((row (A-sym-foldi i Abr))
           (A-sym-row-stv (A-sym-row-to-stv row terms-to-stv))
           (Abr (!A-sym-fold-to-stvi i A-sym-row-stv Abr)))
      (init-A-sym-fold-to-stv (1+ i) n terms-to-stv Abr))))

(defun init-A-num-row (row)
  (declare (xargs :guard (sra-rowp row)))
  (if (atom row)
      nil
    (let* ((pair (car row))
           (col (car pair)))
      (cons (cons col (r2f 0))
            (init-A-num-row (cdr row))))))

(defthm sra-rowp-init-A-num-row
  (implies (sra-rowp row)
           (sra-rowp (init-A-num-row row))))

(defthm sra-rational-rowp-init-A-num-row
  (implies (sra-rowp row)
           (sra-rational-rowp (init-A-num-row row)))
  :hints
  (("Goal" :in-theory (enable sra-rational-rowp))))

(defun init-A-num (i n Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (<= i n)
                              (= n (A-sym-length Abr))
                              (= n (A-num-length Abr)))
                  :stobjs Abr))
  (if (zp (- n i))
      Abr
    (let* ((A-sym-row (A-symi i Abr))
           (new-A-num-row  (init-A-num-row A-sym-row))
           (Abr (!A-numi i new-A-num-row Abr)))
      (init-A-num (1+ i) n Abr))))

(defun output-rtime (rtime)
  (declare (xargs :stobjs rtime))
  (list (time-list rtime)
        (hn-list rtime)))
