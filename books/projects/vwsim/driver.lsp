
; driver.lsp                                  Vivek & Warren

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

(prog2$ (cw "~%~%VWSIM 2.9~%~%")
        "VWSIM 2.9")

; This is the top-level file that must be loaded to use VWSIM. This
; file performs the simulator setup and enables floating-point
; simulation. See the "Floating-point use in VWSIM" discussion below
; for more information.

; Floating-point use in VWSIM
; ===========================

; The VWSIM simulator makes use of double-precision floating-point
; (fp) arithmetic. Why use fp numbers?

; 1. Over the course of a simulation, repeated calculations and
; incremental updates to rational values cause them to explode in size
; (causing an increase in storage requirements and slowing down
; arithmetic). Meanwhile, double-precision fp numbers are of fixed
; size.

; 2. Hardware-support for fast fp arithmetic. By declaring to the LISP
; compiler that the operands to a function are fp numbers, it may
; generate more efficient code. For example, for a simple addition,
; instead of generating code that calls the general-purpose LISP
; adder, we could simply generate a single fp ADD instruction.

; The problem, however, is that ACL2 does not provide native support
; for floating-point numbers and arithmetic! Until ACL2 supports fp
; arithmetic, we use a work-around to appeal to raw LISP for fp
; calculations. Our approach for doing this is as follows:

; We define the simulator in two stages. First in the ACL2 logic and
; then in raw lisp.

; Stage 1 (In the logical world)
; ------------------------------

; We define the simulator in the ACL2 logical world.

; During this logical definition, whenever the simulator needs to
; recognize a floating-point number, it makes use of the "nump"
; recognizer (see the definition in "num.lisp").

; When the simulator needs to appeal to fp arithmetic, it uses the
; special functions defined in "arith-fp.lisp". Our general convention
; is to name each of these functions with the "f" as its first
; character. For example, the function "f+" adds two floating point
; numbers, "f-" subtracts two floating point numbers, and "f-sin"
; calculates the sine of a floating-point number. When the simulator
; is defined in the logic, these fp functions simply perform rational
; arithmetic, or in the case of non-rational functions (like
; trigonometric functions) are encapsulated (uninterpreted) functions
; with some specified properties.

; Stage 1 is performed by the following form.

(set-inhibit-warnings "Skip-proofs")
; include the simulator and its utilities
(include-book "top" :ttags :all)
(set-inhibit-warnings)

; Stage 2 (In the raw lisp world)
; -------------------------------

; Now that the simulator has been defined in the logic, we reload the
; simulator to use raw lisp fp functionality. The next form below adds
; the :RAW feature to *features*. Then, we reload the simulator files
; that make use of the special fp functions. These files check whether
; the :RAW feature has been defined, and if it has, then they define
; the fp-related functions to actually perform the raw lisp fp
; operations. This is completed by the state-global-let* form.

; The rest of this file defines some top-level utilities to interact
; with the simulator more easily.

(set-raw-mode-on!)

#|
(let (;; in the scope of the following form, manually set
      ;; *default-pathname-defaults* (special variable analog for CBD
      ;; in COMMON LISP) for the COMMON LISP "load"s below.
      (*default-pathname-defaults* (pathname (cbd))))
  (state-global-let*
   ((connected-book-directory (cbd)))
   (progn
     (load "raw.lsp")
     ;; contains #-raw #+raw
     (load "dz-unc/fake-dz-unc.lisp")
     (load "arith-fp.lisp")
     (load "read-float.lisp")
     (load "vw-eval.lisp")
     (load "rtime.lisp")
     (load "vw-eval-ar.lisp")
     (load "sra-vw-flat-sim-help.lisp")
     (load "sra-vw-flat-sim.lisp")
     (load "write-csv.lisp")
     (load "print-records-rec.lisp") ;; new
     ;; We need `set-cbd' since `load' is not smart enough to reset the
     ;; cbd on its own, but the book being loaded below itself has
     ;; (include-book "../vw-flat-hdl")
     ;; and we want that ".." to refer back to the present (driver)
     ;; directory.
     ;; The point is that ACL2's include-book is sensitive to the cbd,
     ;; so we set the cbd appropriately here before encountering the
     ;; include-book forms in the book LOADed below.
     (with-live-state (set-cbd "parse-spice"))
     (load "parse-spice/spice-to-vwsim.lisp")
     (value :invisible)))
  )
|#

; Requires updating to a recent ACL2 (due to a change made in November)
(state-global-let*
 ((connected-book-directory (cbd)
                            ;; restore not only cbd but also
                            ;; *default-pathname-defaults*
                            set-cbd-state))
 (progn
   (load "raw.lsp")
   ;; contains #-raw #+raw
   (load "dz-unc/fake-dz-unc.lisp")
   (load "arith-fp.lisp")
   (load "read-float.lisp")
   (load "vw-eval.lisp")
   (load "rtime.lisp")
   (load "vw-eval-ar.lisp")
   (load "sra-vw-flat-sim-help.lisp")
   (load "sra-vw-flat-sim.lisp")
   (load "write-csv.lisp")
   (load "print-records-rec.lisp") ;; new
   ;; We need `set-cbd' since `load' is not smart enough to reset the
   ;; cbd on its own, but the book being loaded below itself has
   ;; (include-book "../vw-flat-hdl")
   ;; and we want that ".." to refer back to the present (driver)
   ;; directory.
   ;; The point is that ACL2's include-book is sensitive to the cbd,
   ;; so we set the cbd appropriately here before encountering the
   ;; include-book forms in the book LOADed below.
   (with-live-state (set-cbd "parse-spice"))
   ;; Given the set-cbd above and the fact that *default-pathname-defaults*
   ;; tracks the cbd, the filenae "spice-to-vwsim.lisp" is interpreted relative
   ;; to the parse-spice/ directory.
   (load "spice-to-vwsim.lisp")
   (value :invisible)))


; For tighter checking and potentially more informative backtraces:
; (declaim (optimize (speed 0) (safety 3)))

(set-raw-mode nil)

(defun init-Abr-aux
; This function initializes the fields in the Abr STOBJ given a new
; VWSIM HDL netlist. The Abr STOBJ holds most of the information about
; the simulation state.
    (netlist
     global-nodes
     sim-type       ;; 'voltage or 'phase
     equations      ;; t = return equations; nil = perform simulation
     time-step
     time-stop
     time-start
     tran-time-step
     tran-time-stop
     tran-time-start
     load-sim
     Abr
     ctx
     state
     )
  (declare (xargs
            ;; the function ``parse-spice-result'' is a program-mode
            ;; function
            :mode :program
            :stobjs (Abr state)))
  (b* (;; Read, parse, and sort an input netlist
       (sorted-netlist (topological-sort netlist))
       (- (cw "vwsim: topological-sort completed!~%"))

       ;; If global nodes are declared, emit warning
       (- (if global-nodes
              (cw "WARNING: Global node(s) defined. The use of ~
                   global nodes is discouraged.~%") 0))

       ;; Flatten netlist while attempting to respect global nodes
       (flat-occs (flatten-netlist sorted-netlist global-nodes))
       (- (cw "vwsim: flatten-netlist completed!~%"))

       ;; Just decide that the reference Node is named signal ``GND''
       (reference-node 'GND)

       ;; Set the start time.  If ``equations'' non-NIL, just set
       ;; times to zero.
       (time-start
        (if equations
            0
          (if time-start
              time-start
            (if tran-time-start
                tran-time-start
              (prog2$ (er hard? ctx
                          "No simulation start time provided.~%")
                      0)))))

       ;; How should we deal with a non-zero time-start?
       ;; Remember, all times are rational numbers and not floats!
       ((unless (= time-start 0))
        (prog2$
         (er hard? ctx
             "non-zero time-start is currently not supported.~%")
         (mv Abr state)))

       ;; How do you use max-time-step?
       (time-step
        (if equations
            (* 1 *femto*)
          (if time-step
              time-step
            (if tran-time-step
                tran-time-step
              (prog2$ (er hard? ctx
                          "No simulation time step provided.~%")
                      0)))))

       ;; Arrange for a stop time.
       (time-stop
        (if equations
            (* 1 *femto*)
          (if time-stop
              time-stop
            (if tran-time-stop
                tran-time-stop
              (prog2$ (er hard? ctx
                          "No simulation stop time provided.~%")
                      0)))))

       (- (if (or (not (= time-start 0)) ;; We may want to relax this
                                         ;; constraint...
                  (>= time-start time-stop)
                  (<= time-step 0))
              (prog2$ (er hard? ctx
                          "Simulation time specification error.~%")
                      0)
            nil))

       ;; initialize the Abr fields
       (Abr (!flat-occs flat-occs Abr))
       (Abr (!ref-node reference-node Abr))
       (Abr (!time-start time-start Abr))
       (Abr (!hn time-step Abr))
       (Abr (!time-stop time-stop Abr))
       (Abr (!sim-type sim-type Abr))
       (Abr (!equations equations Abr))
       (Abr (!alter-values-alist nil Abr))
       (Abr (!hrchl-netlist sorted-netlist Abr))
       (Abr (!load-sim load-sim Abr)))
    (mv Abr state)))

(defun init-Abr-cir
; This function initializes the fields in the Abr STOBJ given a new
; SPICE-file description of a circuit.
    (input-file       ;; path to the input .cir file
     sim-type         ;; 'voltage or 'phase
     equations        ;; t = return equations; nil = perform simulation
     cir-concat-char  ;; the heirarchical circuit concatenation
                      ;; character (typically #\| or #\/) in the cir
                      ;; file
     global-nodes-top ;; list of globally-defined nodes provided from
                      ;; top-level simulation command.
; if supplied, time-step, time-end, and time-start take
; precedence over those given in the .tran statement in the
; SPICE file
     time-step
     time-stop
     time-start
     load-sim
     Abr
     state
     )
  (declare (xargs
            ;; the function ``parse-spice-result'' is a program-mode
            ;; function
            :mode :program
            :stobjs (Abr state)))
  (b* ((ctx 'init-Abr-cir)
       ;; Note: vwsim uses the #\/ character to concatenate names of
       ;; heirarchical modules/occurrences.
       (vw-concat-char/ #\/)
       ((mv er-flg parsed-input-file state)
        (parse-spice-result input-file state))
       ((when er-flg)
        (prog2$ (er hard? ctx
                    "Unable to parse the file provided.~%")
                (mv Abr state)))
       (- (cw "~%vwsim: SPICE file ~p0 parsed!~%" input-file))
       (vwsim-modules-time-globals
        (spice-to-vwsim parsed-input-file
                        cir-concat-char vw-concat-char/))
       (- (cw "vwsim: spice-to-vwsim completed!~%"))
       (netlist (cdr (assoc :modules vwsim-modules-time-globals)))
       (global-nodes-cir (cdr (assoc :global-nodes
                                     vwsim-modules-time-globals)))
       (global-nodes (remove-duplicates (append global-nodes-cir
                                                global-nodes-top)))
       (tran-time-start (cadr (cdr (assoc :time-start
                                          vwsim-modules-time-globals))))
       (tran-time-step (cadr (cdr (assoc :time-step
                                         vwsim-modules-time-globals))))
       (tran-time-stop (cadr (cdr (assoc :time-stop
                                         vwsim-modules-time-globals))))

       ;; initialize the Abr fields
       ((mv abr state)
        (init-abr-aux netlist global-nodes sim-type equations time-step
                      time-stop time-start tran-time-step tran-time-stop
                      tran-time-start load-sim Abr ctx state))
       (prints (cdr (assoc :prints vwsim-modules-time-globals)))
       (Abr (!prints prints Abr))
       (Abr (!cir-concat-char cir-concat-char Abr))
       (Abr (!vw-concat-char vw-concat-char/ Abr)))
    (mv Abr state)))

(defun init-Abr-netlist
; This function initializes the fields in the Abr STOBJ given a new
; SPICE-file description of a circuit. This performs some checks
; before calling init-Abr-aux, which does most of the work.
    (netlist   ;; heirarchical netlist to simulate
     sim-type  ;; 'voltage or 'phase
     equations ;; t = return equations; nil = perform simulation
     global-nodes
     time-step
     time-stop
     time-start
     load-sim
     Abr
     state
     )
  (declare (xargs
            ;; the function ``parse-spice-result'' is a program-mode
            ;; function
            :mode :program
            :stobjs (Abr state)))
  (b* ((ctx 'init-Abr-netlist)
       ;; some checks before sorting. Ex. netlist-syntax-okp etc.
       (- (cw "netlist!"))
       ((unless (modules-syntax-okp netlist))
        (prog2$
         (er hard? ctx
             "init-Abr-netlist: the provided netlist is not ~
              well-formed.~%")
         (mv Abr state))))
    (init-abr-aux netlist global-nodes sim-type equations
                  time-step time-stop time-start
                  nil nil nil ;; tran-time-step tran-time-stop
                              ;; tran-time-start
                  load-sim Abr ctx state)))

(defun init-Abr-load
; This function initializes the fields in the Abr STOBJ given a file
; that stores a saved VWSIM simulation.
    (input-file      ;; path to the file to load old simulation from.
     time-step
     time-stop
     Abr
     rtime
     rec
     st-vals
     state)
  (declare (xargs :mode :program
                  :stobjs (Abr rtime rec st-vals state)))
  (b* (((mv ?flg Abr rtime rec st-vals state)
        (load-Abr-from-file input-file Abr rtime rec st-vals state))
       (Abr (!load-sim t Abr))
       (Abr (if time-step
                ;; if no time-step is provided, the time-step from
                ;; the previous simulation will be used.
                (!hn time-step Abr)
              Abr))
       ((mv Abr state)
        (if time-stop
            (if (<= time-stop (time-stop Abr))
                (prog2$
                 (cw "init-Abr-load: the loaded simulation ends at ~
                      time ~p0. Please provide a time-stop that ~
                      exceeds this time.~%" (time-stop Abr))
                 (mv Abr state))
              ;; the simulation will resume at the time that the
              ;; previous simulation ended + the time-step (hn)
              (let* ((Abr (!time-start (+ (current-time Abr)
                                          (hn Abr))
                                       Abr))
                     (Abr (!time-stop  time-stop Abr)))
                (mv Abr state)))
          (prog2$
           (er hard 'init-Abr-load
               "init-Abr-load: the loaded simulation ends at time ~
                ~x0. Please provide a time-stop for the resumed ~
                simulation.~%"
               (time-stop Abr))
           (mv Abr state))))
       (nvars (len (all-rec-names Abr)))
       (ncycles (+ (length (time-list rtime))
                   (ncycles (time-start Abr)
                            (time-stop Abr)
                            (hn Abr))))
       ((when (< (* ncycles nvars) (arl rec)))
        (prog2$
         (er hard 'init-Abr-load
             "Implementation error: attempted to shrink the array of ~
              rec from size ~x0 to size ~x1 (which is the product of ~
              ncycles = ~x2 and nvars = ~x3)."
             (arl rec) (* ncycles nvars) ncycles nvars)
         (mv Abr rtime rec st-vals state)))
       (rec (resize-ar ncycles nvars rec)))
    (mv Abr rtime rec st-vals state)))

(defun vwsim-fn
; This function performs the requested simulation. The VWSIM macro
; provides defaults for some of the input arguments.
    (input      ;; path to the input .cir file
     sim-type        ;; 'voltage or 'phase
     equations       ;; t = return equations; nil = perform simulation
     cir-concat-char ;; the heirarchical circuit concatenation
                     ;; character (typically #\| or #\/) in the cir file
     spice-print     ;; t = use .print statements in SPICE fil, nil =
                     ;; return the VWSIM record
     ;; if supplied, time-step, time-end, and time-start take
     ;; precedence over those given in the .tran statement in the
     ;; SPICE file
     global-nodes
     time-step
     time-stop
     time-start
     output-file ; for write-csv
     load-sim
     save-var
     save-sim
     save-sim-shortp
     return-records
     Abr
     st-vals
     dz
     rtime
     rec
     state
     )
  (declare (xargs :mode :program
                  :stobjs (Abr st-vals dz rtime rec state)))
  (b* (((mv Abr rtime rec st-vals state)
        (if (stringp input)
            ;; input is a file name
            ;; if the file extension is ".lisp", the load-sim flag
            ;; does not need to be supplied. We keep the load-sim flag
            ;; around for backwards compatibility.
            (let ((load-sim (or load-sim
                                (file-extension-is-lisp input))))
              (if load-sim
                  (init-Abr-load input time-step time-stop Abr rtime
                                 rec st-vals state)
                (b* (((mv Abr state)
                      (init-Abr-cir input sim-type equations
                                    cir-concat-char global-nodes
                                    time-step time-stop time-start
                                    load-sim Abr state))
                     (rtime (init-rtime time-start rtime)))
                  (mv Abr rtime rec st-vals state))))
          ;; input is a LISP netlist
          (b* (((mv Abr state)
                (init-Abr-netlist input sim-type equations
                                  global-nodes time-step time-stop
                                  time-start load-sim Abr state))
               (rtime (init-rtime time-start rtime)))
            (mv Abr rtime rec st-vals state))))

       (- (cw "vwsim: simulation starting...~%"))
       ((mv Abr st-vals dz rtime rec)
        (time$ (simulate Abr st-vals dz rtime rec)))
       (- (cw "vwsim: simulation ended!~%"))

       ;; when equations it t, return the symbolic A and b
       ;; matrices
       ((when (or equations
                  (equations Abr)))
        (mv nil (list (cons :A (A-sym Abr))
                      (cons :b (b-sym Abr)))
            Abr st-vals dz rtime rec state))

       ;; when a save-sim file is given, save the simulation state.
       ((mv Abr rtime rec st-vals state)
        (if save-sim
            (prog2$ (cw "vwsim: saving simulation to ~x0.~%"
                        save-sim)
                    (time$
                     (write-Abr-to-file save-sim save-sim-shortp Abr
                                        rtime rec st-vals state)))
          (mv Abr rtime rec st-vals state)))

       ((when (not
               (or return-records spice-print output-file save-var)))
        (mv nil :done Abr st-vals dz rtime rec state))

       ;; when spice-print is nil, return (a subset of) the VWSIM
       ;; simulation record as an alist.
       ((when (not spice-print))
        (let* ((rec-names
                (cond ((or (eq return-records t)
                           (and (null return-records)
                                (or spice-print output-file save-var)))
                       (all-rec-names Abr))
                      ((not (symbol-listp return-records))
                       (er hard 'vwsim
                           "Illegal :return-records argument, ~x0: ~
                            should be a list of symbols."
                           return-records))
                      ((subsetp-eq return-records (all-rec-names Abr))
                       return-records)
                      (t (er hard 'vwsim
                             "Illegal :return-records argument, ~x0. ~
                               The following list contains names ~
                              provided in that argument that fail to ~
                              belong to (all-rec-names Abr):~|~x1."
                             return-records
                             (set-difference-eq return-records
                                                (all-rec-names Abr))))))
               (record-alist
                (output-rec-as-alist rec-names
                                     (length (all-rec-names Abr))
                                     rec))
              (reversed-record (reverse-records record-alist nil)))
         (mv nil reversed-record Abr st-vals dz rtime rec state)))

       ;; Otherwise, use the .print lines in the SPICE file.
       ;; Only return the records requested by the user along with
       ;; the time record
       (nvars (len (all-rec-names Abr)))
       ;; consider storing ncycles in Abr STOBJ
       (ncycles (/ (arl rec) nvars))
       (print-records
        (cons (cons '$time$ (get-rec-var-by-index *$time$-index*
                                                  0 ncycles nvars rec))
              (print-records-rec rec
                                 ncycles
                                 nvars
                                 (all-rec-names Abr)
                                 (prints Abr)
                                 (flat-occs Abr)
                                 (sim-type Abr)
                                 (cir-concat-char Abr)
                                 (vw-concat-char Abr)))))
    (mv nil print-records Abr st-vals dz rtime rec state)))

(defmacro vwsim
; top-level vwsim macro
    (input                   ;; netlist OR path to the input
                             ;; .cir/.lisp file.

     &key                    ;; Keyword parameters
     (sim-type    ''voltage) ;; 'voltage or 'phase.
     (equations   'nil)      ;; t = equations; nil = simulation.
     (spice-print 'nil)      ;; Use SPICE ``.PRINT'' directives.
     (global-nodes           ;; A list of globally-defined nodes
                             ;; (wires) in the circuit.
      'nil)
     (time-step   'nil) ;; no default!
     (time-stop   'nil) ;; no default!
     (time-start  '0)
     (output-file 'nil) ;; Output ``.csv'' file.
     (save-var 'nil)    ;; Save simulation output to a global variable
                        ;; in ``state''.
     (save-sim 'nil)    ;; A filename where the simulation state will
                        ;; be written.
     (save-sim-shortp 'nil)
     (concat-char       ;; the hierarchical netlist name concatenation
                        ;; character.
      '#\|)
     (return-records 'nil) ;; Return records requested by user
     (load-sim 'nil)    ;; A boolean; if t, use ``input'' argument to
                        ;; load an existing simulation.
     )
  `(b* (((mv ?er-flg result Abr st-vals dz rtime rec state)
         (vwsim-fn ,input ,sim-type ,equations ,concat-char
                   ,spice-print ,global-nodes ,time-step ,time-stop
                   ,time-start ,output-file ,load-sim ,save-var
                   ,save-sim ,save-sim-shortp ,return-records Abr
                   st-vals dz rtime rec state)))
     (if ,output-file
         (mv-let (erp val state)
           (write-csv result ,output-file state)
           (prog2$ (and erp
                        (er hard 'vwsim
                            "Unexpected error from write-csv!"))
                   (mv :written Abr st-vals dz rtime rec state)))
       (if ,save-var
           (pprogn (f-put-global ,save-var result state)
                   (mv :saved Abr st-vals dz rtime rec state))
         (mv result Abr st-vals dz rtime rec state)))))

(defmacro vw-output (prints
                     &key
                     (output-file 'nil)
                     (save-var 'nil))
; This macro produces a new alist of the requested simulation
; variables. The alist can be saved to a global variable in state if
; ``save-var'' is provided or written to a csv file if ``output-file''
; is provided.
  `(b* (((unless (symbol-symbol-alistp ,prints))
         (prog2$ (cw "vw-output: the list of output requests should ~
                     be an alist.~%")
                 (mv :error state)))
        (nvars (len (all-rec-names Abr)))
        ;; consider storing ncycles in Abr STOBJ
        (ncycles (/ (arl rec) nvars))
        ((unless (natp ncycles))
         (prog2$ (cw "vw-output: the VWSIM simulation state has been ~
                      corrupted. Please restart the simulator.~%")
                 (mv :error state)))
        (rec-result
         (cons (cons '$time$ (get-rec-var-by-index *$time$-index*
                                                   0 ncycles nvars rec))
               (print-records-rec rec
                                  ncycles
                                  nvars
                                  (all-rec-names Abr)
                                  ,prints
                                  (flat-occs Abr)
                                  (sim-type Abr)
                                  (cir-concat-char Abr)
                                  (vw-concat-char Abr)))))
     (if ,output-file
         (mv-let (erp val state)
           (write-csv rec-result ,output-file state)
           (prog2$ (and erp
                        (er hard 'rec-output
                            "Unexpected error from write-csv!"))
                   (mv :written state)))
       (if ,save-var
           (pprogn (f-put-global ,save-var rec-result state)
                   (mv :saved state))
         (mv rec-result state)))))

(defmacro vw-output-all (&key
                         (output-file 'nil)
                         (save-var 'nil))
; This macro produces the voltage and phase for every node, and the
; voltage across, current through, and phase across every device.

  ;; !! Add all-node-names to Abr STOBJ to avoid duplicating this
  ;; !! work.
  `(vw-output (all-print-reqs
               (remove-duplicates (all-node-names (flat-occs Abr)))
               (strip-cars (flat-occs Abr)))
              :output-file ,output-file
              :save-var ,save-var))

(defmacro vw-plot (keys csv-file)
; This macro appeals to gnuplot to plot the requested variables. It is
; expected that each of the keys exist in the csv-file.

  ;; keys is an alist of pairs of the form `((DEVV . signal0) (DEVI
  ;; . signal1) ...)  csv-file is the path to the written simulation
  ;; results.
  `(b* (((unless (symbol-symbol-alistp ,keys))
         (cw "vw-plot: the list of plot requests should ~
                     be an alist.~%"))
        (keys-as-strings
         (gen-output-names ,keys
                           (cir-concat-char Abr)
                           (vw-concat-char Abr))))
     (run-gnuplot ,csv-file keys-as-strings)))

(defmacro vw-assoc
; This macro gets a request, (type . name) or '$time$, from an alist
; produced by the vw-output command.
    (request alist)
  `(b* (((when (equal ,request '$time$))
         (assoc-equal '$time$ ,alist))
        (request-as-alist (list ,request))
        ((unless (vw-output-request-alistp request-as-alist))
         (cw "vw-assoc: expected a pair consisting of a name and its ~
              type.~%"))
        (request-as-string
         (car (gen-output-names
               request-as-alist
               (cir-concat-char Abr)
               (vw-concat-char Abr)))))
        (assoc-equal request-as-string ,alist)))

(set-raw-mode-on!)

(format t "~%; To profile, execute the following, and later, (memsum):~%~s~%"
        '(progn (clear-memoize-statistics)
                (profile-fn 'vw-eval-subterm-list)
                (profile-fn 'back-ar)
                (profile-fn 'dz-unc-solve)
                (profile-fn 'xp-rec-updates)
                (profile-fn 'update-rec-x-names)))

; Here's a more extensive profiling form:
#|
(progn
  (profile-fn 'vw-eval-subterm-list)
  (profile-fn 'back-ar)
  (profile-fn 'dz-unc-solve)
  (profile-fn 'xp-rec-updates)
  (profile-fn 'update-rec-x-names)
  (profile-fn 'init-Abr-cir)
  (profile-fn 'output-rec-as-alist)
  (profile-fn 'reverse-records)
  (profile-fn 'print-records)
  (profile-fn 'r2f-tree)
  (profile-fn 'simulate-step)
  (profile-fn 'simulate)
  (profile-fn 'load-b-sym-fold-into-dz)
  (profile-fn 'load-a-num-into-dz)
  (profile-fn 'stv-vals-to-A-num)
  (profile-fn 'dz-unc-decomp)
  (profile-fn 'clear-dz-a)
  (profile-fn 'init-st-vals)
  (profile-fn 'read-rec-ar)
  (profile-fn 'read-rec-ar-1)
  (profile-fn 'read-stv)
  (clear-memoize-statistics))
|#
