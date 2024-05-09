
;  vw-flat-hdl.lisp

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; This book defines the VWSIM hardware description language (hdl) for
; flat (non-heirarchical) circuits.

; (ld "vw-hdl.lisp" :ld-pre-eval-print t)
; (certify-book "vw-hdl" ?)

(in-package "ACL2")

(include-book "std/util/bstar"    :dir :system)
; (include-book "std/lists/flatten" :dir :system)

(include-book "constants")
;; (include-book "sra-matrix-defuns")
(include-book "vw-eval")
(include-book "names-and-indices")

; Here we attempt to recognize a well-formed netlist suitable for
; simulation.  We start by defining the primitives for our netlist
; language.

(defconst *primitive-database*
  ;; First name in a terminal list is considered the "positive" terminal
  '(;; The RCSJ (resistively-capacitively-shunted JJ) model for a JJ
    ;; has these six parameters.  When a JJ is driven to its critical
    ;; current, its Cooper pairs "disintegrate" into electrons,
    ;; effectively turning a JJ into a resistor (RN) with
    ;; resistor-like "phase drop".  Note, the dynamics of a JJ firing
    ;; are quite complex -- and our model is a crude approximation of
    ;; what really happens.
    (b (pos neg) (branch) (icrit    ; Josephson Junction
                            area    ; JJ area
                            vg      ; Vgap
                            rn      ; RN
                            r0      ; Rsg
                            cap))   ; JJ capacitance

    ;; Transmission Line:  delay, impedance
    (t (pos0 neg0  pos1 neg1) (br0 br1)
        ;; Delay concerns the end-to-end signal propagation time
        (delay
         ;; The impedance is a complex-load that the physical
         ;; implemention will hopefully provide.
         impedance))

    ;; Mutual Inductance (Transformer); essentially two co-linear inductors
    (k (inductor0-name inductor1-name)
        ;; SFQ circuits coupling factors tend to be low -- 10% to 20%
        (coupling-factor))

    ;; Note, the resistance, capacitance, and inductance could
    ;; themselves be time varying (like the sources above), but for
    ;; now, we expect to see only fixed values for these components.
    ;; Thus, for now, the time-value equations specifying these values
    ;; will just be constants.
    (r  (pos neg) (branch) (resistance))         ; Resistor
    (c  (pos neg) (branch) (capacitance))        ; Capacitor
    (l  (pos neg) (branch) (inductance))         ; Inductor

    ;; Sources: Voltage, Current, and Phase
    (v (pos neg) (branch) (a-time-value-equation)) ; Voltage Source
    (i (pos neg) (branch) (a-time-value-equation)) ; Current Source
    (p (pos neg) (branch) (a-time-value-equation)) ; Phase Source

    ))

(defun occurrencep (occ)
  "Check for well-formed occurrence."
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (disable vw-eval vw-eval-termp
                                               symlp no-duplicatesp-equal)))))
  (and (or (and (consp occ)
                (symbolp (car occ)) ;; the occurrence name
                (consp (cdr occ))
                (symbolp (cadr occ))) ;; the component type
           (cw "occurrencep: Bad structure: ~p0.~%" occ))
       (case-match occ
         ;; JJ
         ((& 'b (node+ node-) (branch)
             (icrit         ; Critical current
              area          ; JJ area
              vg            ; Vgap
              rn            ; RN
              r0            ; Rsg
              cap))
          (and (or (and (symlp branch)
                        (symlp node+)
                        (symlp node-))
                   (cw "occurrencep: bad branch/node names: ~p0.~%" occ))
               (or (no-duplicatesp-equal (list branch node+ node-))
                   (cw "occurrencep: duplicate branch/node names: ~p0.~%" occ))
               (or (and (rational-quotep icrit)
                        (< 0 (unquote icrit)))
                   (cw "occurrencep: Bad icrit value: ~p0.~%" occ))
               (or (and (rational-quotep area)
                        (< 0 (unquote area)))
                   (cw "occurrencep: Bad area value: ~p0.~%" occ))
               (or (and (rational-quotep vg)
                        (< 0 (unquote vg)))
                   ;;!WAHJr Does a zero or negative gap voltage make sense?
                   (cw "occurrencep: Bad vg value: ~p0.~%" occ))
               (or (and (rational-quotep rn)
                        (< 0 (unquote rn)))
                   (cw "occurrencep: Bad rn value: ~p0.~%" occ))
               (or (and (rational-quotep r0)
                        (< 0 (unquote r0)))
                   (cw "occurrencep: Bad r0 value: ~p0.~%" occ))
               (or (and (rational-quotep cap)
                        (< 0 (unquote cap)))
                   (cw "occurrencep: Bad cap value: ~p0.~%" occ))

               ;; Some additional JJ requirements.  In JoSIM,
               ;; ``deltaV'' and ``ICFACT'' are both parameters that
               ;; can be set with SPICE input file parameters;
               ;; otherwise, JoSIM provides default values.  We
               ;; ignored this entirely!!!

               ;; Note: These are pretty "weak" checks; really, just
               ;; sanity checks.
               (< (/ (f*deltaV*) 2) (unquote vg))
               (< (unquote rn)  ;; Normal resistance
                  (unquote r0)) ;; Subgap resistance (generally ~6x more than rn)
               ))

         ;; Transmission line
         ((& 't (node0+ node0- node1+ node1-) (br0 br1)
             (delay impedance))
          (and (or (and (symlp br0)
                        (symlp br1)
                        (symlp node0+)
                        (symlp node0-)
                        (symlp node1+)
                        (symlp node1-))
                   (cw "occurrencep: bad branch/node names: ~p0.~%" occ))
               (or (no-duplicatesp-equal
                    (list br0 br1))
                    ;; Since transmission lines have more than 2
                    ;; nodes, is it acceptable to have the same node
                    ;; listed more than once?  How about all 4 times?
                   (cw "occurrencep: duplicate branch/node names: ~p0.~%" occ))
               (or (rational-quotep delay)
                   (cw "occurrencep: Bad delay value: ~p0.~%" occ))
               (or (rational-quotep impedance)
                   (cw "occurrencep: Bad impedance value: ~p0.~%" occ))))

         ;; Mutual Inductance
         ((occ-name 'k (inductor0-name inductor1-name) (coupling-factor))
          (and (or (and (symbolp inductor0-name)
                        (symbolp inductor1-name))
                   (cw "occurrencep: bad mutual inductance names: ~p0.~%" occ))
               (or (not (equal inductor0-name inductor1-name))
                   (cw "occurrencep: self mutual inductance specified: ~p0.~%" occ))
               (or (and (not (equal occ-name inductor0-name))
                        (not (equal occ-name inductor1-name)))
                   (cw "occurrencep: mutual inductance refers to itself: ~p0.~%" occ))
               (or (and (rational-quotep coupling-factor)
                        (<= -1 (unquote coupling-factor))
                        (<= (unquote coupling-factor) 1))
                   (cw "occurrencep: Bad coupling-factor value: ~p0.~%" occ))))

         ;; V, I, P, R, C, L
         ((& component (node+ node-) (branch) (value))
          (and (or (and (symlp branch)
                        (symlp node+)
                        (symlp node-))
                   (cw "occurrencep: bad branch/node names: ~p0.~%" occ))
               (or (no-duplicatesp-equal (list branch node+ node-))
                   (cw "occurrencep: duplicate branch/node names: ~p0.~%" occ))
               (if (member-eq component '(v i p))
                   ;; Voltage, Current, Phase source
                   (or (vw-eval-termp value)
                       (cw "occurrencep: Bad source parameter: ~p0.~%" occ))
                 (if (member-eq component '(r c l))
                     ;; Resistor, Capacitor, or Inductor. Some day...,
                     ;; maybe we could allow time-varying values!
                     ;; But, for now, we expect our components to
                     ;; maintain their values.
                     (or ;;; (vw-eval-termp value)
                      (and (rational-quotep value)
                           ;; Note, we require non-negative
                           ;; resistance, capacitance, etc.
                           (< 0 (cadr value)))
                      (cw "occurrencep: r,c,l values must be ~
                              non-zero, positive constants, but the ~
                              following value was ~
                              provided: ~p0.~%" occ))
                   (cw "occurrencep: Unrecognized component: ~p0.~%" occ)))))

         ;; Time-varying resistance, capacitance, and inductance
         ;; values require more sophisticated stamps.

         (& (cw "occurrencep: Unrecognized component: ~p0.~%" occ)))))

(defun occurrence-listp (occs)
  "Check for list of occurrences."
  (declare (xargs :guard t))
  (if (atom occs)
      (null occs)
    (and (occurrencep (car occs))
         (occurrence-listp (cdr occs)))))

(defthm occurrence-listp-forward-symbol-alistp
  (implies (occurrence-listp occs)
           (symbol-alistp occs))
  :hints
  (("Goal" :in-theory (disable assoc-equal member-equal no-duplicatesp-equal)))
  :rule-classes :forward-chaining)

(defthm occurrence-listp-forward-symbol-listp-strip-cars
  (implies (occurrence-listp occs)
           (symbol-listp (strip-cars occs)))
  :hints
  (("Goal" :in-theory (disable assoc-equal member-equal no-duplicatesp-equal)))
  :rule-classes :forward-chaining)

(defun all-node-names (occs)
  "Extract terminal (connection) names from occurrence list."
  (declare (xargs :guard (occurrence-listp occs)))
  (if (atom occs)
      nil
    (let ((occ (car occs)))
      (case-match occ
        ((& component nodes & . &)
         (if (eq component 'k)
             (all-node-names (cdr occs))
           (append nodes (all-node-names (cdr occs)))))
         (& nil)))))

(defun all-branch-names (occs)
  "Extract branch (component) names from occurrence list."
  (declare (xargs :guard (occurrence-listp occs)))
  (if (atom occs)
      nil
    (let ((occ (car occs)))
      (case-match occ
        ((& component & branches . &)
         (if (or (eq component 'k)
                 (eq component 'r))
             (all-branch-names (cdr occs))
           (append branches (all-branch-names (cdr occs)))))
        (& nil)))))

(defthm syml-listp-all-branch-names-occurrence-listp
  (implies (occurrence-listp occs)
           (syml-listp (all-branch-names occs)))
  :hints
  (("Goal" :in-theory (disable assoc-equal member-equal no-duplicatesp-equal))))

(defthm syml-listp-all-node-names-occurrence-listp
  (implies (occurrence-listp occs)
           (syml-listp (all-node-names occs)))
  :hints
  (("Goal" :in-theory (disable assoc-equal member-equal no-duplicatesp-equal
                               binary-append))))

(defthm syml-listp-all-names
  (implies (occurrence-listp occs)
           (let* ((all-branch-names (all-branch-names occs))
                  (all-ios (all-node-names occs))
                  (occ-ios (remove-duplicates all-ios :test 'eq)))
             (syml-listp (append occ-ios all-branch-names)))))

(defun mutual-inductance-occs-okp (occs orig-occs)
  (declare (xargs :guard (and (occurrence-listp occs)
                              (occurrence-listp orig-occs))))
  (if (atom occs)
      t
    (and
     (let ((occ (car occs)))
     (case-match occ
       ((& 'k (inductor0-name inductor1-name) &)
        (let ((inductor0 (assoc-equal inductor0-name orig-occs))
              (inductor1 (assoc-equal inductor1-name orig-occs)))
          (and inductor0
               (consp inductor0)
               (consp (cdr inductor0))
               (equal (cadr inductor0) 'l)
               inductor1
               (consp inductor1)
               (consp (cdr inductor1))
               (equal (cadr inductor1) 'l)))
        )
       (& t)))
     (mutual-inductance-occs-okp (cdr occs) orig-occs))))

(in-theory (disable occurrence-listp))

(defthm member-remove-duplicates
  (implies (member a (remove-duplicates-equal x))
           (member a x)))

(defthm no-duplicatesp-equal-remove-duplicates-equal
  (implies (symbol-listp lst)
           (no-duplicatesp-equal (remove-duplicates-equal lst))))

(defthm symbol-listp-forward-eqlable-listp
  (implies (symbol-listp l)
           (eqlable-listp l))
  :rule-classes :forward-chaining)

(defun occurrencesp (occs)
  "Recognizes a well-formed, flat RSFQ circuit module."
  (declare (xargs :guard t))
  (b* (((unless (occurrence-listp occs))
        (cw "occurrencesp: Problem in occurrences.~%"))

       (occ-names (strip-cars occs))
       ((unless (no-duplicatesp occ-names :test 'eq))
        (cw "occurrencesp: Duplicate occurrence name(s) in ~x0~%"
            occs))
       ;; check that mutual inductances are well-formed
       ((unless (mutual-inductance-occs-okp occs occs))
        (cw "occurrencesp: bad mutual inductance reference(s).~%"))

       (all-ios (all-node-names occs))
       (all-ios-no-dups (remove-duplicates all-ios :test 'eq))

       (all-branch-names (all-branch-names occs))
       ((unless (no-duplicatesp all-branch-names))
        (cw "occurrencesp: duplicate branch names.~%"))

       ((if (intersection$ all-ios-no-dups all-branch-names))
        (cw "occurrencesp: duplicate names in branch and nodes.~%"))

       (node-and-branch-names (append all-ios-no-dups all-branch-names))

       ;; Extend as appropriate
       )
    node-and-branch-names))

(defthm occurrencep-assoc-occurrence-listp
  (implies (and (occurrence-listp occs)
                (assoc-equal occ occs))
           (occurrencep (assoc-equal occ occs)))
  :rule-classes (:forward-chaining :rewrite)
  :hints
  (("Goal" :in-theory (enable occurrence-listp occurrencep))))
