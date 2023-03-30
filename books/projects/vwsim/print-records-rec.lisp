
; print-records-rec.lisp                        Vivek & Warren

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; This file contains some functions that perform post-processing on
; the simulation results, which are stored in the REC STOBJ.

(in-package "ACL2")

(include-book "sra-vw-flat-sim-help")
(include-book "parse-spice/spice-to-vwsim")

(encapsulate
  ()
  (local
   (defthm multiply-add-less-than
     (implies (and (natp cycle)
                   (natp ncycles)
                   (natp nvars)
                   (< cycle ncycles)
                   (< var-i nvars)
                   (<= (* ncycles nvars) len-rec))
              (< (+ var-i (* cycle nvars)) len-rec))
     :hints
     (("Goal" :nonlinearp t))))

  (defun get-rec-var-by-index (var-i cycle ncycles nvars rec)
    ;; Creates a list of values for the variable index in rec from
    ;; cycle to ncycles (exclusive)
    (declare (xargs :measure (nfix (- ncycles cycle))
                    :guard (and (natp var-i)
                                (natp cycle)
                                (natp ncycles)
                                (natp nvars)
                                (< var-i nvars)
                                (<= cycle ncycles)
                                (<= (* ncycles nvars) (arl rec))
                                (< nvars *2^60*)
                                (< ncycles *2^60*)
                                (<= (arl rec) *2^60*))
                    :guard-hints (("Goal"
                                   :in-theory (enable ar-theory-lemmas)
                                   ))
                    :stobjs rec))
    (if (zp (- ncycles cycle))
        nil
      (cons (ari var-i cycle nvars rec)
            (get-rec-var-by-index var-i (1+ cycle) ncycles nvars rec))))

  (defthm rational-listp-get-rec-var-by-index
    (implies (and (recp rec)
                  (natp var-i)
                  (natp cycle)
                  (natp ncycles)
                  (natp nvars)
                  (< var-i nvars)
                  (<= (* ncycles nvars) (arl rec)))
             (rational-listp (get-rec-var-by-index var-i cycle ncycles nvars rec)))
    :hints
    (("Goal" :in-theory (enable ar-theory-lemmas))))

  (defun get-rec-var-by-name (name cycle ncycles nvars all-rec-names rec)
    ;; Creates a list of values for the variable name in rec from
    ;; cycle to ncycles (exclusive)
    (declare (xargs :guard (and (natp cycle)
                                (natp ncycles)
                                (natp nvars)
                                (symbol-listp all-rec-names)
                                (<= cycle ncycles)
                                (= (len all-rec-names) nvars)
                                (<= (* ncycles nvars) (arl rec))
                                (< nvars *2^60*)
                                (< ncycles *2^60*)
                                (<= (arl rec) *2^60*))
                    :guard-hints (("Goal"
                                   :in-theory (enable ar-theory-lemmas)
                                   ))
                    :stobjs rec))
    (let ((name-index (position-equal name all-rec-names)))
      (if name-index
          (get-rec-var-by-index name-index cycle ncycles nvars rec)
        (cw "get-rec-var-by-name: the variable ~p0 was requested, ~
             but does not exist in the simulation record.~%"
             name))))

  (defthm rational-listp-get-rec-var-by-name
    (implies (and (recp rec)
                  (natp cycle)
                  (natp ncycles)
                  (natp nvars)
                  (true-listp all-rec-names)
                  (= (len all-rec-names) nvars)
                  (<= (* ncycles nvars) (arl rec)))
             (rational-listp (get-rec-var-by-name name cycle ncycles nvars all-rec-names rec)))
    :hints
    (("Goal" :in-theory (enable ar-theory-lemmas))))

  (in-theory (disable get-rec-var-by-name))

  (defun phase-to-voltage-rec-help (dp-node-index cycle ncycles
                                                  nvars constant rec)
    (declare (xargs :measure (nfix (- ncycles cycle))
                    :guard (and (natp dp-node-index)
                                (natp cycle)
                                (natp ncycles)
                                (natp nvars)
                                (rationalp constant)
                                (<= cycle ncycles)
                                (<= (* ncycles nvars) (arl rec))
                                (< nvars *2^60*)
                                (< ncycles *2^60*)
                                (<= (arl rec) *2^60*)
                                (< dp-node-index nvars))
                    :guard-hints (("Goal" :in-theory (enable ar-theory-lemmas)))
                    :stobjs rec))
    (if (zp (- ncycles cycle))
        nil
      (cons (f* constant (ari dp-node-index cycle nvars rec))
            (phase-to-voltage-rec-help dp-node-index (1+ cycle) ncycles nvars constant rec))))

  (defthm rational-listp-phase-to-voltage-rec-help
    (implies (and (recp rec)
                  (natp dp-node-index)
                  (natp cycle)
                  (natp ncycles)
                  (natp nvars)
                  (rationalp constant)
                  (<= (* ncycles nvars) (arl rec))
                  (< dp-node-index nvars))
             (rational-listp (phase-to-voltage-rec-help dp-node-index cycle ncycles
                                                        nvars constant rec)))
    :hints
    (("Goal" :in-theory (enable ar-theory-lemmas))))

  (defun voltage-to-phase-rec-help (node-index prev-voltage prev-phase constant
                                               cycle ncycles nvars rec)
    (declare (xargs :measure (nfix (- ncycles cycle))
                    :guard (and (natp node-index)
                                (natp ncycles)
                                (natp nvars)
                                (natp cycle)
                                (< node-index nvars)
                                (<= cycle ncycles)
                                (<= (* ncycles nvars) (arl rec))
                                (< nvars *2^60*)
                                (< ncycles *2^60*)
                                (<= (arl rec) *2^60*)
                                ;; ensure that simulation times are in
                                ;; the REC STOBJ
                                (<= (len *initial-vars*)
                                    nvars)
                                (rationalp prev-voltage)
                                (rationalp prev-phase)
                                (rationalp constant))
                    :guard-hints (("Goal" :in-theory (enable ar-theory-lemmas)))
                    :stobjs rec))
    (if (zp (- ncycles cycle))
        nil
      (b* ((voltage (ari node-index cycle nvars rec))
           (hn (ari *$hn$-index* cycle nvars rec))
           (phase (f+ prev-phase
                      ;; phi_n = phi_n-1 + (hn/2)*(2e/hbar)*(V_n-1 + V_n)
                      (f* (f* (f/ hn (r2f 2)) constant)
                          (f+ prev-voltage voltage)))))
        (cons phase
              (voltage-to-phase-rec-help node-index
                                         voltage phase constant
                                         (1+ cycle) ncycles nvars rec)))))

  (defthm rational-listp-voltage-to-phase-rec-help
    (implies (and (recp rec)
                  (natp node-index)
                  (natp cycle)
                  (natp ncycles)
                  (natp nvars)
                  (rationalp prev-voltage)
                  (rationalp prev-phase)
                  (rationalp constant)
                  (<= (len *initial-vars*)
                      nvars)
                  (<= (* ncycles nvars) (arl rec))
                  (< node-index nvars))
             (rational-listp (voltage-to-phase-rec-help node-index prev-voltage
                                                        prev-phase constant
                                                        cycle ncycles nvars rec)))
    :hints
    (("Goal" :in-theory (enable ar-theory-lemmas)))))

(defun phase-to-voltage-rec (node ncycles nvars all-rec-names rec)
  "Converts the phase values of a node to voltage values (with respect
  to ground)."
  ;; This function will primarily be used after a phase-based
  ;; simulation
  (declare (xargs :guard (and (symbolp node)
                              (natp ncycles)
                              (natp nvars)
                              (symbol-listp all-rec-names)
                              (<= (* ncycles nvars) (arl rec))
                              (< nvars *2^60*)
                              (< ncycles *2^60*)
                              (<= (arl rec) *2^60*)
                              (= (len all-rec-names) nvars)
                              ;; ensure that simulation times are in
                              ;; the REC STOBJ
                              (<= (len *initial-vars*)
                                  (len all-rec-names)))
                  :stobjs rec))
  (b* ((dp-node (dp node))
       (dp-node-index (position-equal dp-node all-rec-names))
       ((unless dp-node-index)
        (cw "phase-to-voltage-rec: the node ~p0 does not exist in the
            ~ simulation output.~%" node))
       (constant (f/ (r2f (f*phi0*))
                     (f* (r2f 2) (r2f (f*pi*))))))
    (phase-to-voltage-rec-help dp-node-index 0 ncycles nvars constant rec)))

(defthm rational-listp-phase-to-voltage-rec
  (implies (and (recp rec)
                (natp ncycles)
                (natp nvars)
                (<= (* ncycles nvars) (arl rec))
                (= (len all-rec-names) nvars)
                ;; ensure that simulation times are in
                ;; the REC STOBJ
                (<= (len *initial-vars*)
                    (len all-rec-names))
                )
           (rational-listp (phase-to-voltage-rec node ncycles nvars all-rec-names rec))))

(in-theory (disable phase-to-voltage-rec))

(defun voltage-to-phase-rec (node ncycles nvars all-rec-names rec)
  "Converts the voltage values of a node to phase values"
  ;; This function will primarily be used after a voltage-based
  ;; simulation
  (declare (xargs :guard (and (symbolp node)
                              (natp ncycles)
                              (natp nvars)
                              (symbol-listp all-rec-names)
                              (<= (* ncycles nvars) (arl rec))
                              (< nvars *2^60*)
                              (< ncycles *2^60*)
                              (<= (arl rec) *2^60*)
                              (= (len all-rec-names) nvars)
                              ;; ensure that simulation times are in
                              ;; the REC STOBJ
                              (<= (len *initial-vars*)
                                  (len all-rec-names)))
                  :stobjs rec))
  ;; we use the formula for the phase guess (see main.pdf) to
  ;; calculate the phase at each time step
  ;; phi_n = phi_n-1 + (hn/2)*(2e/hbar)*(V_n-1 + V_n)
  (b* ((node-index (position-equal node all-rec-names))
       ((unless node-index)
        (cw "voltage-to-phase-rec: the node ~p0 does not exist in the
            ~ simulation output.~%" node))
       ;; (hns (cdr (hons-assoc-equal '$hn$ records)))
       (constant (f/ (f* (r2f 2) (r2f (f*e_C*)))
                     (r2f (f*h_bar*))))
       ;; At this time, VWSIM does not support continuation of
       ;; simulations starting from time 0. What if we would like to
       ;; start the simulation at a non-zero initial voltage/phase???
       (phases (voltage-to-phase-rec-help
                node-index (r2f 0) (r2f 0) constant
                0 ncycles nvars rec)))
    phases))

(defthm rational-listp-voltage-to-phase-rec
  (implies (and (recp rec)
                (natp ncycles)
                (natp nvars)
                (<= (* ncycles nvars) (arl rec))
                (= (len all-rec-names) nvars)
                ;; ensure that simulation times are in
                ;; the REC STOBJ
                (<= (len *initial-vars*)
                    (len all-rec-names)))
           (rational-listp (voltage-to-phase-rec node ncycles nvars all-rec-names rec))))

(in-theory (disable voltage-to-phase-rec))

(encapsulate
  ()

  (local (defthm consp-cdr-occurrencep
         (implies (occurrencep occ)
                  (consp (cdr occ)))))

  (defthm len-position-equal-ac
    (implies (and (natp acc)
                  (position-equal-ac i l acc))
             (< (position-equal-ac i l acc) (+ acc (len l)))))

  (defthm len-position-equal
    (implies (and (true-listp l)
                  (position-equal i l))
             (< (position-equal i l) (len l)))
    :hints
    (("Goal" :in-theory (enable position-equal))))

  (defun devv-rec (occ ncycles nvars all-rec-names sim-type rec)
    ;; calculates the voltage across a device
    ;; TODO: make "subtract-lists" perform the pairwise subtraction
    ;; directly from the STOBJ.
    (declare (xargs :guard (and (occurrencep occ)
                                (natp ncycles)
                                (natp nvars)
                                (symbol-listp all-rec-names)
                                (<= (* ncycles nvars) (arl rec))
                                (< nvars *2^60*)
                                (< ncycles *2^60*)
                                (<= (arl rec) *2^60*)
                                (= (len all-rec-names) nvars)
                                ;; ensure that simulation times are in
                                ;; the REC STOBJ
                                (<= (len *initial-vars*)
                                    (len all-rec-names))
                                (symbolp sim-type))
                    :guard-hints (("Goal" :in-theory (disable member-equal no-duplicatesp-equal)))
                    :stobjs rec))
    (case-match occ
      ((& component (node+ node-) (branch) . &)
       (if (eq component 'k)
           (cw "devv: the mutual inductance is not a device, and hence
         the results are not stored.~%~p0.~%"
               occ)
         (if (eq sim-type 'voltage)
             (b* ((node+-vals
                   (get-rec-var-by-name node+ 0 ncycles nvars
                                        all-rec-names rec))
                  (node--vals
                   (get-rec-var-by-name node- 0 ncycles nvars
                                        all-rec-names rec)))
               (subtract-lists node+-vals node--vals))
           ;; in a phase-based simulation, the JJ's branch stores the
           ;; voltage across it
           (if (eq component 'b)
               (get-rec-var-by-name branch 0 ncycles nvars
                                    all-rec-names rec)
             ;; in phase-based simulation, we convert the phase values to
             ;; voltages and then subtract to get the device voltage
             (subtract-lists
              (phase-to-voltage-rec node+ ncycles nvars all-rec-names
                                    rec)
              (phase-to-voltage-rec node- ncycles nvars all-rec-names
                                    rec))))))
      ;; four-node devices (only the transmission line)
      ((& 't (node0+ node0- node1+ node1-) . &)
       (if (eq sim-type 'voltage)
           (b* ((node0+-vals (get-rec-var-by-name
                              node0+ 0 ncycles nvars all-rec-names rec))
                (node0--vals (get-rec-var-by-name
                              node0- 0 ncycles nvars all-rec-names rec))
                (node1+-vals (get-rec-var-by-name
                              node1+ 0 ncycles nvars all-rec-names rec))
                (node1--vals (get-rec-var-by-name
                              node1- 0 ncycles nvars all-rec-names rec)))
             ;; The voltages across the transmission line are the
             ;; voltage across the entrance nodes and the voltage across
             ;; the exit nodes.
             (list (subtract-lists node0+-vals node0--vals)
                   (subtract-lists node1+-vals node1--vals)))
         ;; In phase-based simulation, convert phase values to voltage
         ;; values
         (list (subtract-lists (phase-to-voltage-rec node0+ ncycles nvars all-rec-names rec)
                               (phase-to-voltage-rec node0- ncycles nvars all-rec-names rec))
               (subtract-lists (phase-to-voltage-rec node1+ ncycles nvars all-rec-names rec)
                               (phase-to-voltage-rec node1- ncycles nvars all-rec-names rec)))))
      (& (cw "devv: the results of the specified device are not stored.~%~p0.~%"
             occ))))

  (defun jj-current-rec (occ ncycles nvars all-rec-names sim-type rec)
    ;; calculates the current through a JJ using the simulation
    ;; records
    (declare (xargs :guard (and (occurrencep occ)
                                (natp ncycles)
                                (natp nvars)
                                (symbol-listp all-rec-names)
                                (symbolp sim-type)
                                (<= (* ncycles nvars) (arl rec))
                                (< nvars *2^60*)
                                (< ncycles *2^60*)
                                (<= (arl rec) *2^60*)
                                (= (len all-rec-names) nvars)
                                ;; ensure that simulation times are in
                                ;; the REC STOBJ
                                (<= (len *initial-vars*)
                                    (len all-rec-names)))
                    :guard-hints (("Goal" :in-theory (e/d (f/) (member-equal no-duplicatesp-equal))))
                    :stobjs rec))
    (b* (((unless (and (occurrencep occ)
                       (equal (cadr occ) 'b)))
          (cw "jj-current-rec: extraced a non-occurrence from occs.~%"))
         (nodes-brs-dps (jj-ios-dps occ))
         (node+-vals (get-rec-var-by-name
                      (car nodes-brs-dps)
                      0 ncycles nvars all-rec-names rec))
         (node--vals (get-rec-var-by-name
                      (cadr nodes-brs-dps)
                      0 ncycles nvars all-rec-names rec))
         (branch-vals (get-rec-var-by-name
                       (caddr nodes-brs-dps)
                       0 ncycles nvars all-rec-names rec))
         (node+-dp-vals (get-rec-var-by-name
                         (cadddr nodes-brs-dps)
                         0 ncycles nvars all-rec-names rec))
         (node--dp-vals (get-rec-var-by-name
                         (car (cddddr nodes-brs-dps))
                         0 ncycles nvars all-rec-names rec))
         ;; will need these values for jj-current in phase-mode
         (branch-dp-vals (get-rec-var-by-name
                          (car (cdr (cddddr nodes-brs-dps)))
                          0 ncycles nvars all-rec-names rec))
         ((unless (and (= (len node+-vals) (len node--vals))
                       (= (len node+-vals) (len node+-dp-vals))
                       (= (len node+-vals) (len node--dp-vals))
                       (= (len node+-vals) (len branch-vals))
                       (= (len node+-vals) (len branch-dp-vals))))
          (cw "jj-current: some entries in the record are not the
          same length!~%"))
         (params (car (cddddr occ)))
         (icrit (r2f (unquote (car params))))
         (area  (r2f (unquote (cadr params))))
         (vg    (r2f (unquote (caddr params))))
         (rn    (r2f (unquote (cadddr params))))
         (r0    (r2f (unquote (car (cddddr params)))))
         (cap   (r2f (unquote (car (cdr (cddddr params))))))
         ;; adjust JJ parameters using area
         (r0 (f/ r0 area))
         (rn  (f/ rn  area))
         (icrit (f* icrit area))
         (cap (f* cap area)))
      (jj-current-help node+-vals node--vals node+-dp-vals
                       node--dp-vals branch-vals branch-dp-vals icrit vg
                       r0 rn cap sim-type)))

  (defun resistor-current-rec
      (occ ncycles nvars all-rec-names sim-type rec)
    (declare (xargs :guard (and (occurrencep occ)
                                (natp ncycles)
                                (natp nvars)
                                (symbol-listp all-rec-names)
                                (symbolp sim-type)
                                (<= (* ncycles nvars) (arl rec))
                                (< nvars *2^60*)
                                (< ncycles *2^60*)
                                (<= (arl rec) *2^60*)
                                (= (len all-rec-names) nvars)
                                ;; ensure that simulation times are in
                                ;; the REC STOBJ
                                (<= (len *initial-vars*)
                                    (len all-rec-names)))
                    :stobjs rec
                    :guard-hints
                    (("Goal"
                      :in-theory (e/d (f*)
                                      (member-equal
                                       no-duplicatesp-equal))))))
    (case-match occ
      ((& 'r (node+ node-) (&) (resistance))
       ;; since Ohm's law requires a constant temperature (and thus a
       ;; constant resistance), we assume that the resistance is
       ;; constant.
       (let ((resistance-val (unquote resistance)))
         (if (eq sim-type 'voltage)
             (let* ((voltages+ (get-rec-var-by-name
                                node+
                                0 ncycles nvars all-rec-names rec))
                    (voltages- (get-rec-var-by-name
                                node-
                                0 ncycles nvars all-rec-names rec)))
               (resistor-current-help voltages+ voltages-
                                      (f-1/x (r2f resistance-val))))
           (let* ((phase-derivs+
                   (get-rec-var-by-name
                    (dp node+)
                    0 ncycles nvars all-rec-names rec))
                  (phase-derivs-
                   (get-rec-var-by-name
                    (dp node-)
                    0 ncycles nvars all-rec-names rec))
                  (s-val (f/ (r2f (f*phi0*))
                             (f* (r2f 2)
                                 (f* (r2f (f*pi*)) (r2f resistance-val))))))
             ;; i = phi0/(2piR) * (dp phase)
             (resistor-current-help phase-derivs+ phase-derivs-
                                    s-val)))))))

  (defun devi-rec (occ ncycles nvars all-rec-names sim-type rec)
    ;; calculates the current through a device
    (declare (xargs :guard (and (occurrencep occ)
                                (natp ncycles)
                                (natp nvars)
                                (symbol-listp all-rec-names)
                                (symbolp sim-type)
                                (<= (* ncycles nvars) (arl rec))
                                (< nvars *2^60*)
                                (< ncycles *2^60*)
                                (<= (arl rec) *2^60*)
                                (= (len all-rec-names) nvars)
                                ;; ensure that simulation times are in
                                ;; the REC STOBJ
                                (<= (len *initial-vars*)
                                    (len all-rec-names)))
                    :guard-hints (("Goal" :in-theory
                                   (disable member-equal
                                            no-duplicatesp-equal)))
                    :stobjs rec))
    (case-match occ
      ;; one-branch devices
      ((& component & (branch) . &)
       (if (eq component 'k)
           (cw "devi: the mutual inductance is not a device, and hence
         the results are not stored.~%~p0.~%"
               occ)
         ;; the JJ's branch stores phase when sim-type is voltage
         ;;                 stores voltage when sim-type is phase
         (if (equal component 'b)
             (jj-current-rec occ ncycles nvars all-rec-names sim-type
                             rec)
           (if (equal component 'r)
               (resistor-current-rec occ ncycles nvars all-rec-names
                                     sim-type rec)
             ;; other components with only one branch store the current
             ;; through the device in the branch
             (let ((currents (get-rec-var-by-name
                              branch
                              0 ncycles nvars all-rec-names rec)))
               currents)))))
      ;; two-branch devices (only the transmission line)
      ((& 't & (br0 br1) . &)
       ;; During simulation, we record the current through the entrance
       ;; and the exit of the transmission line.
       (let ((currents-in (get-rec-var-by-name
                           br0
                           0 ncycles nvars all-rec-names rec))
             (currents-out (get-rec-var-by-name
                           br1
                           0 ncycles nvars all-rec-names rec)))
         (list currents-in currents-out)))
      (& (cw "devi: the results of the specified device are not stored.~%~p0.~%"
             occ))))

  (defun phase-fn-rec (occ ncycles nvars all-rec-names sim-type rec)
    ;; calculates the phase across a device
    (declare (xargs :guard (and (occurrencep occ)
                                (natp ncycles)
                                (natp nvars)
                                (symbol-listp all-rec-names)
                                (<= (* ncycles nvars) (arl rec))
                                (< nvars *2^60*)
                                (< ncycles *2^60*)
                                (<= (arl rec) *2^60*)
                                (= (len all-rec-names) nvars)
                                ;; ensure that simulation times are in
                                ;; the REC STOBJ
                                (<= (len *initial-vars*)
                                    (len all-rec-names))
                                (symbolp sim-type))
                    :guard-hints (("Goal" :in-theory (disable member-equal
                                                              no-duplicatesp-equal)))
                    :stobjs rec))
    (case-match occ
      ;; one-branch devices
      ((& component (node+ node-) (branch) . &)
       (if (eq component 'k)
           (cw "phase: the mutual inductance is not a device, and hence
         the results are not stored.~%~p0.~%"
               occ)
         (if (eq sim-type 'voltage)
             ;; in a voltage-simulation, the JJ's branch stores the
             ;; phase across it
             (if (eq component 'b)
                 (get-rec-var-by-name
                  branch 0 ncycles nvars all-rec-names rec)
               ;; for other components, we need to calculate the phase
               ;; across it.
               (subtract-lists (voltage-to-phase-rec node+ ncycles nvars all-rec-names rec)
                               (voltage-to-phase-rec node- ncycles nvars all-rec-names rec)))
           ;; in a phase-based simulation, we simply subtract the values
           ;; of the nodes
           (let ((node+-vals (get-rec-var-by-name
                              node+ 0 ncycles nvars all-rec-names rec))
                 (node--vals (get-rec-var-by-name
                              node- 0 ncycles nvars all-rec-names rec)))
             (subtract-lists node+-vals node--vals)))))
      ((& 't (node0+ node0- node1+ node1-) . &)
       (if (eq sim-type 'voltage)
           ;; The phases across the transmission line are the phase
           ;; across the entrance nodes and the phase across the exit
           ;; nodes.
           (list (subtract-lists (voltage-to-phase-rec node0+ ncycles nvars all-rec-names rec)
                                 (voltage-to-phase-rec node0- ncycles nvars all-rec-names rec))
                 (subtract-lists (voltage-to-phase-rec node1+ ncycles nvars all-rec-names rec)
                                 (voltage-to-phase-rec node1- ncycles nvars all-rec-names rec)))
         (let ((node0+-vals (get-rec-var-by-name node0+ 0 ncycles nvars all-rec-names rec))
               (node0--vals (get-rec-var-by-name node0- 0 ncycles nvars all-rec-names rec))
               (node1+-vals (get-rec-var-by-name node1+ 0 ncycles nvars all-rec-names rec))
               (node1--vals (get-rec-var-by-name node1- 0 ncycles nvars all-rec-names rec)))
           (list (subtract-lists node0+-vals node0--vals)
                 (subtract-lists node1+-vals node1--vals)))))
      (& (cw "devv: the results of the specified device are not stored.~%~p0.~%"
             occ))))

  (defun print-records-rec (rec ncycles nvars all-rec-names prints
                            flat-netlist sim-type old-concat-char
                            vw-concat-char)
    ;; Filters the simulation state (records) to only return the
    ;; requested (.print) values in the cir file.
    (declare (xargs :guard (and (natp ncycles)
                                (natp nvars)
                                (symbol-listp all-rec-names)
                                (<= (* ncycles nvars) (arl rec))
                                (< nvars *2^60*)
                                (< ncycles *2^60*)
                                (<= (arl rec) *2^60*)
                                (= (len all-rec-names) nvars)
                                ;; ensure that simulation times are in
                                ;; the REC STOBJ
                                (<= (len *initial-vars*) (len all-rec-names))
                                (symbol-symbol-alistp prints)
                                (occurrence-listp flat-netlist)
                                (symbolp sim-type)
                                (characterp old-concat-char)
                                (standard-char-p old-concat-char)
                                (characterp vw-concat-char)
                                (standard-char-p vw-concat-char))
                    :stobjs rec
                    :guard-hints (("Goal" :in-theory
                                   (disable occurrencep member-equal)))))
    (if (atom prints)
        nil
      (let* ((print (car prints))
             (type (car print))
             (name (cdr print)))
        (case type
          (NODEV (b* ((voltages
                       (if (eq sim-type 'voltage)
                           (let ((node-index (position-equal name all-rec-names)))
                             (if node-index
                                 (get-rec-var-by-index node-index 0 ncycles nvars rec)
                               nil))
                         (phase-to-voltage-rec name ncycles nvars all-rec-names rec)))
                      ((unless voltages)
                       (prog2$
                        (cw "print-records-rec: the node ~p0 does not exist.~%"
                            name)
                        (print-records-rec rec ncycles nvars all-rec-names
                                           (cdr prints)
                                           flat-netlist
                                           sim-type
                                           old-concat-char
                                           vw-concat-char)))
                      (new-name (gen-output-name name "V"
                                                 old-concat-char
                                                 vw-concat-char))
                      (new-entry (cons new-name voltages)))
                   (cons new-entry (print-records-rec rec ncycles nvars all-rec-names
                                                      (cdr prints)
                                                      flat-netlist
                                                      sim-type
                                                      old-concat-char
                                                      vw-concat-char))))
          (NODEP (b* ((phases
                       (if (eq sim-type 'voltage)
                           (voltage-to-phase-rec name ncycles nvars all-rec-names rec)
                         (let ((node-index (position-equal name all-rec-names)))
                           (if node-index
                               (get-rec-var-by-index node-index 0 ncycles nvars rec)
                             nil))))
                      ((unless phases)
                       (prog2$
                        (cw "print-records: the node ~p0 does not exist.~%"
                            name)
                        (print-records-rec rec ncycles nvars all-rec-names
                                           (cdr prints)
                                           flat-netlist
                                           sim-type
                                           old-concat-char
                                           vw-concat-char)))
                      (new-name (gen-output-name name "P" old-concat-char
                                                 vw-concat-char))
                      (new-entry (cons new-name phases)))
                   (cons new-entry (print-records-rec rec ncycles nvars all-rec-names
                                                      (cdr prints)
                                                      flat-netlist
                                                      sim-type
                                                      old-concat-char
                                                      vw-concat-char))))
          (DEVV (b* ((occ (assoc-equal name flat-netlist))
                     ((unless occ)
                      (prog2$
                       (cw "print-records: the device ~p0 does not exist.~%"
                           name)
                       (print-records-rec rec ncycles nvars all-rec-names
                                          (cdr prints)
                                          flat-netlist
                                          sim-type
                                          old-concat-char
                                          vw-concat-char)))
                     (voltages (devv-rec occ ncycles nvars all-rec-names sim-type rec)))
                  ;; transmission lines have an entrance and exit
                  ;; voltage.
                  (if (eq (cadr occ) 't)
                      (b* ((voltage-in (car voltages))
                           (voltage-out (cadr voltages))
                           (new-name-in (gen-output-name name "V"
                                                         old-concat-char
                                                         vw-concat-char))
                           (new-name-in (string-append new-name-in "-in"))
                           (new-name-out (gen-output-name name "V"
                                                          old-concat-char
                                                          vw-concat-char))
                           (new-name-out (string-append new-name-out "-out"))
                           (new-entry1 (cons new-name-in voltage-in))
                           (new-entry2 (cons new-name-out voltage-out)))
                        (cons new-entry1
                              (cons new-entry2
                                    (print-records-rec rec ncycles nvars all-rec-names
                                                       (cdr prints)
                                                       flat-netlist
                                                       sim-type
                                                       old-concat-char
                                                       vw-concat-char))))
                    (let* ((new-name (gen-output-name name "V" old-concat-char
                                                      vw-concat-char))
                           (new-entry (cons new-name voltages)))
                      (cons new-entry (print-records-rec rec ncycles nvars all-rec-names
                                                         (cdr prints)
                                                         flat-netlist
                                                         sim-type
                                                         old-concat-char
                                                         vw-concat-char))))))
          (DEVI (b* ((occ (assoc-equal name flat-netlist))
                     ((unless occ)
                      (prog2$
                       (cw "print-records: the device ~p0 does not exist.~%"
                           name)
                       (print-records-rec rec ncycles nvars all-rec-names
                                          (cdr prints)
                                          flat-netlist
                                          sim-type
                                          old-concat-char
                                          vw-concat-char)))
                     (currents (devi-rec occ ncycles nvars all-rec-names sim-type rec)))
                  ;; transmission lines have an entrance and exit
                  ;; current
                  (if (eq (cadr occ) 't)
                      (b* ((current-in (car currents))
                           (current-out (cadr currents))
                           (new-name-in (gen-output-name name "I"
                                                         old-concat-char
                                                         vw-concat-char))
                           (new-name-in (string-append new-name-in "-in"))
                           (new-name-out (gen-output-name name "I"
                                                          old-concat-char
                                                          vw-concat-char))
                           (new-name-out (string-append new-name-out "-out"))
                           (new-entry1 (cons new-name-in current-in))
                           (new-entry2 (cons new-name-out current-out)))
                        (cons new-entry1
                              (cons new-entry2
                                    (print-records-rec
                                     rec ncycles nvars all-rec-names
                                     (cdr prints)
                                     flat-netlist
                                     sim-type
                                     old-concat-char
                                     vw-concat-char))))
                    ;; all of the other devices have only one terminal (branch).
                    (let* ((new-name (gen-output-name name "I" old-concat-char
                                                      vw-concat-char))
                           (new-entry (cons new-name currents)))
                      (cons new-entry
                            (print-records-rec rec ncycles nvars all-rec-names
                                               (cdr prints) flat-netlist
                                               sim-type old-concat-char
                                               vw-concat-char))))))
          (PHASE (b* ((occ (assoc-equal name flat-netlist))
                      ((unless occ)
                       (prog2$
                        (cw "print-records: the device ~p0 does not exist.~%"
                            name)
                        (print-records-rec rec ncycles nvars all-rec-names
                                           (cdr prints) flat-netlist
                                           sim-type old-concat-char
                                           vw-concat-char)))
                      (phases (phase-fn-rec occ ncycles nvars all-rec-names sim-type rec)))
                   (if (eq (cadr occ) 't)
                       (b* ((phase-in (car phases))
                            (phase-out (cadr phases))
                            (new-name-in (gen-output-name name "P"
                                                          old-concat-char
                                                          vw-concat-char))
                            (new-name-in (string-append new-name-in "-in"))
                            (new-name-out (gen-output-name name "P"
                                                           old-concat-char
                                                           vw-concat-char))
                            (new-entry1 (cons new-name-in phase-in))
                            (new-entry2 (cons new-name-out phase-out)))
                         ;; transmission lines have an entrance and
                         ;; exit phase.
                         (cons new-entry1
                               (cons new-entry2
                                     (print-records-rec
                                      rec ncycles nvars all-rec-names
                                      (cdr prints) flat-netlist
                                      sim-type old-concat-char
                                      vw-concat-char))))
                     ;; all of the other devices have only one terminal (branch).
                     (let* ((new-name (gen-output-name name "P"
                                                       old-concat-char
                                                       vw-concat-char))
                            (new-entry (cons new-name phases)))
                       (cons new-entry
                             (print-records-rec rec ncycles nvars all-rec-names
                                                (cdr prints) flat-netlist
                                                sim-type old-concat-char
                                                vw-concat-char))))))
          (otherwise (print-records-rec rec ncycles nvars all-rec-names
                                        (cdr prints) flat-netlist
                                        sim-type old-concat-char
                                        vw-concat-char)))))))
