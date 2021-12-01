;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; May 2019

(in-package "ADE")

(include-book "de")
(include-book "store-n")

(include-book "std/lists/flatten" :dir :system)

;; ======================================================================

(defun fullp (link-st)
  (declare (xargs :guard t))
  (equal link-st '(t)))

(defun emptyp (link-st)
  (declare (xargs :guard t))
  (equal link-st '(nil)))

(defun validp (link-st)
  (declare (xargs :guard t))
  (or (fullp link-st) (emptyp link-st)))

;; Some utility functions that help print out a readable format of link states.

(defun 4v->link-st (x)
  (declare (xargs :guard t))
  (cond ((equal x T)
         'full)
        ((equal x NIL)
         'empty)
        ((consp x)
         (4v->link-st (car x)))
        (t nil)))

(defun map-to-links1 (x)
  (declare (xargs :guard (true-list-listp x)))
  (if (endp x)
      nil
    (cons
     (b* ((link (car x))
          (name (first link))
          (status (second link))
          (value (third link)))
       (list* name
              (if (fullp status)
                  (list (4v->link-st status)
                        (v-to-nat value))
                (list (4v->link-st status) '_))))
     (map-to-links1 (cdr x)))))

(defun map-to-links (x)
  (declare (xargs :guard (true-list-listp x)))
  (if (endp x)
      nil
    (cons
     (b* ((link (car x))
          (name (first link))
          (status (second link))
          (value (third link)))
       (list* name
              (if (fullp status)
                  (list (4v->link-st status)
                        (v-to-nat (acl2::flatten value)))
                (list (4v->link-st status) '_))))
     (map-to-links (cdr x)))))

(defun remove-dup-neighbors (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         x)
        ((equal (car x) (cadr x))
         (remove-dup-neighbors (cdr x)))
        (t (cons (car x)
                 (remove-dup-neighbors (cdr x))))))

(defun pretty-list (x count)
  (declare (xargs :guard (natp count)))
  (if (atom x)
      nil
    (cons (car x)
          (cons (string-append (str::nat-to-dec-string count)
                               "------------------------------")
                (pretty-list (cdr x) (1+ count))))))

;; SIGNAL-VALS-GEN randomly generates a sequence of signals' values.

(defun signal-vals-gen (num-signals n state signals-lst)
  (declare (xargs :guard (and (natp num-signals)
                              (natp n))
                  :guard-hints
                  (("Goal" :in-theory (enable random$)))
                  :stobjs state))
  (if (zp n)
      (mv signals-lst state)
    (b* (((mv oracle state) (random$ (expt 2 num-signals) state))
         (signals (nat-to-v oracle num-signals))
         (signals-lst (cons signals signals-lst)))
      (signal-vals-gen num-signals (1- n) state signals-lst))))

;; ======================================================================

;; Non-RTZ two-phase handshake

(defun n-rtz-fullp (req ack)
  (declare (xargs :guard t))
  (and (booleanp req)
       (booleanp ack)
       (not (equal req ack))))

(defun n-rtz-emptyp (req ack)
  (declare (xargs :guard t))
  (and (booleanp req)
       (booleanp ack)
       (equal req ack)))

(defthm n-rtz-fullp-of-b-not
  (implies (n-rtz-fullp req ack)
           (n-rtz-fullp (b-not req) (b-not ack)))
  :rule-classes (:rewrite :type-prescription))

(defthm n-rtz-emptyp-of-b-not
  (implies (n-rtz-emptyp req ack)
           (n-rtz-emptyp (b-not req) (b-not ack)))
  :rule-classes (:rewrite :type-prescription))

(defthm drain-n-rtz-full
  (implies (n-rtz-fullp req ack)
           (n-rtz-emptyp req (b-not ack)))
  :rule-classes (:rewrite :type-prescription))

(defthm fill-n-rtz-empty
  (implies (n-rtz-emptyp req ack)
           (n-rtz-fullp (b-not req) ack))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable n-rtz-fullp n-rtz-emptyp))

;; RTZ two-phase handshake

(defun rtz-fullp (sw)
  (declare (xargs :guard t))
  (equal sw t))

(defun rtz-emptyp (sw)
  (declare (xargs :guard t))
  (equal sw nil))

;; ======================================================================

;; Joint control circuit

(defconst *joint-cntl*
  '((joint-cntl
     (fin fout go)
     (act)
     ()
     ((not-fout (fout~) b-not (fout))
      (g0 (ready) b-and (fin fout~))
      (g1 (b-go) b-bool (go))
      (jact (act) b-and (ready b-go))))))

(defund joint-cntl& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (equal (assoc 'joint-cntl netlist)
         (car *joint-cntl*)))

(local
 (defthmd check-joint-cntl
   (and (net-syntax-okp *joint-cntl*)
        (net-arity-okp *joint-cntl*)
        (joint-cntl& *joint-cntl*))))

(defun joint-act (fin fout go)
  (declare (xargs :guard t))
  (f-and (f-and fin (f-not fout))
         (f-bool go)))

(defthm booleanp-joint-act
  (implies (and (booleanp fin)
                (booleanp fout))
           (booleanp (joint-act fin fout go)))
  :rule-classes :type-prescription)

(defthm joint-act-rewrite
  (and (not (joint-act nil fout go))
       (not (joint-act fin t go))
       (not (joint-act fin fout nil))
       (equal (joint-act t nil go)
              (f-bool go))))

(defthm joint-act-removes-f-buf
  (and (equal (f-buf (joint-act fin fout go))
              (joint-act fin fout go))
       (equal (joint-act (f-buf fin) fout go)
              (joint-act fin fout go))
       (equal (joint-act fin (f-buf fout) go)
              (joint-act fin fout go))
       (equal (joint-act fin fout (f-buf go))
              (joint-act fin fout go)))
  :hints (("Goal" :in-theory (enable f-buf-delete-lemmas-2))))

(defthm joint-cntl$value
  (implies (joint-cntl& netlist)
           (equal (se 'joint-cntl inputs st netlist)
                  (list (joint-act (car inputs) (cadr inputs) (caddr inputs)))))
  :hints (("Goal"
           :expand (se 'joint-cntl inputs st netlist)
           :in-theory (enable de-rules joint-cntl&))))

(in-theory (disable joint-act))

;; ======================================================================

;; Click link control circuit

(defconst *click-link*
  '((click-link
     (fi dr)
     (ls)
     (ff0 ff1)
     ((ff0 (req req~) ff (fi r))
      (ff1 (ack ack~) ff (dr a))
      (g0 (ls) b-xor (req ack))
      (g1 (r) b-not (req))
      (g2 (a) b-not (ack))))))

(defund click-link& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (equal (assoc 'click-link netlist)
         (car *click-link*)))

(local
 (defthmd check-click-link
   (and (net-syntax-okp *click-link*)
        (net-arity-okp *click-link*)
        (click-link& *click-link*))))

(defthm click-link$value
  (implies (click-link& netlist)
           (equal (se 'click-link inputs st netlist)
                  (list (f-xor (caar st) (caadr st)))))
  :hints (("Goal"
           :expand (se 'click-link inputs st netlist)
           :in-theory (enable de-rules
                              click-link&
                              f-gates))))

(defthm click-link$state
  (implies (click-link& netlist)
           (equal (de 'click-link inputs st netlist)
                  (list (list (f-if (car inputs)
                                    (f-not (caar st))
                                    (caar st)))
                        (list (f-if (cadr inputs)
                                    (f-not (caadr st))
                                    (caadr st))))))
  :hints (("Goal"
           :expand (de 'click-link inputs st netlist)
           :in-theory (enable de-rules
                              click-link&
                              f-gates))))

;; ======================================================================

;; DE module of LINK1

(defconst *link1$st-len* 2)

(module-generator
 link1* ()
 'link1
 '(fill drain bit-in)
 '(status bit-out)
 '(s d)
 '((s (status) link-cntl (fill drain))
   (d (bit-out bit-out~) latch (fill bit-in)))
 (declare (xargs :guard t)))

(make-event
 `(progn
    ,@(state-accessors-gen 'link1 '(s d) 0)))

;; DE netlist containing LINK1

(defund link1$netlist ()
  (declare (xargs :guard t))
  (list (link1*)))

;; Recognizer for LINK1

(defund link1& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (equal (assoc 'link1 netlist)
         (link1*)))

;; Sanity check

(local
 (defthmd check-link1$netlist
   (and (net-syntax-okp (link1$netlist))
        (net-arity-okp (link1$netlist))
        (link1& (link1$netlist)))))

;; Constraints on the state of LINK1

(defun link1$valid-st (st)
  (b* ((s (nth *link1$s* st))
       (d (nth *link1$d* st)))
    (and (validp s)
         (true-listp d)
         (equal (len d) 1)
         (or (emptyp s)
             (booleanp (car d))))))

;; The value lemma for LINK1

(defthm link1$value
  (b* ((fill$ (car inputs))
       (bit-in (caddr inputs))
       (s (nth *link1$s* st))
       (d (nth *link1$d* st)))
    (implies (link1& netlist)
             (equal (se 'link1 inputs st netlist)
                    (list (f-buf (car s))
                          (f-if fill$ bit-in (car d))))))
  :hints (("Goal"
           :expand (:free (inputs)
                          (se 'link1 inputs st netlist))
           :in-theory (e/d (de-rules
                            link1&
                            link1*$destructure)
                           ((link1*)
                            de-module-disabled-rules)))))

;; This function specifies the next state of LINK1.

(defun link1$step (inputs st)
  (b* ((fill$ (nth 0 inputs))
       (drain (nth 1 inputs))
       (bit-in (nth 2 inputs))

       (s (nth *link1$s* st))
       (d (nth *link1$d* st)))
    (list
     (list (f-sr fill$ drain (car s)))
     (list (f-if fill$ bit-in (car d))))))

(defthm len-of-link1$step
  (equal (len (link1$step inputs st))
         *link1$st-len*))

;; The state lemma for LINK1

(defthm link1$state
  (implies (link1& netlist)
           (equal (de 'link1 inputs st netlist)
                  (link1$step inputs st)))
  :hints (("Goal"
           :expand (de 'link1 inputs st netlist)
           :in-theory (e/d (de-rules
                            link1&
                            link1*$destructure)
                           ((link1*)
                            de-module-disabled-rules)))))

;; (in-theory (disable link1$step))

;; ======================================================================

;; DE module generator of LINK

(defconst *link$st-len* 2)

(defun link$ins-len (data-size)
  (declare (xargs :guard (natp data-size)))
  (+ 2 (mbe :logic (nfix data-size)
            :exec  data-size)))

(module-generator
 link* (data-size)
 (si 'link data-size)
 (list* 'fill 'drain (sis 'data-in 0 data-size))
 (list* 'status (sis 'data-out 0 data-size))
 ;; INTERNAL STATE
 ;; A link have two state-holding devices: one stores the link's full/empty
 ;; status and one stores the link data.
 '(s d)
 (list
  '(s (status) link-cntl (fill drain))
  (list 'd
        (sis 'data-out 0 data-size)
        (si 'latch-n data-size)
        (list* 'fill (sis 'data-in 0 data-size))))
 (declare (xargs :guard (natp data-size))))

(make-event
 `(progn
    ,@(state-accessors-gen 'link '(s d) 0)))

(defun extract-valid-data (st)
  ;;(declare (xargs :guard (true-listp st)))
  (if (atom st)
      nil
    (b* ((link (car st)))
      (if (fullp (nth *link$s* link))
          (cons (strip-cars (nth *link$d* link))
                (extract-valid-data (cdr st)))
        (extract-valid-data (cdr st))))))

;; DE netlist generator.  A generated netlist will contain an instance of
;; LINK.

(defund link$netlist (data-size)
  (declare (xargs :guard (natp data-size)))
  (cons (link* data-size)
        (union$ (latch-n$netlist data-size)
                :test 'equal)))

;; Recognizer for LINK

(defund link& (netlist data-size)
  (declare (xargs :guard (and (alistp netlist)
                              (natp data-size))))
  (b* ((subnetlist (delete-to-eq (si 'link data-size) netlist)))
    (and (equal (assoc (si 'link data-size) netlist)
                (link* data-size))
         (latch-n& subnetlist data-size))))

;; Sanity check

(local
 (defthmd check-link$netlist-64
   (and (net-syntax-okp (link$netlist 64))
        (net-arity-okp (link$netlist 64))
        (link& (link$netlist 64) 64))))

;; Constraints on the state of LINK

(defun link$st-format (st data-size)
  (b* ((d (nth *link$d* st)))
    (and (len-1-true-listp d)
         (equal (len d) data-size))))

(defthm link$st-format=>constraint
  (implies (link$st-format st data-size)
           (natp data-size))
  :hints (("Goal" :in-theory (enable link$st-format)))
  :rule-classes :forward-chaining)

(defun link$valid-st (st data-size)
  (b* ((s (nth *link$s* st))
       (d (nth *link$d* st)))
    (and (link$st-format st data-size)

         (validp s) ;; The link status is either full or empty.
         (or (emptyp s)               ;; When the link is full,
             (bvp (strip-cars d)))))) ;; its data must be a bit vector.

(defthmd link$valid-st=>constraint
  (implies (link$valid-st st data-size)
           (natp data-size))
  :rule-classes :forward-chaining)

;; The value lemma for LINK

(defthm link$value
  (b* ((fill$ (car inputs))
       (data-in (cddr inputs))
       (s (nth *link$s* st))
       (d (nth *link$d* st)))
    (implies (and (link& netlist data-size)
                  (true-listp data-in)
                  (equal (len data-in) data-size)
                  (link$st-format st data-size))
             (equal (se (si 'link data-size) inputs st netlist)
                    (list* (f-buf (car s))
                           (fv-if fill$ data-in (strip-cars d))))))
  :hints (("Goal"
           :expand (:free (inputs data-size)
                          (se (si 'link data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            link&
                            link*$destructure)
                           (de-module-disabled-rules)))))

;; This function specifies the next state of LINK.

(defun link$step (inputs st data-size)
  (b* ((fill$ (nth 0 inputs))
       (drain (nth 1 inputs))
       (data-in (take (nfix data-size)
                      (nthcdr 2 inputs)))

       (s (nth *link$s* st))
       (d (nth *link$d* st)))
    (list
     (list (f-sr fill$ drain (car s)))
     (pairlis$ (fv-if fill$ data-in (strip-cars d))
               nil))))

(defthm len-of-link$step
  (equal (len (link$step inputs st data-size))
         *link$st-len*))

;; The state lemma for LINK

(defthm link$state
  (implies (and (link& netlist data-size)
                (true-listp inputs)
                (equal (len inputs) (link$ins-len data-size))
                (link$st-format st data-size))
           (equal (de (si 'link data-size) inputs st netlist)
                  (link$step inputs st data-size)))
  :hints (("Goal"
           :expand (:free (data-size)
                          (de (si 'link data-size) inputs st netlist))
           :in-theory (e/d (de-rules
                            link&
                            link*$destructure)
                           (de-module-disabled-rules)))))

;; (in-theory (disable link$step))

(defthm link$valid-st-preserved
  (implies (and (booleanp (nth 0 inputs))
                (booleanp (nth 1 inputs))
                (not (and (nth 0 inputs) (nth 1 inputs)))
                (or (not (nth 0 inputs))
                    (bvp (nthcdr 2 inputs)))
                (link$valid-st st data-size))
           (link$valid-st (link$step inputs st data-size)
                          data-size))
  :hints (("Goal" :in-theory (enable f-sr))))
