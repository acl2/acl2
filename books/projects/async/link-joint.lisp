;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2018

(in-package "ADE")

(include-book "de")
(include-book "macros")

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

(defun extract-state (st)
  ;;(declare (xargs :guard (true-listp st)))
  (if (atom st)
      nil
    (if (fullp (car st))
        (cons (strip-cars (cadr st))
              (extract-state (cddr st)))
      (extract-state (cddr st)))))

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

(defun map-to-links (x)
  (declare (xargs :guard (true-list-listp x)))
  (if (endp x)
      nil
    (cons
     (b* ((tuple (car x))
          (name (first tuple))
          (status (second tuple))
          (value (third tuple)))
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
          (cons (string-append (str::natstr count) "----------")
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
  (netlist-hyps netlist joint-cntl))

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

(defthmd joint-cntl$value
  (implies (joint-cntl& netlist)
           (equal (se 'joint-cntl (list fin fout go) sts netlist)
                  (list (joint-act fin fout go))))
  :hints (("Goal"
           :expand (se 'joint-cntl (list fin fout go) sts netlist)
           :in-theory (enable de-rules joint-cntl&))))

(in-theory (disable joint-act))

;; ======================================================================

;; Click link-state control circuit

(defconst *click-link-st*
  '((click-link-st
     (fi dr)
     (ls)
     (ff0 ff1)
     ((ff0 (req req~) fd1 (fi r))
      (ff1 (ack ack~) fd1 (dr a))
      (g0 (ls) b-xor (req ack))
      (g1 (r) b-not (req))
      (g2 (a) b-not (ack))))))

(defund click-link-st& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist click-link-st))

(local
 (defthmd check-click-link-st
   (and (net-syntax-okp *click-link-st*)
        (net-arity-okp *click-link-st*)
        (click-link-st& *click-link-st*))))

(defthmd click-link-st$value
  (implies (click-link-st& netlist)
           (equal (se 'click-link-st (list fi dr) (list ff0 ff1) netlist)
                  (list (f-xor (car ff0) (car ff1)))))
  :hints (("Goal"
           :expand (se 'click-link-st (list fi dr) (list ff0 ff1) netlist)
           :in-theory (enable de-rules
                              click-link-st&
                              f-gates))))

(defthmd click-link-st$state
  (implies (click-link-st& netlist)
           (equal (de 'click-link-st (list fi dr) (list ff0 ff1) netlist)
                  (list (list (f-if fi
                                    (f-not (car ff0))
                                    (car ff0)))
                        (list (f-if dr
                                    (f-not (car ff1))
                                    (car ff1))))))
  :hints (("Goal"
           :expand (de 'click-link-st (list fi dr) (list ff0 ff1) netlist)
           :in-theory (enable de-rules
                              click-link-st&
                              f-gates))))



