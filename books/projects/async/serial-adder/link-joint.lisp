;; Cuong Chau <ckcuong@cs.utexas.edu>
;; November 2016

(in-package "ADE")

(include-book "de")
(include-book "macros")

;; ======================================================================

;; Some utility functions that help print out a readable format of link states.

(defun 4v->link-state (x)
  (declare (xargs :guard t))
  (cond ((equal x T)
         'full)
        ((equal x NIL)
         'empty)
        ((consp x)
         (4v->link-state (car x)))
        (t nil)))

(defun 4v->data (x)
  (declare (xargs :guard t))
  (cond ((equal x T)
         1)
        ((equal x NIL)
         0)
        ((equal x *X*)
         x)
        ((equal x *Z*)
         x)
        ((consp x)
         (cons (4v->data (car x))
               (4v->data (cdr x))))
        (t nil)))

(defun map-to-links (x idx)
  (declare (xargs :guard (and (true-listp x)
                              (natp idx))))
  (if (endp x)
      nil
    (cons
     (list (string-append "L" (str::natstr idx))
           (4v->link-state (car x))
           (reverse (list-fix (4v->data (cadr x)))))
     (map-to-links (cddr x) (1+ idx)))))

(defun map-to-links-list (x count)
  (declare (xargs :guard (and (true-list-listp x)
                              (natp count))))
  (if (endp x)
      nil
    (cons (map-to-links (car x) 0)
          (cons (string-append (str::natstr count) "-----")
                (map-to-links-list (cdr x) (1+ count))))))

;; ======================================================================

;; Non-RTZ two-phase handshake.

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

;; RTZ two-phase handshake.

(defun rtz-fullp (sw)
  (declare (xargs :guard t))
  (equal sw t))

(defun rtz-emptyp (sw)
  (declare (xargs :guard t))
  (equal sw nil))

(defun fullp (link)
  (declare (xargs :guard t))
  (equal link '((t))))

(defun emptyp (link)
  (declare (xargs :guard t))
  (equal link '((nil))))

(defun validp (link)
  (declare (xargs :guard t))
  (or (fullp link) (emptyp link)))

;; ======================================================================

; Joint circuit

(defconst *joint*
  '((joint
     (fin fout go)
     (act)
     ()
     ((not-fout (fout~) b-not (fout))
      (g0 (ready) b-and (fin fout~))
      (g1 (b-go) b-bool (go))
      (jact (act) b-and (ready b-go))))))

(defthmd joint-okp
  (and (net-syntax-okp *joint*)
       (net-arity-okp *joint*)))

(defund joint& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist joint))

(defun joint-act (fin fout go)
  (declare (xargs :guard t))
  (f-and (f-and fin (f-not fout))
         (f-bool go)))

(defthm joint-act-rewrite
  (and (not (joint-act nil fout go))
       (not (joint-act fin t go))
       (not (joint-act fin fout nil))))

(defthm joint-act-removes-f-buf
  (and (equal (joint-act (f-buf fin) fout go)
              (joint-act fin fout go))
       (equal (joint-act fin (f-buf fout) go)
              (joint-act fin fout go))
       (equal (joint-act fin fout (f-buf go))
              (joint-act fin fout go)))
  :hints (("Goal" :in-theory (enable f-buf-delete-lemmas-2))))

(defthmd joint$value
  (implies (joint& netlist)
           (equal (se 'joint (list fin fout go) sts netlist)
                  (list (joint-act fin fout go))))
  :hints (("Goal" :in-theory (enable* se-rules joint&))))

(in-theory (disable joint-act))

;; ======================================================================

; Click link control circuit

(defconst *click-link*
  '((click-link
     (fi dr)
     (ls)
     (ff0 ff1)
     ((ff0 (req req~) fd1 (fi r))
      (ff1 (ack ack~) fd1 (dr a))
      (g0 (ls) b-xor (req ack))
      (g1 (r) b-not (req))
      (g2 (a) b-not (ack))))))

(defthmd click-link-okp
  (and (net-syntax-okp *click-link*)
       (net-arity-okp *click-link*)))

(defund click-link& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist click-link))

(defthmd click-link$value
  (implies (click-link& netlist)
           (equal (se 'click-link (list fi dr) (list ff0 ff1) netlist)
                  (list (f-xor (car ff0) (car ff1)))))
  :hints (("Goal" :in-theory (enable* se-rules
                                      click-link&
                                      f-gates))))

(defthmd click-link$state
  (implies (click-link& netlist)
           (equal (de 'click-link (list fi dr) (list ff0 ff1) netlist)
                  (list (list (f-if fi
                                    (f-not (car ff0))
                                    (car ff0)))
                        (list (f-if dr
                                    (f-not (car ff1))
                                    (car ff1))))))
  :hints (("Goal" :in-theory (enable* de-rules
                                      click-link&
                                      f-gates))))

;; ======================================================================

; SR-link circuit

(defconst *sr-link*
  '((sr-link
     (fi dr)
     (ls)
     (sr-st)
     ((sr-st (ls ls~) sr (fi dr))))))

(defthmd sr-link-okp
  (and (net-syntax-okp *sr-link*)
       (net-arity-okp *sr-link*)))

(defund sr-link& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist sr-link))

(defthmd sr-link$value
  (implies (sr-link& netlist)
           (equal (se 'sr-link ins sts netlist)
                  (list (f-buf (caar sts)))))
  :hints (("Goal" :in-theory (enable* se-rules sr-link&))))

(defthmd sr-link$state
  (implies (sr-link& netlist)
           (equal (de 'sr-link (list fi dr) sts netlist)
                  (list (list (f-sr fi dr (caar sts))))))
  :hints (("Goal" :in-theory (enable* de-rules sr-link&))))

;; ======================================================================

(defun or-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (or (car x)
        (or-list (cdr x)))))

(defconst *link*
  '((link
     (fi dr)
     (ls)
     (sr-st)
     ((sr-st (ls ls~) sr (fi dr))))))

(defthmd link-okp
  (and (net-syntax-okp *link*)
       (net-arity-okp *link*)))

(defund link& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist link))

(defthmd link$value
  (implies (link& netlist)
           (equal (se 'link ins sts netlist)
                  (list (f-buf (caar sts)))))
  :hints (("Goal" :in-theory (enable* se-rules link&))))

(defthmd link$state
  (implies (link& netlist)
           (equal (de 'link (list fi dr) sts netlist)
                  (list (list (f-sr fi dr (caar sts))))))
  :hints (("Goal" :in-theory (enable* de-rules link&))))


