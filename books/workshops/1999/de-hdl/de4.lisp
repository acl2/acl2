
;;;                          DUAL-EVAL

;;;  de4.lisp                                  Warren A. Hunt, Jr.

;;;  This is an attempt to define a new interpreter which is
;;;  similar in spirit to the NQTHM version of DUAL-EVAL.

;;;  We are going to define a recognizer and an interpreter for
;;;  this langauge.  The language recognizer is actually a litany
;;;  of recognizers, as we introduce more and more concepts as we
;;;  go along.

;;;  This language is designed to represent FSMs, thus the
;;;  primitive is itself an FSM.  Each module takes as arguments a
;;;  set of inputs and a state (combinational modules will not
;;;  have a state).  We require a module to have at least one
;;;  output, and a module will specify its next state if
;;;  appropriate.

;;;  Something to check:  is a module with an unused primary input allowed?

(in-package "ACL2")
(include-book "sts-okp")
(set-well-founded-relation e0-ord-<)

(deflabel de4-defuns-section)

;;;  We define a guard for the application of primitive evaluation
;;;  functions; that is, what are the allowable primitive applications.

(defun primp-rec (fn ins sts)
  (declare (xargs :guard t))
  (and (symbolp fn)
       (primp fn)
       (true-listp ins)
       (true-listp sts)
;       (= (len (primp-ins fn))
;	  (len ins))
;       (= (len (primp-sts fn))
;	  (len sts))
       ))

;;;  Below are primitive symbolic evaluation functions that are used
;;;  by DE to evaluate primitives.

;;;  The primitive evaluation function to compute outputs.

(defun se-primp-apply (fn ins sts)
  (declare (xargs :guard (primp-rec fn ins sts)))
  (case fn
    (gnd    (list nil))
    (vdd    (list t))

    (buf    (list (car ins)))
    (not    (list (not   (car ins))))

    (and    (list (and   (car ins) (b-fix (cadr ins)))))
    (and3   (list (and   (car ins) (cadr ins) (b-fix (caddr ins)))))
    (and4   (list (and   (car ins) (cadr ins) (caddr ins) (b-fix (cadddr ins)))))

    (or     (list (b-fix (or  (car ins) (cadr ins)))))
    (or3    (list (b-fix (or  (car ins) (cadr ins) (caddr ins)))))
    (or4    (list (b-fix (or  (car ins) (cadr ins) (caddr ins) (cadddr ins)))))

    (nand   (list (not (and (car ins) (cadr ins)))))
    (nand3  (list (not (and (car ins) (cadr ins) (caddr ins)))))
    (nand4  (list (not (and (car ins) (cadr ins) (caddr ins) (cadddr ins)))))

    (nor    (list (not (or  (car ins) (cadr ins)))))
    (nor3   (list (not (or  (car ins) (cadr ins) (caddr ins)))))
    (nor4   (list (not (or  (car ins) (cadr ins) (caddr ins) (cadddr ins)))))

    (xor    (list (xor   (car ins) (cadr ins))))

    (ff     (list (b-fix (car sts))))
    (ff2    (list (b-fix (car sts)) (b-fix (cadr sts))))

    (if     (list (if (car ins) (b-fix (cadr ins)) (b-fix (caddr ins)))))
    (otherwise nil)))


;;;  The primitive evaluation function to compute the next states.

(defun de-primp-apply (fn ins sts)
  (declare (xargs :guard (primp-rec fn ins sts))
           (ignore sts))
  (case fn
    (gnd    nil)
    (vdd    nil)

    (buf    nil)
    (not    nil)

    (and    nil)
    (and3   nil)
    (and4   nil)

    (or     nil)
    (or3    nil)
    (or4    nil)

    (nand   nil)
    (nand3  nil)
    (nand4  nil)

    (nor    nil)
    (nor3   nil)
    (nor4   nil)

    (xor    nil)

    (ff     (list (b-fix (car ins))))
    (ff2    (list (b-fix (car ins)) (b-fix (cadr ins))))

    (if     nil)
    (otherwise nil)))


;;;  The name DUAL-EVAL is derived from the fact that DUAL-EVAL (DE)
;;;  requires two inputs (the current inputs and state), produces two
;;;  outputs (the outputs and the next state), and it requires two
;;;  passes to compute the result.  We actually define two pairs of
;;;  mutually recursive functions:  SE (Single Eval) and DE
;;;  (Dual-Eval).  SE computes the "wire" values for a module, and DE
;;;  computes the next state value after calling SE to get the wire
;;;  values.

(mutual-recursion

(defun se (fn ins sts netlist)
  (declare (xargs :measure (se-measure fn netlist)))
  (if (primp fn)
      (se-primp-apply fn ins sts)
    (let ((module (assoc-eq fn netlist)))
      (if (atom module)
          nil
        (let* ((md-ins    (md-ins    module))
               (md-outs   (md-outs   module))
               (md-sts    (md-sts    module))
               (md-occs   (md-occs   module))
               (wire-alist (pairlis$ md-ins ins))
               (sts-alist  (pairlis$ md-sts sts)))
          (assoc-eq-values
           md-outs
           (se-occ md-occs wire-alist sts-alist
                   (delete-eq-module fn netlist))))))))

(defun se-occ (occurs wire-alist sts-alist netlist)
  (declare (xargs :measure (se-measure occurs netlist)))
  (if (endp occurs)
      wire-alist
    (let* ((occur    (car occurs))
           (occ-name (occ-name occur))
           (occ-outs (occ-outs occur))
           (occ-fn   (occ-fn   occur))
           (occ-ins  (occ-ins  occur))
           (ins      (assoc-eq-values occ-ins  wire-alist))
           (sts      (assoc-eq-value  occ-name sts-alist))
           (new-wire-alist
            (append
             (pairlis$ occ-outs
                       (se occ-fn ins sts netlist))
             wire-alist)))
      (se-occ (cdr occurs) new-wire-alist sts-alist netlist))))
)

(mutual-recursion

(defun de (fn ins sts netlist)
  (declare (xargs :measure (se-measure fn netlist)))
  (if (primp fn)
      (de-primp-apply fn ins sts)
    (let ((module (assoc-eq fn netlist)))
      (if (atom module)
          nil
        (let* ((md-ins      (md-ins    module))
               (md-sts      (md-sts    module))
               (md-occs     (md-occs   module))
               (wire-alist  (pairlis$ md-ins ins))
               (sts-alist   (pairlis$ md-sts sts))
               (new-netlist (delete-eq-module fn netlist)))
          (assoc-eq-values
           md-sts
           (de-occ md-occs
                   (se-occ md-occs wire-alist sts-alist new-netlist)
                   sts-alist new-netlist)))))))

(defun de-occ (occurs wire-alist sts-alist netlist)
  (declare (xargs :measure (se-measure occurs netlist)))
  (if (endp occurs)
      wire-alist
    (let* ((occur    (car occurs))
           (occ-name (occ-name occur))
           (occ-fn   (occ-fn   occur))
           (occ-ins  (occ-ins  occur))
           (ins      (assoc-eq-values occ-ins  wire-alist))
           (sts      (assoc-eq-value  occ-name sts-alist))
           (new-wire-alist
            (cons (cons occ-name (de occ-fn ins sts netlist))
                  wire-alist)))
      (de-occ (cdr occurs) new-wire-alist sts-alist netlist))))
)

(defun de-sim (fn ins-list sts netlist)
  (if (atom ins-list)
      sts
    (de-sim fn (cdr ins-list)
            (de fn (car ins-list) sts netlist)
            netlist)))



(defun map-occs-arity-okp (occs netlist)
  (declare (xargs :guard (and (occs-syntax-okp occs)
                              (net-syntax-okp netlist))))
  (if (atom occs)
      nil
    (cons (occ-arity-okp (car occs) netlist)
          (map-occs-arity-okp (cdr occs) netlist))))


(defthm se-open
  (equal (se fn ins sts netlist)
         (if (primp fn)
             (se-primp-apply fn ins sts)
           (let ((module (assoc-eq fn netlist)))
             (if (atom module)
                 nil
               (let* ((md-ins    (md-ins    module))
                      (md-outs   (md-outs   module))
                      (md-sts    (md-sts    module))
                      (md-occs   (md-occs   module))
                      (wire-alist (pairlis$ md-ins ins))
                      (sts-alist  (pairlis$ md-sts sts)))
                 (assoc-eq-values
                  md-outs
                  (se-occ md-occs wire-alist sts-alist
                          (delete-eq-module fn netlist)))))))))

(in-theory (disable se-open))

(defthm se-occ-open
  (equal (se-occ occurs wire-alist sts-alist netlist)
         (if (endp occurs)
             wire-alist
           (let* ((occur    (car occurs))
                  (occ-name (occ-name occur))
                  (occ-outs (occ-outs occur))
                  (occ-fn   (occ-fn   occur))
                  (occ-ins  (occ-ins  occur))
                  (ins      (assoc-eq-values occ-ins  wire-alist))
                  (sts      (assoc-eq-value  occ-name sts-alist))
                  (new-wire-alist
                   (append
                    (pairlis$ occ-outs
                              (se occ-fn ins sts netlist))
                    wire-alist)))
             (se-occ (cdr occurs) new-wire-alist sts-alist netlist)))))

(in-theory (disable se-occ-open))

;;;  Identify a set of symbols for this book.

(deftheory de4-section
  (set-difference-theories (current-theory :here)
			   (current-theory 'de4-defuns-section)))
