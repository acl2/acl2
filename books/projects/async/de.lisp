;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Warren A. Hunt, Jr. and Cuong Chau
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>
;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2018

; (ld "de.lisp" :ld-pre-eval-print t)

; This collection of things we need to define ACL2 version of DUAL-EVAL.

; !!! Should CONSP-N and TRUE-LISTP-AT-LEAST-N be exchanged for
; (and (TRUE-LISTP x) (= (LEN x) n))?

(in-package "ADE")

(include-book "assoc-eq-value")
(include-book "f-functions")
(include-book "macros")
(include-book "primp-database")

(include-book "tools/flag" :dir :system)

;; ======================================================================

;;;  Macros to simplify specifications.

(defmacro consp-n (x n)
  (declare (xargs :guard (natp n)))
  (if (<= n 0)
      ''t
    (if (= n 1)
        `(consp ,x)
      (list 'and
            `(consp ,x)
            `(consp-n (cdr ,x) ,(- n 1))))))

(defmacro true-listp-at-least-n (x n)
  (declare (xargs :guard (natp n)))
  (list 'and
        (list 'true-listp `,x)
        `(consp-n ,x ,n)))

;; This has to be connected to SE and DE below!!!

(defun primp-call-syntaxp (fn ins sts)
  (declare (xargs :guard t))
  (and (symbolp fn)
       (primp fn)
       (true-listp ins)
       (true-listp sts)))

(defun primp-call-arityp (fn ins sts)
  (declare (xargs :guard (primp-call-syntaxp fn ins sts)))
  (and (= (primp-ins fn) (len ins))
       (= (primp-sts fn) (len sts))))

(defun se-primp-apply (fn ins sts)
  (declare (xargs :guard (and (primp-call-syntaxp fn ins sts)
                              (primp-call-arityp  fn ins sts))))
  (case fn
    (b-and       (list (f-and  (car ins) (cadr ins))))
    (b-and3      (list (f-and3 (car ins) (cadr ins) (caddr ins))))
    (b-and4      (list (f-and4 (car ins) (cadr ins)
                               (caddr ins) (cadddr ins))))
    (b-and5      (list (f-and5 (car ins) (cadr ins)
                               (caddr ins) (cadddr ins)
                               (car (cddddr ins)))))
    (b-bool      (list (f-bool (car ins))))
    (b-buf       (list (f-buf  (car ins))))
    (b-equv      (list (f-equv (car ins) (cadr ins))))
    (b-if        (list (f-if (car ins) (cadr ins) (caddr ins))))
    (b-nand      (list (f-nand (car ins) (cadr ins))))
    (b-nand3     (list (f-nand3 (car ins) (cadr ins) (caddr ins))))
    (b-nand4     (list (f-nand4 (car ins) (cadr ins)
                                (caddr ins) (cadddr ins))))
    (b-nand5     (list (f-nand5 (car ins) (cadr ins)
                                (caddr ins) (cadddr ins)
                                (car (cddddr ins)))))
    (b-nand6     (list (f-nand6 (car ins) (cadr ins)
                                (caddr ins) (cadddr ins)
                                (car (cddddr ins)) (cadr (cddddr ins)))))
    (b-nand8     (list (f-nand8 (car ins) (cadr ins)
                                (caddr ins) (cadddr ins)
                                (car (cddddr ins)) (cadr (cddddr ins))
                                (caddr (cddddr ins)) (cadddr (cddddr ins)))))
    (b-nor       (list (f-nor  (car ins) (cadr ins))))
    (b-nor3      (list (f-nor3 (car ins) (cadr ins) (caddr ins))))
    (b-nor4      (list (f-nor4 (car ins) (cadr ins)
                               (caddr ins) (cadddr ins))))
    (b-nor5      (list (f-nor5 (car ins) (cadr ins)
                               (caddr ins) (cadddr ins)
                               (car (cddddr ins)))))
    (b-nor6      (list (f-nor6 (car ins) (cadr ins)
                               (caddr ins) (cadddr ins)
                               (car (cddddr ins)) (cadr (cddddr ins)))))
    (b-nor8      (list (f-nor8 (car ins) (cadr ins)
                               (caddr ins) (cadddr ins)
                               (car (cddddr ins)) (cadr (cddddr ins))
                               (caddr (cddddr ins)) (cadddr (cddddr ins)))))
    (b-not       (list (f-not  (car ins))))
    (b-or        (list (f-or   (car ins) (cadr ins))))
    (b-or3       (list (f-or3  (car ins) (cadr ins) (caddr ins))))
    (b-or4       (list (f-or4  (car ins) (cadr ins)
                               (caddr ins) (cadddr ins))))
    (b-or5       (list (f-or5  (car ins) (cadr ins)
                               (caddr ins) (cadddr ins)
                               (car (cddddr ins)))))
    (b-xnor      (list (f-xnor (car ins) (cadr ins))))
    (b-xor       (list (f-xor  (car ins) (cadr ins))))

    (fd1         (list (f-buf (car sts))
                       (f-not (car sts))))
    (latch       (list (f-if (car ins)
                             (cadr ins)
                             (car sts))
                       (f-if (car ins)
                             (f-not (cadr ins))
                             (f-not (car sts)))))

    ;; LINK-CNTL is a new primitive for modeling self-timed modules using the
    ;; link-joint model.
    (link-cntl   (list (f-buf (car sts))))

    (pullup      (list (f-pullup (car ins))))
    (t-buf       (list (ft-buf (car ins) (cadr ins))))
    (t-wire      (list (ft-wire (car ins) (cadr ins))))
    (vdd         (list T))
    (vss         (list NIL))
    (wire        (list (car ins)))

    (otherwise   nil)))

(defun de-primp-apply (fn ins sts)
  (declare (xargs :guard (and (primp-call-syntaxp fn ins sts)
                              (primp-call-arityp  fn ins sts))))
  (case fn
    (fd1       (list (f-if (car ins) (cadr ins) (car sts))))
    (latch     (list (f-if (car ins) (cadr ins) (car sts))))

    ;; LINK-CNTL is a new primitive for modeling self-timed modules using the
    ;; link-joint model.
    (link-cntl (list (f-sr (car ins) (cadr ins) (car sts))))

    (otherwise nil)))

(defun len-se-primp-apply (fn ins sts)
  (declare (xargs :guard t)
           (ignore ins sts))
  (case fn
    ((fd1 latch) 2)
    (otherwise   1)))

(defun len-de-primp-apply (fn ins sts)
  (declare (xargs :guard (true-listp ins))
           (ignore ins sts))
  (case fn
    ((fd1 latch link-cntl) 1)
    (otherwise             0)))

(defthm len-de-primp-apply-lemma
  (equal (len (de-primp-apply fn ins sts))
         (len-de-primp-apply fn ins sts)))

(in-theory (disable se-primp-apply de-primp-apply))

; We now define the DE language.  This is a derivative from the
; DUAL-EVAL language.  The DE language is designed to be simple,
; suitable for teaching, and for performing experiments.

; A module is the representation of a non-primitive FSM.  It is
; composed of five elements: name, inputs, outputs, states, and
; occurrences.  Each occurrence is itself composed of four pieces:
; name, outputs, primitive or module reference, and inputs.  The
; following macros are the destructor operations for accessing the
; various pieces of a module.

(deflabel md-accessors-defuns-section)

(defun-inline md-name   (x)
  (declare (xargs :guard (consp-n x 1)))
  (car x))

(defun-inline md-ins    (x)
  (declare (xargs :guard (consp-n x 2)))
  (cadr x))

(defun-inline md-outs   (x)
  (declare (xargs :guard (consp-n x 3)))
  (caddr x))

(defun-inline md-sts    (x)
  (declare (xargs :guard (consp-n x 4)))
  (cadddr x))

(defun-inline md-occs   (x)
  (declare (xargs :guard (consp-n x 5)))
  (car (cddddr x)))

(deftheory md-accessors-defuns
  (set-difference-theories (current-theory :here)
			   (current-theory 'md-accessors-defuns-section)))

(deflabel occ-accessors-defuns-section)

(defun-inline occ-name  (x)
  (declare (xargs :guard (consp-n x 1)))
  (car x))

(defun-inline occ-outs  (x)
  (declare (xargs :guard (consp-n x 2)))
  (cadr x))

(defun-inline occ-fn    (x)
  (declare (xargs :guard (consp-n x 3)))
  (caddr x))

(defun-inline occ-ins   (x)
  (declare (xargs :guard (consp-n x 4)))
  (cadddr x))

(deftheory occ-accessors-defuns
  (set-difference-theories (current-theory :here)
			   (current-theory 'occ-accessors-defuns-section)))

;  We define the syntactic restrictions for occurrences and modules.

(defun occ-syntax-okp (occ)
  (declare (xargs :guard t))
  (and (true-listp-at-least-n occ 4)
       (let ((occ-name (occ-name occ))
             (occ-outs (occ-outs occ))
             (occ-fn   (occ-fn   occ))
             (occ-ins  (occ-ins  occ)))
         (and (symbolp           occ-name)
              (symbol-listp      occ-outs)
              (no-duplicatesp-eq occ-outs)
              (symbolp           occ-fn)
              (symbol-listp      occ-ins)))))

(defun occs-syntax-okp (occs)
  (declare (xargs :guard t))
  (if (atom occs)
      (eq occs nil)
    (and (occ-syntax-okp (car occs))
         (occs-syntax-okp (cdr occs)))))

(defthm occs-syntax-okp-forward-symbol-alistp
  (implies (occs-syntax-okp occs)
           (symbol-alistp occs))
  :rule-classes :forward-chaining)

(defun module-syntax-okp (module)
  (declare (xargs :guard t))
  (and (true-listp-at-least-n module 5)
       (let ((md-name  (md-name  module))
             (md-ins   (md-ins   module))
             (md-outs  (md-outs  module))
             (md-sts   (md-sts   module))
             (md-occs  (md-occs  module)))
         (and
          (symbolp           md-name)
          ;; Inputs
          (symbol-listp      md-ins)
          (no-duplicatesp-eq md-ins)
          ;; Outputs
          (symbol-listp      md-outs)
          (no-duplicatesp-eq md-outs)
          ;; No degenerative modules
          (or (consp         md-ins)   ; Module must have at least
              (consp         md-outs)) ; one input or one output
          ;; Occurrences
          (occs-syntax-okp   md-occs)
          (no-duplicatesp-eq (strip-cars md-occs))
          ;; States
          (symbol-listp      md-sts)
          (no-duplicatesp-eq md-sts)
          ;; State names subset of Occurrence names
          (subsetp md-sts (strip-cars md-occs))
          ))))

(defun net-syntax-okp (netlist)
  (declare (xargs :guard t
                  :verify-guards nil))
  (if (atom netlist)
      (null netlist)
    (let* ((module (car netlist))
           (rest-netlist (cdr netlist)))
      (and
       (module-syntax-okp module)
       (let ((module-name (car module)))
         (and (net-syntax-okp rest-netlist)
              (not (primp module-name))    ; Module name is not a primitive
              (not (assoc-eq module-name   ; nor previously defined module
                             rest-netlist))))))))

; Some facts about our netlist syntax

(defthm net-syntax-okp-forward-to-symbol-alistp
  ;; For effeciency, this lemms before guard proof for NET-SYNTAX-OKP
  (implies (net-syntax-okp x)
           (symbol-alistp x))
  :rule-classes :forward-chaining)

(verify-guards net-syntax-okp)

(defthm net-syntax-okp-delete-to-eq-netlist
  (implies (net-syntax-okp netlist)
           (net-syntax-okp (delete-to-eq fn netlist))))

(defthmd assoc-eq-of-non-fn-netlist
  (implies (and (net-syntax-okp netlist)
		(atom (assoc-eq fn netlist)))
           (equal (assoc-eq fn netlist) nil)))

(defthm symbol-listp-md-of-ins-outs-and-sts
  (implies (and (net-syntax-okp netlist)
                (consp (assoc-equal fn netlist)))
           (and (symbol-listp (md-ins (assoc-equal fn netlist)))
                (symbol-listp (md-outs (assoc-equal fn netlist)))
                (symbol-listp (md-sts (assoc-eq fn netlist)))))
  :hints (("Goal" :induct (assoc-equal fn netlist))))

(defthm net-syntax-okp->module-syntax-okp
  (implies (and (net-syntax-okp netlist)
                (consp (assoc-equal fn netlist)))
           (module-syntax-okp (assoc-equal fn netlist)))
  :hints (("Goal" :in-theory (disable module-syntax-okp)))
  :rule-classes (:rewrite :type-prescription))

; Facts that would be expensive to have around because of the function
; symbols involved on the left-hand side, so we globaly disable them
; and enable them when appropriate.

(defthmd consp-assoc-eq-fn-of-non-empty-netlist
  (implies (and (net-syntax-okp netlist)
		(not (atom (assoc-eq fn netlist))))
	   (and (consp (assoc-eq fn netlist))
		(consp (cdr (assoc-eq fn netlist)))
		(consp (cddr (assoc-eq fn netlist)))
		(consp (cdddr (assoc-eq fn netlist)))
		(consp (cddddr (assoc-eq fn netlist)))))
  :hints (("Goal" :induct (assoc-equal fn netlist))))

;  Arity Recognizer

(defun occ-arity-okp (occ netlist)
  (declare (xargs :guard (and (net-syntax-okp netlist)
                              (occ-syntax-okp occ))
                  :guard-hints
                  (("Goal" :in-theory
                    (enable consp-assoc-eq-fn-of-non-empty-netlist)))))
  (let* ((occ-outs (occ-outs occ))
         (occ-fn   (occ-fn   occ))
         (occ-ins  (occ-ins  occ))
         (primp    (primp occ-fn))
         (len-ins  (len occ-ins))
         (len-outs (len occ-outs)))
    (if primp
        (and (= (primp-ins  occ-fn) len-ins)
             (= (primp-outs occ-fn) len-outs))
      (let ((module (assoc-eq occ-fn netlist)))
        (if (atom module)
            nil
          (and (= (len (md-ins  module)) len-ins)
               (= (len (md-outs module)) len-outs)))))))

(defun occs-arity-okp (occs netlist)
  (declare (xargs :guard (and (net-syntax-okp netlist)
                              (occs-syntax-okp occs))
                  :guard-hints
                  (("Goal" :in-theory (disable occ-syntax-okp)))))
  (if (atom occs)
      t
    (and (occ-arity-okp (car occs) netlist)
         (occs-arity-okp (cdr occs) netlist))))

(defun net-arity-okp (netlist)
  (declare (xargs :guard (net-syntax-okp netlist)))
  (if (atom netlist)
      t
    (let* ((module      (car netlist))
           (cdr-netlist (cdr netlist))
           (md-name     (md-name module)))
      (and (not (assoc-eq md-name cdr-netlist))  ; No self-referential modules
           (net-arity-okp cdr-netlist)           ; Check all inferior modules
           (occs-arity-okp (md-occs module)      ; For each occurrence, check
                           cdr-netlist)))))      ; its arity

(in-theory (disable occ-accessors-defuns md-accessors-defuns))

(defthm net-arity-okp-of-delete-to-eq
  (implies (net-arity-okp netlist)
           (net-arity-okp (delete-to-eq fn netlist))))

(defthm occs-syntax-okp-md-occs-assoc-eq-fn-netlist
  ;; Silly rule?  If the ASSOC-EQ is NIL, then MD-OCCS is NIL
  (implies (net-syntax-okp netlist)
           (occs-syntax-okp (md-occs (assoc-eq fn netlist))))
  :hints (("Goal"
           :in-theory (enable md-occs)
           :induct (assoc-eq fn netlist))))

(in-theory (disable net-syntax-okp))

(defthm occs-arity-okp-md-occs-assoc-eq-fn-netlist
  (implies (and (net-arity-okp netlist)
                (assoc-eq fn netlist))
           (occs-arity-okp (md-occs (assoc-eq fn netlist))
                           (delete-to-eq fn netlist))))


; Measure for the netlist evaluation functions

(defthm len-fn-delete-to-eq
  (implies (or (consp netlist)
               (consp (assoc-eq fn netlist)))
           (and (< (len (delete-to-eq fn netlist))
                   (len netlist))
                (< (+ 1 (len (delete-to-eq fn netlist)))
                   (+ 1 (len netlist)))))
  :rule-classes (:linear :rewrite))


; The measure function for the DE recursions.

(defun se-measure (fn-or-occurs netlist)
  (declare (xargs :guard t))
  (make-ord (1+ (len netlist))
            1
            (acl2-count fn-or-occurs)))

(defthm acl2-count-of-occs-fn-car-occs
  (implies (consp (double-rewrite occs))
           (< (acl2-count (occ-fn (car occs)))
              (acl2-count occs)))
  :hints (("Goal" :in-theory (enable occ-fn)))
  :rule-classes (:rewrite :linear))

(defun sts-okp-guard (fn sts)
  (declare (xargs :guard t))
   (and (symbolp fn)
        (true-listp sts)))

(defun sts-occs-okp-guard (occs sts-alist netlist)
  (declare (xargs :guard (net-syntax-okp netlist)))
  (and (symbol-alistp sts-alist)
       (occs-syntax-okp occs)
       (occs-arity-okp occs netlist)
       (no-duplicatesp-eq (strip-cars occs))
       ;;What about adding (no-duplicatesp-eq (strip-cars sts-alist)) ?
       ))

; The STS-OKP and STS-OCC-OKP functions check structure of state
; argument.  These functions are intended to make assure that the STS
; argument is "isomorphic" to the way it will be destructured by the
; SE, SE-OCC interpreter.

(mutual-recursion

 (defun sts-okp (fn sts netlist)
   (declare (xargs :measure (se-measure fn netlist)
                   :guard (and (net-syntax-okp netlist)
                               (net-arity-okp netlist)
                               (sts-okp-guard fn sts))
                   :guard-hints
                   (("Goal"
                     :use net-syntax-okp->module-syntax-okp
                     :in-theory (disable assoc-equal
                                         alistp
                                         symbol-alistp
                                         symbol-listp)))))
   (if (primp fn)
       (= (primp-sts fn) (len sts))
     (let ((module (assoc-eq fn netlist)))
       (if (atom module)
           nil
         (let* ((md-sts     (md-sts   module))
                (md-occs    (md-occs  module))
                (sts-alist  (pairlis$ md-sts sts)))
           (and (= (len md-sts) (len sts))
                (sts-occs-okp md-occs sts-alist
                              (delete-to-eq fn netlist))))))))

 (defun sts-occs-okp (occs sts-alist netlist)
   (declare (xargs :measure (se-measure occs netlist)
                   :guard (and (net-syntax-okp netlist)
                               (net-arity-okp netlist)
                               (sts-occs-okp-guard occs sts-alist netlist))))
   (if (atom occs)
       t
     (let* ((occur    (car occs))
            (occ-name (occ-name occur))
            (occ-fn   (occ-fn   occur))
            (sts      (assoc-eq-value occ-name sts-alist)))
       (and (true-listp sts)
            (sts-okp occ-fn sts netlist)
            (sts-occs-okp (cdr occs) sts-alist netlist))))))

(defthm sts-occs-okp-update-alist
  (implies (not (member occ-name (strip-cars occs)))
           (equal (sts-occs-okp occs
                         (update-alist occ-name sts sts-alist)
                         netlist)
                  (sts-occs-okp occs sts-alist netlist)))
  :hints (("Goal"
           :in-theory (enable occ-name))
          ("Subgoal *1/3"
           :expand (sts-occs-okp occs
                                 (update-alist occ-name sts sts-alist)
                                 netlist))))


;                              DE

; This is an attempt to define the DE interpreter which is similar in
; spirit to the NQTHM version of DUAL-EVAL language.  We define the DE
; syntax recognizer and the DE semantic interpreter.  The DE language
; recognizer is actually a litany of recognizers, each of which futher
; constrain the language.

; This DE language is designed to represent FSMs, thus the primitives
; are themselves FSMs.  To evaluate a module requires its inputs and
; its state (combinational-only modules do not have a state).  We
; require a module to have at least one input or one output.

; The name DUAL-EVAL is derived from the fact that DUAL-EVAL (DE)
; requires two inputs (the current inputs and state), produces two
; outputs (the outputs and the next state), and it requires two passes
; to compute the result.  We actually define two pairs of mutually
; recursive functions: SE (Single Eval) and DE (Dual-Eval).  SE
; computes the "wire" values for a module, and DE computes the next
; state value after calling SE to get the wire values.


(defun se-ins-guard (fn ins netlist)
  (declare (xargs :guard (net-syntax-okp netlist)
                  :guard-hints
                  (("Goal" :in-theory (e/d (consp-assoc-eq-fn-of-non-empty-netlist)
                                           (md-occs md-sts))))))
  (and (symbolp fn)
       (true-listp ins)
       ;; Check form of top-level INS argument
       (if (primp fn)
           (equal (primp-ins fn) (len ins))
         (if (assoc-eq fn netlist)
             (equal (len (md-ins (assoc-eq fn netlist)))
                    (len ins))
           nil))))

(defun se-guard (fn ins sts netlist)
  (declare (xargs :guard t))
  (and (net-syntax-okp netlist)
       (net-arity-okp netlist)
       (sts-okp-guard fn sts)
       (sts-okp fn sts netlist)
       (se-ins-guard fn ins netlist)))

(defun se-occ-guard (occs wire-alist sts-alist netlist)
  (declare (xargs :guard t))
  (and (net-syntax-okp netlist)
       (net-arity-okp netlist)
       (sts-occs-okp-guard occs sts-alist netlist)
       (sts-occs-okp occs sts-alist netlist)
       ;; Check form of WIRE-ALIST
       (symbol-alistp wire-alist)
       ;; Likely need to know that WIRE-ALIST has values for all inputs
       ))

(mutual-recursion

 (defun se (fn ins sts netlist)
   (declare (xargs :measure (se-measure fn netlist)
                   :guard (se-guard fn ins sts netlist)
                   :verify-guards nil))
   (if (primp fn)
       (se-primp-apply fn ins sts)
     (let ((module (assoc-eq fn netlist)))
       (if (atom module)
           nil
         (let* ((md-ins     (md-ins   module))
                (md-outs    (md-outs  module))
                (md-sts     (md-sts   module))
                (md-occs    (md-occs  module))
                (wire-alist (pairlis$ md-ins ins))
                (sts-alist  (pairlis$ md-sts sts)))
           (assoc-eq-values
            md-outs
            (se-occ md-occs wire-alist sts-alist
                    (delete-to-eq fn netlist))))))))

 (defun se-occ (occs wire-alist sts-alist netlist)
   (declare (xargs :measure (se-measure occs netlist)
                   :guard (se-occ-guard occs wire-alist sts-alist netlist)
                   :verify-guards nil))
   (if (atom occs)
       wire-alist
     (let* ((occur     (car occs))
            (occ-name  (occ-name occur))
            (occ-outs  (occ-outs occur))
            (occ-fn    (occ-fn   occur))
            (occ-ins   (occ-ins  occur))
            (ins       (assoc-eq-values occ-ins wire-alist))
            (sts       (assoc-eq-value  occ-name sts-alist))
            (new-vals  (se occ-fn ins sts netlist))
            (new-alist (pairlis$ occ-outs new-vals))
            (new-wire-alist
             (append new-alist wire-alist)))
       (se-occ (cdr occs) new-wire-alist sts-alist netlist)))))

(mutual-recursion

 (defun de (fn ins sts netlist)
   (declare (xargs :measure (se-measure fn netlist)
                   :guard (se-guard fn ins sts netlist)
                   :verify-guards nil))
   (if (primp fn)
       (de-primp-apply fn ins sts)
     (let ((module (assoc-eq fn netlist)))
       (if (atom module)
           nil
         (let* ((md-ins      (md-ins   module))
                (md-sts      (md-sts   module))
                (md-occs     (md-occs  module))
                (wire-alist  (pairlis$ md-ins ins))
                (sts-alist   (pairlis$ md-sts sts))
                (new-netlist (delete-to-eq fn netlist)))
           (assoc-eq-values
            md-sts
            (de-occ md-occs
                    (se-occ md-occs wire-alist sts-alist new-netlist)
                    sts-alist new-netlist)))))))

 (defun de-occ (occs wire-alist sts-alist netlist)
   (declare (xargs :measure (se-measure occs netlist)
                   :guard (se-occ-guard occs wire-alist sts-alist netlist)
                   :verify-guards nil))
   (if (atom occs)
       sts-alist
     (let* ((occur    (car occs))
            (occ-name (occ-name occur))
            (occ-fn   (occ-fn   occur))
            (occ-ins  (occ-ins  occur))
            (ins      (assoc-eq-values occ-ins  wire-alist))
            (sts-pair (assoc-eq        occ-name sts-alist))
            (sts      (mbe :logic (assoc-eq-value occ-name sts-alist)
                           :exec  (cdr sts-pair)))
            (new-sts-alist
             (mbe :logic (update-alist occ-name
                                       (de occ-fn ins sts netlist)
                                       sts-alist)
                  :exec (if (atom sts-pair)
                            sts-alist
                          (update-alist occ-name
                                        (de occ-fn ins sts netlist)
                                        sts-alist)))))
       (de-occ (cdr occs) wire-alist new-sts-alist netlist)))))

; se lemmas

(defthmd open-se
  (and
   (implies (primp fn)
            (equal (se fn ins sts netlist)
                   (se-primp-apply fn ins sts)))
   (implies (not (primp fn))
            (equal (se fn ins sts netlist)
                   (let ((module (assoc-eq fn netlist)))
                     (if (atom module)
                         nil
                       (let* ((md-ins (md-ins module))
                              (md-outs (md-outs module))
                              (md-sts (md-sts module))
                              (md-occs (md-occs module))
                              (wire-alist (pairlis$ md-ins ins))
                              (sts-alist (pairlis$ md-sts sts)))
                         (assoc-eq-values
                          md-outs
                          (se-occ md-occs wire-alist sts-alist
                                  (delete-to-eq fn netlist))))))))))

(defun se-occ-induct (occs wire-alist sts-alist netlist)
  ;; Need this because "induction machine" for SE-OCC is involved with
  ;; a mutual recursion; this definition is stand alone.
  (declare (ignorable sts-alist netlist))
  (if (atom occs)
      wire-alist
    (let* ((occur     (car occs))
           (occ-name  (occ-name occur))
           (occ-outs  (occ-outs occur))
           (occ-fn    (occ-fn   occur))
           (occ-ins   (occ-ins  occur))
           (ins       (assoc-eq-values occ-ins  wire-alist))
           (sts       (assoc-eq-value  occ-name sts-alist))
           (new-vals  (se occ-fn ins sts netlist))
           (new-alist (pairlis$ occ-outs new-vals))
           (new-wire-alist
            (append new-alist wire-alist)))
      (se-occ-induct (cdr occs) new-wire-alist sts-alist netlist))))

(encapsulate
 ()

 (local
  (defthm symbol-alistp-fact-append-cons
    (implies (and (symbolp sym)
                  (symbol-alistp sym-alist)
                  (symbol-alistp first-sym-alist))
             (symbol-alistp (append first-sym-alist
                                    (cons (cons sym anything)
                                          sym-alist))))))

 (local
  (defthm symbol-alistp-fact-append-pairlis$
    (implies (and (symbol-alistp wire-alist)
                  (consp (double-rewrite occs))
                  (occs-syntax-okp occs))
             (symbol-alistp (append (pairlis$ (occ-outs (car occs))
                                              anything)
                                    wire-alist)))))

 (defthm symbol-alistp-se-occ
   (implies (and (symbol-alistp wire-alist)
                 (occs-syntax-okp occs))
            (and (alistp (se-occ occs wire-alist sts-alist netlist))
                 (symbol-alistp (se-occ occs wire-alist sts-alist netlist))))
   :hints
   (("Goal"
     :induct (se-occ-induct occs wire-alist sts-alist netlist)
     :in-theory (disable symbol-alistp occ-outs
                         occ-arity-okp occs-arity-okp)))))

(local
 (defthm symbol-listp=>true-listp
   (implies (symbol-listp x)
            (true-listp x))))

(verify-guards se
  ;;:guard-debug t
  :hints (("Subgoal 2" :use net-syntax-okp->module-syntax-okp)))

(make-event
 `(progn
    ,@(primitives-lemmas-gen
       'se
       '((b-and       (list (f-and  (car ins) (cadr ins))))
         (b-and3      (list (f-and3 (car ins) (cadr ins) (caddr ins))))
         (b-and4      (list (f-and4 (car ins) (cadr ins)
                                    (caddr ins) (cadddr ins))))
         (b-and5      (list (f-and5 (car ins) (cadr ins)
                                    (caddr ins) (cadddr ins)
                                    (car (cddddr ins)))))
         (b-bool      (list (f-bool (car ins))))
         (b-buf       (list (f-buf  (car ins))))
         (b-equv      (list (f-equv (car ins) (cadr ins))))
         (b-if        (list (f-if (car ins) (cadr ins) (caddr ins))))
         (b-nand      (list (f-nand (car ins) (cadr ins))))
         (b-nand3     (list (f-nand3 (car ins) (cadr ins) (caddr ins))))
         (b-nand4     (list (f-nand4 (car ins) (cadr ins)
                                     (caddr ins) (cadddr ins))))
         (b-nand5     (list (f-nand5 (car ins) (cadr ins)
                                     (caddr ins) (cadddr ins)
                                     (car (cddddr ins)))))
         (b-nand6     (list (f-nand6 (car ins) (cadr ins)
                                     (caddr ins) (cadddr ins)
                                     (car (cddddr ins)) (cadr (cddddr ins)))))
         (b-nand8     (list (f-nand8 (car ins) (cadr ins)
                                     (caddr ins) (cadddr ins)
                                     (car (cddddr ins)) (cadr (cddddr ins))
                                     (caddr (cddddr ins)) (cadddr (cddddr ins)))))
         (b-nor       (list (f-nor  (car ins) (cadr ins))))
         (b-nor3      (list (f-nor3 (car ins) (cadr ins) (caddr ins))))
         (b-nor4      (list (f-nor4 (car ins) (cadr ins)
                                    (caddr ins) (cadddr ins))))
         (b-nor5      (list (f-nor5 (car ins) (cadr ins)
                                    (caddr ins) (cadddr ins)
                                    (car (cddddr ins)))))
         (b-nor6      (list (f-nor6 (car ins) (cadr ins)
                                    (caddr ins) (cadddr ins)
                                    (car (cddddr ins)) (cadr (cddddr ins)))))
         (b-nor8      (list (f-nor8 (car ins) (cadr ins)
                                    (caddr ins) (cadddr ins)
                                    (car (cddddr ins)) (cadr (cddddr ins))
                                    (caddr (cddddr ins)) (cadddr (cddddr ins)))))
         (b-not       (list (f-not  (car ins))))
         (b-or        (list (f-or   (car ins) (cadr ins))))
         (b-or3       (list (f-or3  (car ins) (cadr ins) (caddr ins))))
         (b-or4       (list (f-or4  (car ins) (cadr ins)
                                    (caddr ins) (cadddr ins))))
         (b-or5       (list (f-or5  (car ins) (cadr ins)
                                    (caddr ins) (cadddr ins)
                                    (car (cddddr ins)))))
         (b-xnor      (list (f-xnor (car ins) (cadr ins))))
         (b-xor       (list (f-xor  (car ins) (cadr ins))))

         (fd1         (list (f-buf (car sts))
                            (f-not (car sts))))
         (latch       (list (f-if (car ins)
                                  (cadr ins)
                                  (car sts))
                            (f-if (car ins)
                                  (f-not (cadr ins))
                                  (f-not (car sts)))))
         (link-cntl   (list (f-buf (car sts))))

         (pullup      (list (f-pullup (car ins))))
         (t-buf       (list (ft-buf (car ins) (cadr ins))))
         (t-wire      (list (ft-wire (car ins) (cadr ins))))
         (vdd         (list T))
         (vss         (list NIL))
         (wire        (list (car ins)))))))

; de lemmas

(defthmd open-de
  (and
   (implies (primp fn)
            (equal (de fn ins sts netlist)
                   (de-primp-apply fn ins sts)))
   (implies (not (primp fn))
            (equal (de fn ins sts netlist)
                   (let ((module (assoc-eq fn netlist)))
                     (if (atom module)
                         nil
                       (let* ((md-ins      (md-ins   module))
                              (md-sts      (md-sts   module))
                              (md-occs     (md-occs  module))
                              (wire-alist  (pairlis$ md-ins ins))
                              (sts-alist   (pairlis$ md-sts sts))
                              (new-netlist (delete-to-eq fn netlist)))
                         (assoc-eq-values
                          md-sts
                          (de-occ md-occs
                                  (se-occ md-occs wire-alist sts-alist
                                          new-netlist)
                                  sts-alist new-netlist)))))))))

(defun de-occ-induct (occs wire-alist sts-alist netlist)
  (declare (xargs :guard (and (symbol-alistp wire-alist)
                              ;; Using :guard to make formals relevant.
                              (symbol-alistp sts-alist)
                              (symbol-alistp netlist))
                  :verify-guards nil))
  (if (atom occs)
      sts-alist
    (let* ((occur    (car occs))
           (occ-name (occ-name occur))
           (occ-fn   (occ-fn   occur))
           (occ-ins  (occ-ins  occur))
           (ins      (assoc-eq-values occ-ins  wire-alist))
           (sts      (assoc-eq-value  occ-name sts-alist))
           (new-sts-alist
            (update-alist occ-name
                          (de occ-fn ins sts netlist)
                          sts-alist)))
      (de-occ-induct (cdr occs) wire-alist new-sts-alist
                     netlist))))

(encapsulate
 ()

 (local
  (defthm symbol-alistp-fact-cons
    (implies (and (symbolp sym)
                  (symbol-alistp sym-alist))
             (symbol-alistp (cons (cons sym anything)
                                  sym-alist)))))

 (local
  (defthm symbol-alistp-fact-cons-one-pair
    (implies (and (symbol-alistp wire-alist)
                  (consp (double-rewrite occs))
                  (occs-syntax-okp occs))
             (symbol-alistp (cons (cons (car (car occs)) anything)
                                  wire-alist)))
    :hints (("Goal"
             :in-theory (enable occ-name)))))

 (defthm symbol-alistp-de-occ
   (implies (and (symbol-alistp wire-alist)
                 (symbol-alistp sts-alist)
                 (occs-syntax-okp occs))
            (and (alistp (de-occ occs wire-alist sts-alist
                                 netlist))
                 (symbol-alistp (de-occ occs wire-alist sts-alist
                                        netlist))))
   :hints
   (("Goal"
     :induct (de-occ-induct occs wire-alist sts-alist netlist)
     :expand (occs-syntax-okp occs)
     :in-theory (e/d (occ-name)
                     (occ-outs symbol-alistp
                               occ-syntax-okp occs-syntax-okp))))))

(defthm update-alist-of-not-a-key
  (implies (and (alistp alist)
                (not (consp (assoc key alist))))
           (equal (update-alist key val alist)
                  alist))
  :hints (("Goal" :in-theory (enable update-alist))))

(verify-guards de
  :hints (("Goal" :in-theory (enable occ-name assoc-eq-value))
          ("Subgoal 2" :use net-syntax-okp->module-syntax-okp)))

(make-event
 `(progn
    ,@(primitives-lemmas-gen
       'de
       '((fd1       (list (f-if (car ins) (cadr ins) (car sts))))
         (latch     (list (f-if (car ins) (cadr ins) (car sts))))
         (link-cntl (list (f-sr (car ins) (cadr ins) (car sts))))))))

;; ======================================================================

;; SE-OCC-BINDINGS and DE-OCC-BINDINGS are two shorthand ways of generating the
;; binding lists when doing proofs about the bodies of modules.

(defun se-occ-bindings (n body bindings state-bindings netlist)
  (if (zp n)
      bindings
    (b* ((occurrence (car body))
         (occ-name (occ-name occurrence))
         (outputs (occ-outs occurrence))
         (fn (occ-fn occurrence))
         (inputs (occ-ins occurrence)))
      (se-occ-bindings
       (1- n)
       (cdr body)
       (append (pairlis$ outputs
                         (se fn
                             (assoc-eq-values inputs bindings)
                             (assoc-eq-value occ-name state-bindings)
                             netlist))
               bindings)
       state-bindings
       netlist))))

(defthm open-se-occ-bindings
  (and
   (implies (zp n)
            (equal (se-occ-bindings n body bindings state-bindings netlist)
                   bindings))
   (implies (not (zp n))
            (equal (se-occ-bindings n body bindings state-bindings netlist)
                   (b* ((occurrence (car body))
                        (occ-name (occ-name occurrence))
                        (outputs (occ-outs occurrence))
                        (fn (occ-fn occurrence))
                        (inputs (occ-ins occurrence)))
                     (se-occ-bindings
                      (1- n)
                      (cdr body)
                      (append (pairlis$ outputs
                                        (se fn
                                            (assoc-eq-values inputs
                                                             bindings)
                                            (assoc-eq-value occ-name
                                                            state-bindings)
                                            netlist))
                              bindings)
                      state-bindings
                      netlist))))))

(in-theory (disable se-occ-bindings))

(defun de-occ-bindings (n occs wire-alist sts-alist netlist)
  (if (zp n)
      sts-alist
    (b* ((occur    (car occs))
         (occ-name (occ-name occur))
         (occ-fn   (occ-fn   occur))
         (occ-ins  (occ-ins  occur))
         (ins      (assoc-eq-values occ-ins  wire-alist))
         (sts      (assoc-eq-value  occ-name sts-alist))
         (new-sts-alist
          (update-alist occ-name
                        (de occ-fn ins sts netlist)
                        sts-alist)))
      (de-occ-bindings
       (1- n)
       (cdr occs)
       wire-alist
       new-sts-alist
       netlist))))

(defthm open-de-occ-bindings
  (and
   (implies (zp n)
            (equal (de-occ-bindings n occs wire-alist sts-alist netlist)
                   sts-alist))
   (implies (not (zp n))
            (equal (de-occ-bindings n occs wire-alist sts-alist netlist)
                   (b* ((occur    (car occs))
                        (occ-name (occ-name occur))
                        (occ-fn   (occ-fn   occur))
                        (occ-ins  (occ-ins  occur))
                        (ins      (assoc-eq-values occ-ins  wire-alist))
                        (sts      (assoc-eq-value  occ-name sts-alist))
                        (new-sts-alist
                         (update-alist occ-name
                                       (de occ-fn ins sts netlist)
                                       sts-alist)))
                     (de-occ-bindings
                      (1- n)
                      (cdr occs)
                      wire-alist
                      new-sts-alist
                      netlist))))))

(in-theory (disable de-occ-bindings))

;; ======================================================================

(defthm len-de
  (implies (se-guard fn ins sts netlist)
           (equal (len (de fn ins sts netlist))
                  (if (primp fn)
                      (len-de-primp-apply fn ins sts)
                    (if (assoc-eq fn netlist)
                        (len (md-sts (assoc-eq fn netlist)))
                      0))))
  :hints
  (("Goal"
    :do-not-induct t
    :expand (de fn ins sts netlist))))

(defthm sts-okp-de-primp-apply
  (implies (and (primp fn)
                (se-guard fn ins sts netlist))
           (sts-okp fn (de-primp-apply fn ins sts) netlist))
  :hints
  (("Goal" :in-theory (enable de-primp-apply primp-sts primp))))

(defthm se-guard-de-primp-apply
  (implies (and (primp fn)
                (se-guard fn ins sts netlist))
           (se-guard fn ins (de-primp-apply fn ins sts) netlist))
  :hints
  (("Goal" :in-theory (enable de-primp-apply primp-sts primp))))

(defthm assoc-eq-value-de-occ
  (implies (not (member name (strip-cars occs)))
           (equal (assoc-eq-value name
                                  (de-occ occs
                                          wire-alist
                                          sts-alist
                                          netlist))
                  (assoc-eq-value name sts-alist)))
  :hints (("Goal"
           :in-theory (enable occ-name)
           :induct (de-occ-induct occs wire-alist sts-alist netlist))))

(defthm de-occ-update-alist
  (implies (and (not (member name (strip-cars occs)))
                (not (member nil (strip-cars occs))))
           (equal (de-occ occs
                          wire-alist
                          (update-alist name sts sts-alist)
                          netlist)
                  (update-alist name sts
                                (de-occ occs wire-alist sts-alist netlist))))
  :hints (("Goal"
           :in-theory (enable occ-name)
           :induct (de-occ-induct occs wire-alist sts-alist netlist))))

(defthm assoc-eq-value-de-occ-update-alist-same-name
  (implies (and (not (member name (strip-cars occs)))
                (consp (assoc-eq name sts-alist)))
           (equal (assoc-eq-value name
                                  (de-occ occs
                                          wire-alist
                                          (update-alist name sts
                                                        sts-alist)
                                          netlist))
                  sts)))

(defthm assoc-eq-value-de-occ-update-alist-diff-names
  (implies (and (not (equal name1 name2))
                (not (member name2 (strip-cars occs)))
                (not (member nil (strip-cars occs))))
           (equal (assoc-eq-value name1
                                  (de-occ occs
                                          wire-alist
                                          (update-alist name2 sts
                                                        sts-alist)
                                          netlist))
                  (assoc-eq-value name1
                                  (de-occ occs
                                          wire-alist
                                          sts-alist
                                          netlist)))))

(defthm assoc-eq-values-de-occ-update-alist
  (implies (and (not (member name names))
                (not (member name (strip-cars occs)))
                (not (member nil (strip-cars occs))))
           (equal (assoc-eq-values names
                                   (de-occ occs
                                           wire-alist
                                           (update-alist name sts sts-alist)
                                           netlist))
                  (assoc-eq-values names
                                   (de-occ occs
                                           wire-alist
                                           sts-alist
                                           netlist)))))

(in-theory (disable de-occ-update-alist))

(defthm strip-cars-de-occ
  (equal (strip-cars (de-occ occs wire-alist sts-alist
                             netlist))
         (strip-cars sts-alist))
  :hints (("Goal"
           :induct (de-occ-induct occs wire-alist sts-alist
                                  netlist))))

(make-flag flag-de ; flag function name
           de      ; any member of the clique
           ;; optional arguments:
           :flag-mapping ((de     . term)
                          (de-occ . list))
           :defthm-macro-name defthm-de
           :flag-var flag)

(local
 (defthm alistp-symbol-listp-symbol-alistp-are-true-listp
   (implies (or (alistp        lst)
                (symbol-listp  lst)
                (symbol-alistp lst))
            (true-listp lst))))

(defun well-formed-sts (fn sts netlist)
  (declare (xargs :guard t))
  (and (net-syntax-okp netlist)
       (net-arity-okp netlist)
       (sts-okp-guard fn sts)
       (sts-okp fn sts netlist)))

(defthm se-guard=>well-formed-sts
  (implies (se-guard fn ins sts netlist)
           (well-formed-sts fn sts netlist))
  :rule-classes :forward-chaining)

(defun well-formed-sts-occs (occs sts-alist netlist)
  (declare (xargs :guard t))
  (and (net-syntax-okp netlist)
       (net-arity-okp netlist)
       (sts-occs-okp-guard occs sts-alist netlist)
       (sts-occs-okp occs sts-alist netlist)))

(defthm se-occ-guard=>well-formed-sts-occs
  (implies (se-occ-guard occs wire-alist sts-alist netlist)
           (well-formed-sts-occs occs sts-alist netlist))
  :rule-classes :forward-chaining)

(local
 (defthm well-formed-sts-de<->well-formed-sts-occs-de-occ-aux
   (IMPLIES (AND (PRIMP FN)
                 (SYMBOLP FN)
                 (TRUE-LISTP STS)
                 (EQUAL (PRIMP-STS FN) (LEN STS))
                 (NOT (EQUAL FN 'FD1))
                 (NOT (EQUAL FN 'LATCH))
                 (NOT (EQUAL FN 'LINK-CNTL)))
            (EQUAL (LEN STS) 0))
   :hints (("Goal" :in-theory (enable primp)))))

(defthm well-formed-sts-de<->well-formed-sts-occs-de-occ
  (if (equal flag 'term)
      (implies (well-formed-sts fn sts netlist)
               (well-formed-sts fn (de fn ins sts netlist) netlist))
    (implies (well-formed-sts-occs occs sts-alist netlist)
             (well-formed-sts-occs occs
                                   (de-occ occs wire-alist sts-alist
                                           netlist)
                                   netlist)))
  :hints (("Goal"
           :in-theory (enable occ-name)
           :induct (flag-de flag
                            fn ins sts
                            occs wire-alist sts-alist
                            netlist))
          ("Subgoal *1/4"
           :cases ((consp (assoc (car (car occs)) sts-alist))
                   (not (consp (assoc (car (car occs)) sts-alist)))))
          ("Subgoal *1/2"
           :use net-syntax-okp->module-syntax-okp))
  :rule-classes nil)

(defthm well-formed-sts-de
  (implies (well-formed-sts fn sts netlist)
           (well-formed-sts fn (de fn ins sts netlist) netlist))
  :hints (("Goal"
           :by (:instance well-formed-sts-de<->well-formed-sts-occs-de-occ
                          (flag 'term))))
  :rule-classes (:rewrite :type-prescription))

(defthm well-formed-sts-occs-de-occ
  (implies (well-formed-sts-occs occs sts-alist netlist)
           (well-formed-sts-occs occs
                                 (de-occ occs wire-alist sts-alist
                                         netlist)
                                 netlist))
  :hints (("Goal"
           :by (:instance well-formed-sts-de<->well-formed-sts-occs-de-occ
                          (flag 'list))))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable se de))

;; ======================================================================

;; Simulation functions

(defun de-sim-guard (fn inputs-seq netlist)
  (declare (xargs :guard (net-syntax-okp netlist)))
  (if (atom inputs-seq)
      t
    (and (se-ins-guard fn (car inputs-seq) netlist)
         (de-sim-guard fn (cdr inputs-seq) netlist))))

(defun de-sim (fn inputs-seq sts netlist)
  (declare (xargs :guard (and (well-formed-sts fn sts netlist)
                              (de-sim-guard fn inputs-seq netlist))
                  :verify-guards nil))
  (if (atom inputs-seq)
      sts
    (de-sim fn
            (cdr inputs-seq)
            (de fn (car inputs-seq) sts netlist)
            netlist)))

(defthm open-de-sim-atom
  (implies (atom inputs-seq)
           (equal (de-sim fn inputs-seq sts netlist)
                  sts)))

(defthm open-de-sim
  (implies (consp inputs-seq)
           (equal (de-sim fn inputs-seq sts netlist)
                  (de-sim fn (cdr inputs-seq)
                          (de fn (car inputs-seq) sts netlist)
                          netlist))))

(in-theory (disable de-sim))

(defun de-sim-trace (fn inputs-seq sts netlist)
  (declare (xargs :guard (and (well-formed-sts fn sts netlist)
                              (de-sim-guard fn inputs-seq netlist))
                  :verify-guards nil))
  (if (atom inputs-seq)
      (list sts)
    (cons sts
          (de-sim-trace fn
                        (cdr inputs-seq)
                        (de fn (car inputs-seq) sts netlist)
                        netlist))))

(defun simulate (fn inputs-seq sts netlist)
  (declare (xargs :guard (and (well-formed-sts fn sts netlist)
                              (de-sim-guard fn inputs-seq netlist))
                  :verify-guards nil))
  (if (atom inputs-seq)
      nil
    (let ((value (se fn (car inputs-seq) sts netlist))
          (new-sts (de fn (car inputs-seq) sts netlist)))
      (cons (list value new-sts)
            (simulate fn (cdr inputs-seq) new-sts netlist)))))

(defun de-n (fn inputs-seq sts netlist n)
  (declare (xargs :guard (and (well-formed-sts fn sts netlist)
                              (de-sim-guard fn inputs-seq netlist)
                              (equal (len inputs-seq) n)
                              (natp n))
                  :verify-guards nil))
  (if (zp n)
      sts
    (de-n fn
          (cdr inputs-seq)
          (de fn (car inputs-seq) sts netlist)
          netlist
          (1- n))))

(defthm de-m+n
  (implies (and (natp m)
                (natp n))
           (equal (de-n fn inputs-seq sts netlist (+ m n))
                  (de-n fn (nthcdr m inputs-seq)
                        (de-n fn inputs-seq sts netlist m)
                        netlist
                        n)))
  :hints (("Goal"
           :induct (de-n fn inputs-seq sts netlist m))))

(defthm open-de-n-zp
  (implies (zp n)
           (equal (de-n fn inputs-seq sts netlist n)
                  sts)))

(defthm open-de-n
  (implies (not (zp n))
           (equal (de-n fn inputs-seq sts netlist n)
                  (de-n fn
                        (cdr inputs-seq)
                        (de fn (car inputs-seq) sts netlist)
                        netlist
                        (1- n)))))

(in-theory (disable de-n))

(verify-guards de-sim
 :hints (("Goal" :in-theory (disable de sts-okp))))

(verify-guards de-sim-trace
 :hints (("Goal" :in-theory (disable de sts-okp))))

(verify-guards simulate
 :hints (("Goal" :in-theory (disable se de sts-okp))))

(verify-guards de-n
 :hints (("Goal" :in-theory (disable de sts-okp))))

(in-theory (disable se-guard se-occ-guard
                    well-formed-sts well-formed-sts-occs))

;; ======================================================================

;; Defining a theory for proving value and state lemmas

(deftheory de-rules
  '(open-nth
    get-field
    len-1-true-listp=>true-listp
    nthcdr-of-pos-const-idx
    md-name md-ins md-outs md-sts md-occs
    occ-name occ-outs occ-fn occ-ins
    take-of-len-free))

;; The following theory should be disabled in order to speed up proof times
;; when proving the value and state lemmas of DE modules.

(deftheory de-module-disabled-rules
  '((si)
    (sis)
    default-car
    default-cdr
    delete-to-eq
    f-gates=b-gates
    no-duplicatesp-eq
    nth
    nthcdr
    prefixp-of-cons-left
    prefixp-when-equal-lengths
    str::iprefixp-of-cons-left
    str::istrprefixp$inline
    str::iprefixp-when-prefixp
    take
    take-redefinition
    take-of-take-split
    take-of-too-many
    v-threefix))

