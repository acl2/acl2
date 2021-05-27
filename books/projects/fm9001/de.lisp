;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Warren Hunt and Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Warren Hunt <hunt@cs.utexas.edu>
;; Cuong Chau <ckcuong@cs.utexas.edu>
;; December 2016

; This collection of things we need to define ACL2 version of
; DUAL-EVAL.

; !!! Nathan believes that CONSP-N and TRUE-LISTP-AT-LEAST-N should
; be exchanged for (and (TRUE-LISTP x) (= (LEN x) n)).

(in-package "FM9001")

(include-book "assoc-eq-value")
(include-book "dual-port-ram")
(include-book "f-functions")
(include-book "fm9001-memory")
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
    (ao2         (list (f-nor (f-and (car ins) (cadr ins))
                              (f-and (caddr ins) (cadddr ins)))))
    (ao6         (list (f-nor (f-and (car ins) (cadr ins))
                              (caddr ins))))
    (b-and       (list (f-and  (car ins) (cadr ins))))
    (b-and3      (list (f-and3 (car ins) (cadr ins) (caddr ins))))
    (b-and4      (list (f-and4 (car ins) (cadr ins)
                               (caddr ins) (cadddr ins))))
    (b-buf       (list (f-buf  (car ins))))
    (b-equv      (list (f-equv  (car ins) (cadr ins))))
    (b-equv3     (list (f-equv3 (car ins) (cadr ins) (caddr ins))))
    (b-if        (list (f-if   (car ins) (cadr ins) (caddr ins))))
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
    (b-nbuf      (list (f-not  (car ins)) (f-buf (car ins))))
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
    (b-not-b4ip  (list (f-not  (car ins))))
    (b-or        (list (f-or   (car ins) (cadr ins))))
    (b-or3       (list (f-or3  (car ins) (cadr ins) (caddr ins))))
    (b-or4       (list (f-or4  (car ins) (cadr ins)
                               (caddr ins) (cadddr ins))))
    (b-xor       (list (f-xor  (car ins) (cadr ins))))

    (del4        (list (f-buf (car ins))))
    (procmon     (list (f-if (caddr ins)
                             (f-if (cadr ins)
                                   (f-if (car ins) NIL NIL)
                                   (car ins))
                             (cadddr ins))))
    (dp-ram-16x32 (dual-port-ram-value 32 4
                                       (list (nth 0 ins)
                                             (nth 1 ins)
                                             (nth 2 ins)
                                             (nth 3 ins)
                                             (nth 4 ins)
                                             (nth 5 ins)
                                             (nth 6 ins)
                                             (nth 7 ins)
                                             (nth 8 ins)
                                             (nth 9 ins)
                                             (nth 10 ins)
                                             (nth 11 ins)
                                             (nth 12 ins)
                                             (nth 13 ins)
                                             (nth 14 ins)
                                             (nth 15 ins)
                                             (nth 16 ins)
                                             (nth 17 ins)
                                             (nth 18 ins)
                                             (nth 19 ins)
                                             (nth 20 ins)
                                             (nth 21 ins)
                                             (nth 22 ins)
                                             (nth 23 ins)
                                             (nth 24 ins)
                                             (nth 25 ins)
                                             (nth 26 ins)
                                             (nth 27 ins)
                                             (nth 28 ins)
                                             (nth 29 ins)
                                             (nth 30 ins)
                                             (nth 31 ins)
                                             (nth 32 ins)
                                             (nth 33 ins)
                                             (nth 34 ins)
                                             (nth 35 ins)
                                             (nth 36 ins)
                                             (nth 37 ins)
                                             (nth 38 ins)
                                             (nth 39 ins)
                                             (nth 40 ins))
                                       (car sts)))

    (fd1         (list (f-buf (car sts))
                       (f-not (car sts))))
    (fd1s        (list (f-buf (car sts))
                       (f-not (car sts))))
    (fd1slp      (list (f-buf (car sts))
                       (f-not (car sts))))

    (id          (list (car ins)))
    (mem-32x32   (mem-value (list (nth 0 ins)
                                  (nth 1 ins)
                                  (nth 2 ins)
                                  (nth 3 ins)
                                  (nth 4 ins)
                                  (nth 5 ins)
                                  (nth 6 ins)
                                  (nth 7 ins)
                                  (nth 8 ins)
                                  (nth 9 ins)
                                  (nth 10 ins)
                                  (nth 11 ins)
                                  (nth 12 ins)
                                  (nth 13 ins)
                                  (nth 14 ins)
                                  (nth 15 ins)
                                  (nth 16 ins)
                                  (nth 17 ins)
                                  (nth 18 ins)
                                  (nth 19 ins)
                                  (nth 20 ins)
                                  (nth 21 ins)
                                  (nth 22 ins)
                                  (nth 23 ins)
                                  (nth 24 ins)
                                  (nth 25 ins)
                                  (nth 26 ins)
                                  (nth 27 ins)
                                  (nth 28 ins)
                                  (nth 29 ins)
                                  (nth 30 ins)
                                  (nth 31 ins)
                                  (nth 32 ins)
                                  (nth 33 ins)
                                  (nth 34 ins)
                                  (nth 35 ins)
                                  (nth 36 ins)
                                  (nth 37 ins)
                                  (nth 38 ins)
                                  (nth 39 ins)
                                  (nth 40 ins)
                                  (nth 41 ins)
                                  (nth 42 ins)
                                  (nth 43 ins)
                                  (nth 44 ins)
                                  (nth 45 ins)
                                  (nth 46 ins)
                                  (nth 47 ins)
                                  (nth 48 ins)
                                  (nth 49 ins)
                                  (nth 50 ins)
                                  (nth 51 ins)
                                  (nth 52 ins)
                                  (nth 53 ins)
                                  (nth 54 ins)
                                  (nth 55 ins)
                                  (nth 56 ins)
                                  (nth 57 ins)
                                  (nth 58 ins)
                                  (nth 59 ins)
                                  (nth 60 ins)
                                  (nth 61 ins)
                                  (nth 62 ins)
                                  (nth 63 ins)
                                  (nth 64 ins)
                                  (nth 65 ins))
                            (car sts)))
    (ram-enable-circuit  (list (f-nand (caddr ins) (cadddr ins))))

    (t-buf       (list (ft-buf (car ins) (cadr ins))))
    (t-wire      (list (ft-wire (car ins) (cadr ins))))
    (pullup      (list (f-pullup (car ins))))
    (ttl-bidirect           (list
                             (ft-buf (f-not (caddr ins)) (cadr ins))
                             (f-buf (ft-wire (car ins)
                                             (ft-buf (f-not (caddr ins))
                                                     (cadr ins))))
                             (f-nand (ft-wire (car ins)
                                              (ft-buf (f-not (caddr ins))
                                                      (cadr ins)))
                                     (cadddr ins))))
    (ttl-clk-input          (list (f-buf (car ins))
                                  (f-nand (car ins) (cadr ins))))
    (ttl-input              (list (f-buf (car ins))
                                  (f-nand (car ins) (cadr ins))))
    (ttl-output             (list (f-buf (car ins))))
    (ttl-output-parametric  (list (f-buf (car ins))))
    (ttl-output-fast        (list (f-buf (car ins))))
    (ttl-tri-output         (list (ft-buf (f-not (cadr ins)) (car ins))))
    (ttl-tri-output-fast    (list (ft-buf (f-not (cadr ins)) (car ins))))
    (vdd                    (list T))
    (vdd-parametric         (list T))
    (vss                    (list NIL))

    (otherwise   nil)))

(defun de-primp-apply (fn ins sts)
  (declare (xargs :guard (and (primp-call-syntaxp fn ins sts)
                              (primp-call-arityp  fn ins sts))))
  (case fn
    (dp-ram-16x32 (list (dual-port-ram-state 32 4
                                             (list (nth 0 ins)
                                                   (nth 1 ins)
                                                   (nth 2 ins)
                                                   (nth 3 ins)
                                                   (nth 4 ins)
                                                   (nth 5 ins)
                                                   (nth 6 ins)
                                                   (nth 7 ins)
                                                   (nth 8 ins)
                                                   (nth 9 ins)
                                                   (nth 10 ins)
                                                   (nth 11 ins)
                                                   (nth 12 ins)
                                                   (nth 13 ins)
                                                   (nth 14 ins)
                                                   (nth 15 ins)
                                                   (nth 16 ins)
                                                   (nth 17 ins)
                                                   (nth 18 ins)
                                                   (nth 19 ins)
                                                   (nth 20 ins)
                                                   (nth 21 ins)
                                                   (nth 22 ins)
                                                   (nth 23 ins)
                                                   (nth 24 ins)
                                                   (nth 25 ins)
                                                   (nth 26 ins)
                                                   (nth 27 ins)
                                                   (nth 28 ins)
                                                   (nth 29 ins)
                                                   (nth 30 ins)
                                                   (nth 31 ins)
                                                   (nth 32 ins)
                                                   (nth 33 ins)
                                                   (nth 34 ins)
                                                   (nth 35 ins)
                                                   (nth 36 ins)
                                                   (nth 37 ins)
                                                   (nth 38 ins)
                                                   (nth 39 ins)
                                                   (nth 40 ins))
                                             (car sts))))
    (fd1       (list (f-buf (car ins))))
    (fd1s      (list (f-if (cadddr ins) (caddr ins) (car ins))))
    (fd1slp    (list (f-if (car (cddddr ins))
                           (cadddr ins)
                           (f-if (caddr ins) (car ins) (car sts)))))
    (mem-32x32 (list (mem-state (list (nth 0 ins)
                                      (nth 1 ins)
                                      (nth 2 ins)
                                      (nth 3 ins)
                                      (nth 4 ins)
                                      (nth 5 ins)
                                      (nth 6 ins)
                                      (nth 7 ins)
                                      (nth 8 ins)
                                      (nth 9 ins)
                                      (nth 10 ins)
                                      (nth 11 ins)
                                      (nth 12 ins)
                                      (nth 13 ins)
                                      (nth 14 ins)
                                      (nth 15 ins)
                                      (nth 16 ins)
                                      (nth 17 ins)
                                      (nth 18 ins)
                                      (nth 19 ins)
                                      (nth 20 ins)
                                      (nth 21 ins)
                                      (nth 22 ins)
                                      (nth 23 ins)
                                      (nth 24 ins)
                                      (nth 25 ins)
                                      (nth 26 ins)
                                      (nth 27 ins)
                                      (nth 28 ins)
                                      (nth 29 ins)
                                      (nth 30 ins)
                                      (nth 31 ins)
                                      (nth 32 ins)
                                      (nth 33 ins)
                                      (nth 34 ins)
                                      (nth 35 ins)
                                      (nth 36 ins)
                                      (nth 37 ins)
                                      (nth 38 ins)
                                      (nth 39 ins)
                                      (nth 40 ins)
                                      (nth 41 ins)
                                      (nth 42 ins)
                                      (nth 43 ins)
                                      (nth 44 ins)
                                      (nth 45 ins)
                                      (nth 46 ins)
                                      (nth 47 ins)
                                      (nth 48 ins)
                                      (nth 49 ins)
                                      (nth 50 ins)
                                      (nth 51 ins)
                                      (nth 52 ins)
                                      (nth 53 ins)
                                      (nth 54 ins)
                                      (nth 55 ins)
                                      (nth 56 ins)
                                      (nth 57 ins)
                                      (nth 58 ins)
                                      (nth 59 ins)
                                      (nth 60 ins)
                                      (nth 61 ins)
                                      (nth 62 ins)
                                      (nth 63 ins)
                                      (nth 64 ins)
                                      (nth 65 ins))
                                (car sts))))
    (otherwise nil)))

; se-primp-apply lemmas

(defun len-se-primp-apply (fn ins sts)
  (declare (xargs :guard t)
           (ignore ins sts))
  (case fn
    ((b-nbuf fd1 fd1s fd1slp ttl-clk-input ttl-input) 2)
    (dp-ram-16x32 32)
    (mem-32x32    33)
    (ttl-bidirect  3)
    (otherwise     1)))

;; (defthm len-se-primp-apply-lemma
;;   (implies (primp fn)
;;            (equal (len (se-primp-apply fn ins sts))
;;                   (len-se-primp-apply fn ins sts)))
;;   :hints (("Goal" :in-theory (enable primp))))

; de-primp-apply lemmas

(defun len-de-primp-apply (fn ins sts)
  (declare (xargs :guard (true-listp ins))
           (ignore ins sts))
  (case fn
    ((dp-ram-16x32 fd1 fd1s fd1slp mem-32x32) 1)
    (otherwise 0)))

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
          (or (consp         md-ins)             ; Module must have at least
              (consp         md-outs))           ; one input or one output
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
       (consp module)
       (let ((module-name (car module)))
         (and (net-syntax-okp rest-netlist)
              (not (primp module-name))    ; Module name is not a primitive
              (not (assoc-eq module-name   ;   nor previously defined module
                             rest-netlist))
              (module-syntax-okp module)))))))

; Some facts about our netlist syntax.

(defthm net-syntax-okp-forward-to-symbol-alistp
  ;; For effeciency, this lemms before guard proof for NET-SYNTAX-OKP
  (implies (net-syntax-okp x)
           (symbol-alistp x))
  :rule-classes :forward-chaining)

(verify-guards net-syntax-okp)

(defthm net-syntax-okp-delete-to-eq-netlist
  (implies (net-syntax-okp netlist)
           (net-syntax-okp (delete-to-eq fn netlist))))

(defthm assoc-eq-of-non-fn-netlist
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

(defun sts-okp-guard (fn sts netlist)
  (declare (xargs :guard t))
   (and (symbolp fn)
        (true-listp sts)
        (net-syntax-okp netlist)
        (net-arity-okp  netlist)))

(defun sts-occs-okp-guard (occs sts-alist netlist)
  (declare (xargs :guard t))
  (and (symbol-alistp sts-alist)
       (net-syntax-okp netlist)
       (net-arity-okp netlist)
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
                   :guard (sts-okp-guard fn sts netlist)
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
                   :guard (sts-occs-okp-guard occs sts-alist netlist)))
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
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal"
                    :in-theory (e/d (consp-assoc-eq-fn-of-non-empty-netlist)
                                    (md-occs md-sts))))))
  (and (symbolp fn)
       (true-listp ins)
       (net-syntax-okp netlist)
       (net-arity-okp netlist)
       ;; Check form of top-level INS argument
       (if (primp fn)
           (equal (primp-ins fn) (len ins))
         (if (assoc-eq fn netlist)
             (equal (len (md-ins (assoc-eq fn netlist)))
                    (len ins))
           nil))))

(defun se-guard (fn ins sts netlist)
  (declare (xargs :guard t))
  (and (se-ins-guard fn ins netlist)
       (sts-okp-guard fn sts netlist)
       (sts-okp fn sts netlist)))

(defun se-occ-guard (occs wire-alist sts-alist netlist)
  (declare (xargs :guard t))
  (and (sts-occs-okp-guard occs sts-alist netlist)
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
                (wire-alist (pairs md-ins ins))
                (sts-alist  (pairs md-sts sts)))
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
            (new-alist (pairs occ-outs new-vals))
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
                (wire-alist  (pairs    md-ins ins))
                (sts-alist   (pairs    md-sts sts))
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
                              (wire-alist (pairs md-ins ins))
                              (sts-alist (pairs md-sts sts)))
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
           (new-alist (pairs occ-outs new-vals))
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

(verify-guards se
  ;;:guard-debug t
  :hints
  (("Goal" :in-theory
    (e/d ()
         (not
          occ-accessors-defuns
          md-accessors-defuns
          md-occs md-sts)))
   ("Subgoal 2"
    :use net-syntax-okp->module-syntax-okp))
  :otf-flg t)

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
                              (wire-alist  (pairs    md-ins ins))
                              (sts-alist   (pairs    md-sts sts))
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

(verify-guards
  de
  :hints
  (("Goal"
    :in-theory (enable occ-name assoc-eq-value))
   ("Subgoal 2"
    :use net-syntax-okp->module-syntax-okp)))

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
           :flag-mapping ((de      term)
                          (de-occ  list))
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
  (and (sts-okp-guard fn sts netlist)
       (sts-okp fn sts netlist)))

(defthm se-guard=>well-formed-sts
  (implies (se-guard fn ins sts netlist)
           (well-formed-sts fn sts netlist))
  :rule-classes :forward-chaining)

(defun well-formed-sts-occs (occs sts-alist netlist)
  (declare (xargs :guard t))
  (and (sts-occs-okp-guard occs sts-alist netlist)
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
                 (NET-SYNTAX-OKP NETLIST)
                 (NET-ARITY-OKP NETLIST)
                 (EQUAL (PRIMP-STS FN) (LEN STS))
                 (NOT (EQUAL FN 'DP-RAM-16X32))
                 (NOT (EQUAL FN 'FD1))
                 (NOT (EQUAL FN 'FD1S))
                 (NOT (EQUAL FN 'FD1SLP))
                 (NOT (EQUAL FN 'MEM-32X32)))
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

(defun de-sim-guard (fn ins-list netlist)
  (declare (xargs :guard t))
  (if (atom ins-list)
      t
    (and (se-ins-guard fn (car ins-list) netlist)
         (de-sim-guard fn (cdr ins-list) netlist))))

(defun de-sim (fn ins-list sts netlist)
  (declare (xargs :guard (and (de-sim-guard fn ins-list netlist)
                              (well-formed-sts fn sts netlist))
                  :verify-guards nil))
  (if (atom ins-list)
      sts
    (de-sim fn
            (cdr ins-list)
            (de fn (car ins-list) sts netlist)
            netlist)))

(defthm open-de-sim
  (and
   (implies (atom ins-list)
            (equal (de-sim fn ins-list sts netlist)
                   sts))
   (implies (consp ins-list)
            (equal (de-sim fn ins-list sts netlist)
                   (de-sim fn (cdr ins-list)
                           (de fn (car ins-list) sts netlist)
                           netlist)))))

(in-theory (disable de-sim))

(defun de-sim-list (fn ins-list sts netlist)
  (declare (xargs :guard (and (de-sim-guard fn ins-list netlist)
                              (well-formed-sts fn sts netlist))
                  :verify-guards nil))
  (if (atom ins-list)
      (list sts)
    (cons sts
          (de-sim-list fn
                       (cdr ins-list)
                       (de fn (car ins-list) sts netlist)
                       netlist))))

(defun simulate (fn ins-list sts netlist)
  (declare (xargs :guard (and (de-sim-guard fn ins-list netlist)
                              (well-formed-sts fn sts netlist))
                  :verify-guards nil))
  (if (atom ins-list)
      nil
    (let ((value (se fn (car ins-list) sts netlist))
          (new-sts (de fn (car ins-list) sts netlist)))
      (cons (list value new-sts)
            (simulate fn (cdr ins-list) new-sts netlist)))))

(defun de-sim-n (fn ins-list sts netlist n)
  (declare (xargs :guard (and (de-sim-guard fn ins-list netlist)
                              (well-formed-sts fn sts netlist)
                              (equal (len ins-list) n)
                              (natp n))
                  :verify-guards nil))
  (if (zp n)
      sts
    (de-sim-n fn
              (cdr ins-list)
              (de fn (car ins-list) sts netlist)
              netlist
              (1- n))))

(defthm de-sim-m+n
  (implies (and (natp m)
                (natp n))
           (equal (de-sim-n fn ins-list sts netlist (+ m n))
                  (de-sim-n fn (nthcdr m ins-list)
                            (de-sim-n fn ins-list sts netlist m)
                            netlist
                            n)))
  :hints (("Goal"
           :induct (de-sim-n fn ins-list sts netlist m))))

(defthm open-de-sim-n
  (and
   (implies (zp n)
            (equal (de-sim-n fn ins-list sts netlist n)
                   sts))
   (implies (not (zp n))
            (equal (de-sim-n fn ins-list sts netlist n)
                   (de-sim-n fn
                             (cdr ins-list)
                             (de fn (car ins-list) sts netlist)
                             netlist
                             (1- n))))))

(in-theory (disable de-sim-n))

(verify-guards
 de-sim
 ;;:guard-debug t
 :hints
 (("Goal"
   :in-theory (disable de sts-okp))))

(verify-guards
 de-sim-list
 :hints
 (("Goal"
   :in-theory (disable de sts-okp))))

(verify-guards
 simulate
 :hints
 (("Goal"
   :in-theory (disable se de sts-okp))))

(verify-guards
 de-sim-n
 :hints
 (("Goal"
   :in-theory (disable de sts-okp))))

(in-theory (disable se-guard se-occ-guard
                    well-formed-sts well-formed-sts-occs))

;; ======================================================================

;; Define some theories.

(deftheory se-rules
  '(se
    se-primp-apply
    open-se
    md-name md-ins md-outs md-sts md-occs
    occ-name occ-outs occ-fn occ-ins))

(deftheory de-rules
  '(de
    de-primp-apply
    open-de
    se
    se-primp-apply
    md-name md-ins md-outs md-sts md-occs
    occ-name occ-outs occ-fn occ-ins))

;; The following theory should be disabled in order to speed up proof times
;; when proving lemmas about TV-based circuits' outputs and next state.

(deftheory tv-disabled-rules
  '(take
    take-of-take-split
    take-of-too-many
    take-of-len-free
    nthcdr
    nthcdr-of-len-l
    no-duplicatesp-eq
    prefixp-of-cons-left
    prefixp-when-equal-lengths
    str::iprefixp-of-cons-left
    str::istrprefixp$inline
    str::iprefixp-when-prefixp))
