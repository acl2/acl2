
; vw-hrch-hdl.lisp

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

(in-package "ACL2")
(include-book "vw-flat-hdl")

;; Some primitive recognizers

(defun primp (occ-type)
  "Recognizes a primitive circuit component type"
  (declare (xargs :guard t))
  (assoc occ-type *primitive-database*))

(defun primp-nodes (occ-type)
  (declare (xargs :guard t))
  (cadr (primp occ-type)))

(defun primp-brs (occ-type)
  (declare (xargs :guard t))
  (caddr (primp occ-type)))

(defun primp-params (occ-type)
  (declare (xargs :guard t))
  (cadddr (primp occ-type)))

;; Next few events define syntax for heirarchical netlists

(defun occ-syntax-okp (occ)
  (declare (xargs :guard t))
  (and (true-listp occ)
       (<= 3 (len occ))
       (let ((occ-name (car occ))
	     (occ-type (cadr occ))
	     (occ-nodes  (caddr occ)))
         (and
          ;; Occurrence name
          (symlp occ-name)
          ;; Occurrence type (primitive or module)
          (symbolp occ-type) ; can be T for transmission line
          ;; IO nodes
          (syml-listp occ-nodes)
; An occurrence of a module can use the same wire/node name for
; for the module's IO wires.
          ;; (no-duplicatesp-equal occ-nodes)
          ;; Primitive
          (if (primp occ-type)
              ;; use occurrencep for more rigorous tests?
              (let ((occ-brs    (cadddr occ))
                    (occ-params (car (cddddr occ))))
                (and
                 ;; transmission line can have duplicate nodes.
                 (if (eq occ-type 't)
                     t
                   (no-duplicatesp-equal occ-nodes))
                 ;; Check the branch names
                 (syml-listp occ-brs)
                 (no-duplicatesp-equal occ-brs)
                 ;; Check the parameters
                 (vw-eval-term-listp occ-params)))
            ;; Module
            t)))
         ;; Leave the remainder of the checks for occ-arity-okp
       ))

(defun occs-syntax-okp (occs)
  (declare (xargs :guard t))
  (if (atom occs)
      (null occs)
    (and (occ-syntax-okp (car occs))
         (occs-syntax-okp (cdr occs)))))

(defun module-syntax-okp (module)
  (declare (xargs :guard t))
  (and (true-listp module)
       (<= 3 (len module))
       ;; Name
       (symlp (car module))
       ;; IOs
       (syml-listp (cadr module))
       ;; Occurrences
       (occs-syntax-okp (caddr module))))

(defun netlist-syntax-okp (netlist)
  "Recognizes a well-formed, hierarchial RSFQ circuit netlist."
  (declare (xargs :guard t))
  (if (atom netlist)
      (null netlist)
    (b* ((module (car netlist))
         (rest-netlist (cdr netlist)))
      (and (module-syntax-okp module)
           (netlist-syntax-okp rest-netlist)
           (b* ((module-name (car module)))
	     (and (not (primp module-name))    ; module not a primitive
		  (not (assoc module-name      ; module not redefined later
			      rest-netlist))))))))

(defthm netlist-syntax-okp-forward-to-alistp
  (implies (netlist-syntax-okp circuit)
           (alistp circuit))
  :rule-classes :forward-chaining)

;; Next few events define arity for heirarchical netlists

(defun occ-arity-okp (occ netlist)
  (declare (xargs :guard (and (occ-syntax-okp occ)
                              (netlist-syntax-okp netlist))))
  (let* ((occ-type (cadr occ))
         (occ-nodes  (caddr occ))
         (prim     (primp occ-type)))
    ;; Check the arities, based on the reference name
    (if prim
        (let ((occ-brs (cadddr occ))
              (occ-params (car (cddddr occ))))
          ;; # nodes and branches match primitive
          (and
           (or (= (len occ-nodes) (len (primp-nodes occ-type)))
               (cw "occ-arity-okp: Wrong number of nodes. Given: ~p0, ~
                    Expected: ~p1. The occurrence ~p2~%"
                   (len occ-nodes) (len (primp-nodes occ-type)) occ))
           (or (= (len occ-brs) (len (primp-brs occ-type)))
               (cw "occ-arity-okp: Wrong number of branches. Given: ~
                    ~p0, Expected: ~p1 ~%"
                   (len occ-brs) (len (primp-brs occ-type))))
           (or (= (len occ-params) (len (primp-params occ-type)))
               (cw "occ-arity-okp: Wrong number of parameters. Given: ~
                    ~p0, Expected: ~p1 ~%"
                   (len occ-params) (len (primp-params occ-type))))))
      ;; IOs, branches, vals
      ;; # nodes matches module
      (let* ((module (assoc occ-type netlist))
	    (module-IOs (cadr module)))
	(or (and module
                 (mbt (module-syntax-okp module))
                 (= (len occ-nodes) (len module-IOs)))
            (cw "occ-arity-okp: Wrong number of node IOs. Given: ~p0, ~
                 Expected: ~p1. The occurence: ~p2~%"
                (len occ-nodes) (len module-IOs) occ))))))

(defun occs-arity-okp (occs netlist)
  (declare (xargs :guard (and (occs-syntax-okp occs)
                              (netlist-syntax-okp netlist))))
  (if (atom occs)
      t
    (and (occ-arity-okp (car occs) netlist)
         (occs-arity-okp (cdr occs) netlist))))

;; should we define module arity?

(defun netlist-arity-okp (netlist)
  (declare (xargs :guard (netlist-syntax-okp netlist)))
  (if (atom netlist)
      t
    (let* ((module (car netlist))
           (cdr-netlist (cdr netlist))
           (module-name (car module)))
      (and (or (not (assoc-eq module-name cdr-netlist))
               (cw "netlist-arity-okp: duplicate definition of module ~p0. ~%"
                   module-name))
           (netlist-arity-okp cdr-netlist)
           (occs-arity-okp (caddr module) cdr-netlist)))))

