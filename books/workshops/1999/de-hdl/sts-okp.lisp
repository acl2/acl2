
;;;  sts-okp.lisp                               Warren A. Hunt, Jr.

(in-package "ACL2")
(include-book "arity")
(set-well-founded-relation e0-ord-<)

(deflabel sts-okp-defuns-section)


;;;  The structure of a state argument must be isomorphic to the
;;;  nesting structure of its corresponding module definition.

;;;  At the end of this file are an alternative definition of STS-OKP
;;;  which is meant to speed up its execution; however, some testing
;;;  didn't reveal more than a small (< 10%) improvement.  One short
;;;  circuit test is included here (= (len sts) 0), which should help
;;;  on netlists with deeply nested state structures.

(mutual-recursion

(defun sts-okp (fn sts netlist)
  (declare (xargs :measure (se-measure fn netlist)
                  :guard   (and (symbolp fn)
                                (true-listp sts)
                                (net-syntax-okp netlist)
                                (net-arity-okp netlist))
		  :guard-hints
		  (("Goal" :in-theory
		    (enable some-netlist-lookup-facts occ-syntax-okp
			    module-arity-okp)))))
  (if (primp fn)
      (and (eqlable-listp sts)   ; Allowable kinds of states.
           (eql (len sts)        ; Relationship between STS and a primitive.
		(len (primp-sts fn))))
    (let ((module (assoc-eq fn netlist)))
      (if (atom module)
          nil
        (let* ((md-occs   (md-occs   module))
               (md-sts    (md-sts    module)))
          (and (eql (len sts)       ; Relationship between STS
		    (len md-sts))   ; and a module's states
	       (or (= (len sts) 0)  ; Short circuit -- speed improvement?
		   (sts-occ-okp md-occs (pairlis$ md-sts sts)
				(delete-eq-module fn netlist)))))))))

(defun sts-occ-okp (occs sts-alist netlist)
  (declare (xargs :measure (se-measure occs netlist)
                  :guard   (and (occs-syntax-okp occs)
                                (net-syntax-okp netlist)
                                (occs-arity-okp occs netlist)
                                (net-arity-okp netlist)
                                (alistp sts-alist))
		  :guard-hints
		  (("Goal" :in-theory
		    (enable some-netlist-lookup-facts occ-syntax-okp
			    module-arity-okp)))))
  (if (endp occs)
      t
    (and (let* ((occ      (car occs))
                (occ-fn   (occ-fn   occ))
                (occ-name (occ-name occ))
                (sts      (assoc-eq-value occ-name sts-alist)))
           (and (true-listp sts)
                (sts-okp occ-fn sts netlist)))
          (sts-occ-okp (cdr occs) sts-alist netlist))))
)


(defthm assoc-eq-same-with-cdr
  (implies (and (net-syntax-okp netlist)
                (net-arity-okp  netlist)
                (symbolp fn)
                (not (primp fn))
                (not (eq fn (caar netlist))))
           (equal (assoc fn (cdr netlist))
                  (assoc fn netlist))))

(defthm sts-okp-same-with-cdr
  (implies (and (net-syntax-okp netlist)
                (net-arity-okp  netlist)
                (symbolp fn)
                (not (primp fn))
                (not (eq fn (caar netlist))))
           (equal (sts-okp fn sts (cdr netlist))
                  (sts-okp fn sts netlist)))
  :hints (("Goal"
           :do-not-induct t
           :expand (sts-okp fn sts netlist))))

(defthm sts-okp-cdr-netlist
  (implies (and (net-syntax-okp netlist)
                (net-arity-okp  netlist)
                (symbolp fn)
                (not (primp fn))
                (not (eq fn (caar netlist)))
                (sts-okp fn sts netlist))
           (sts-okp fn sts (cdr netlist))))


;;;  Identify a set of symbols for this book.

(deftheory sts-okp-section
  (set-difference-theories (current-theory :here)
			   (current-theory 'sts-okp-defuns-section)))

#|

(defun len-primp-sts (fn)
  (declare (xargs :guard (primp fn)))
  (assoc-eq-value fn '((ff    . 1)
		       (ff2   . 2)
		       (gnd   . 0)
		       (vdd   . 0)
		       (buf   . 0)
		       (not   . 0)
		       (and   . 0)
		       (and3  . 0)
		       (and4  . 0)
		       (or    . 0)
		       (or3   . 0)
		       (or4   . 0)
		       (nand  . 0)
		       (nand3 . 0)
		       (nand4 . 0)
		       (nor   . 0)
		       (nor3  . 0)
		       (nor4  . 0)
		       (xor   . 0)
		       (if    . 0))))

(defthm len-primp-sts-correct
  (implies (primp fn)
	   (= (len (primp-sts fn))
	      (len-primp-sts fn)))
  :hints (("Goal" :in-theory (enable primp))))

(defun sts-okp (fn sts netlist)
  (declare (xargs :measure (se-measure fn netlist)
                  :guard   (and (symbolp fn)
                                (true-listp sts)
                                (net-syntax-okp netlist)
                                (net-arity-okp netlist))
		  :guard-hints
		  (("Goal" :in-theory
		    (enable some-netlist-lookup-facts occ-syntax-okp)))))
  (if (primp fn)
      (and (eqlable-listp sts)   ; Allowable kinds of states.
           (eql (len sts)        ; Relationship between STS and a primitive.
		(len-primp-sts fn)))
    (let ((module (assoc-eq fn netlist)))
      (if (atom module)
          nil
        (let* ((md-occs   (md-occs   module))
               (md-sts    (md-sts    module)))
          (and (eql (len sts)    ; Relationship between STS and a module's states
		    (len md-sts))
	       (or (= (len sts) 0)  ; Short circuit -- little speed improvement
		   (sts-occ-okp md-occs (pairlis$ md-sts sts)
				(delete-eq-module fn netlist)))))))))

|#
