
;;;  arity.lisp                               Warren A. Hunt, Jr.

(in-package "ACL2")
(include-book "syntax")

(deflabel arity-defuns-section)

;;;  Arity Recognizer

(defun occ-arity-okp (occ netlist)
  (declare (xargs :guard (and (net-syntax-okp netlist)
                              (occ-syntax-okp occ))
		  :guard-hints
		  (("Goal" :in-theory
		    (enable some-netlist-lookup-facts)))))
  (let* ((occ-outs (occ-outs occ))
         (occ-fn   (occ-fn   occ))
         (occ-ins  (occ-ins  occ))
         (primp    (primp occ-fn))
         (len-ins  (len occ-ins))
         (len-outs (len occ-outs)))
    (if primp
        (and (eql (len (primp-ins  occ-fn)) len-ins)
             (eql (len (primp-outs occ-fn)) len-outs))
      (let ((module (assoc-eq occ-fn netlist)))
        (if (atom module)
            nil
          (and (eql (len (md-ins  module)) len-ins)
               (eql (len (md-outs module)) len-outs)))))))

(defthm occ-arity-okp-forward
  (implies (occ-arity-okp occ netlist)
           (let* ((occ-outs (occ-outs occ))
                  (occ-fn   (occ-fn   occ))
                  (occ-ins  (occ-ins  occ))
		  (primp    (primp occ-fn))
                  (len-ins  (len occ-ins))
                  (len-outs (len occ-outs)))
             (if primp
                 (and (eql (len (primp-ins  occ-fn)) len-ins)
                      (eql (len (primp-outs occ-fn)) len-outs))
               (let ((module (assoc-eq occ-fn netlist)))
                 (if (atom module)
                     nil
                   (and (eql (len (md-ins  module)) len-ins)
                        (eql (len (md-outs module)) len-outs)))))))
  :rule-classes :forward-chaining)

(in-theory (disable occ-arity-okp))

(defun occs-arity-okp (occs netlist)
  (declare (xargs :guard (and (net-syntax-okp netlist)
                              (occs-syntax-okp occs))))
  (if (atom occs)
      t
    (and (occ-arity-okp (car occs) netlist)
         (occs-arity-okp (cdr occs) netlist))))

(defun module-arity-okp (module cdr-netlist)
  (declare (xargs :guard (and (module-syntax-okp module)
                              (net-syntax-okp cdr-netlist))))
  (occs-arity-okp (md-occs module) cdr-netlist))

(in-theory (disable module-arity-okp))

;;; Below is the definition I think I want...

(defun net-arity-okp (netlist)
  (declare (xargs :guard (net-syntax-okp netlist)))
  (if (atom netlist)
      t
    (let* ((module      (car netlist))
           (cdr-netlist (cdr netlist))
           (md-name     (md-name module)))
      (and (not (assoc-eq md-name cdr-netlist))  ; No self-referential modules.
           (module-arity-okp module cdr-netlist)
           (net-arity-okp cdr-netlist)))))

(defthm net-arity-okp-forward
  (implies (and (net-arity-okp netlist)
		(net-syntax-okp netlist)
		(consp netlist))
	   (let* ((module      (car netlist))
		  (cdr-netlist (cdr netlist))
		  (md-name     (md-name module)))
	     (and (not (assoc-eq md-name cdr-netlist))
		  (module-arity-okp module cdr-netlist)
		  (net-arity-okp cdr-netlist))))
  :rule-classes (:forward-chaining))


;;;  I am here!!!  This is going to be a mess, as I need to establish
;;;  various "arity" properties, which means I am going to have to
;;;  perform inductions on the netlist, which is not how the arity
;;;  functions operate.

(defthm module-arity-okp-of-something-gross!!!
  (implies (and (net-arity-okp netlist)
		(net-syntax-okp netlist)
		(assoc-eq fn netlist))
	   (module-arity-okp (assoc-eq fn netlist)
			     (cdr (assoc-eq-rest fn netlist))))
  :hints (("Goal" :in-theory (enable md-name))))


(defthm net-arity-okp-of-delete-eq-module
  (implies (and (assoc-eq fn netlist)
                (net-syntax-okp netlist)
                (net-arity-okp netlist))
           (net-arity-okp (delete-eq-module fn netlist))))

(defthm module-arity-okp-of-something-gross-2!!!
  (implies (and (net-arity-okp netlist)
		(net-syntax-okp netlist)
		(consp (assoc-eq fn netlist)))
	   (module-arity-okp (assoc-eq fn netlist)
			     (delete-eq-module fn netlist)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable md-name))))


(defmacro enable-disable (a b)
  `(set-difference-theories (enable ,@a) ',b))

(defthm occs-arity-okp-md-occs-assoc-eq-fn-netlist
  (IMPLIES (AND (NET-ARITY-OKP NETLIST)
		(NET-SYNTAX-OKP NETLIST)
		(TRUE-LISTP STS)
		(SYMBOLP FN)
		(NOT (PRIMP FN))
		(CONSP (ASSOC-EQ FN NETLIST))
;		(EQUAL (LEN STS) (LEN (MD-STS (ASSOC-EQ FN NETLIST))))
		)
	   (OCCS-ARITY-OKP (MD-OCCS (ASSOC-EQ FN NETLIST))
			   (DELETE-EQ-MODULE FN NETLIST)))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (enable-disable
		       (module-arity-okp)
		       (module-arity-okp-of-something-gross-2!!!))
	   :use ((:instance module-arity-okp-of-something-gross-2!!!
			    (netlist netlist)
			    (fn fn)))
	   )))

(defthm net-arity-okp-of-delete-eq-module
  (implies (and (assoc-eq fn netlist)
                (net-syntax-okp netlist)
                (net-arity-okp netlist))
           (net-arity-okp (delete-eq-module fn netlist))))



(defthm true-listp-sts-list-of-module
  (implies (and (net-syntax-okp netlist)
                (symbolp fn)
                (not (primp fn))
                (consp (assoc-eq fn netlist)))
           (true-listp (md-sts (assoc-eq fn netlist))))
  :hints (("Goal" :do-not-induct t)))


;;;  Identify a set of symbols for this book.

(deftheory arity-section
  (set-difference-theories (current-theory :here)
			   (current-theory 'arity-defuns-section)))
