
;;;  syntax.lisp                               Warren A. Hunt, Jr.

(in-package "ACL2")
(include-book "primitives")

(deflabel syntax-defuns-section)

;;;  A module is the representation of a non-primitive FSM.  It is
;;;  composed of five elements:  name, inputs, outputs, states, and
;;;  occurrences.  Each occurrence is itself composed of four pieces:
;;;  name, outputs, primitive or module reference, and inputs.  The
;;;  following macros are the destructor operations for accessing the
;;;  various pieces of a module.

(deflabel md-accessors-defuns-section)

(defun md-name   (x)
  (declare (xargs :guard (consp-n+1 x 0)))
  (car x))

(defun md-ins    (x)
  (declare (xargs :guard (consp-n+1 x 1)))
  (cadr x))

(defun md-outs   (x)
  (declare (xargs :guard (consp-n+1 x 2)))
  (caddr x))

(defun md-sts    (x)
  (declare (xargs :guard (consp-n+1 x 3)))
  (cadddr x))

(defun md-occs   (x)
  (declare (xargs :guard (consp-n+1 x 4)))
  (car (cddddr x)))

(deftheory md-accessors-defuns
  (set-difference-theories (current-theory :here)
			   (current-theory 'md-accessors-defuns-section)))

(deflabel occ-accessors-defuns-section)

(defun occ-name  (x)
  (declare (xargs :guard (consp-n+1 x 0)))
  (car x))

(defun occ-outs  (x)
  (declare (xargs :guard (consp-n+1 x 1)))
  (cadr x))

(defun occ-fn    (x)
  (declare (xargs :guard (consp-n+1 x 2)))
  (caddr x))

(defun occ-ins   (x)
  (declare (xargs :guard (consp-n+1 x 3)))
  (cadddr x))

(deftheory occ-accessors-defuns
  (set-difference-theories (current-theory :here)
			   (current-theory 'occ-accessors-defuns-section)))

;;;  We define the syntactic restrictions for occurrences and modules.

(defun occ-syntax-okp (occ)
  (declare (xargs :guard t))
  (and (true-listp-at-least-n+1 occ 3)
       (let ((occ-name (occ-name occ))
             (occ-outs (occ-outs occ))
             (occ-fn   (occ-fn   occ))
             (occ-ins  (occ-ins  occ)))
         (and (symbolp           occ-name)
              (symbol-listp      occ-outs)
              (no-duplicatesp-eq occ-outs)
              (symbolp           occ-fn)
              (symbol-listp      occ-ins)))))

;;;  For the lemmas that follow, it is important that the "occ" functions
;;;  are disabled or they will not fire.

(defthm occ-name-info
  (implies (occ-syntax-okp occ)
	   (symbolp (occ-name occ))))

(defthm occ-outs-info
  (implies (occ-syntax-okp occ)
	   (and (symbol-listp      (occ-outs occ))
		(no-duplicatesp-eq (occ-outs occ)))))

(defthm occ-fn-info
  (implies (occ-syntax-okp occ)
	   (symbolp (occ-fn occ))))

(defthm occ-ins-info
  (implies (occ-syntax-okp occ)
	   (symbol-listp  (occ-ins occ))))

(defthm cons-size-occ-lessp-eql
  (and (<= (cons-size (occ-name occ))
	   (cons-size occ))
       (<= (cons-size (occ-outs occ))
	   (cons-size occ))
       (<= (cons-size (occ-fn   occ))
	   (cons-size occ))
       (<= (cons-size (occ-ins  occ))
	   (cons-size occ)))
  :rule-classes (:linear))

(defthm cons-size-occ-lessp
  (implies (consp occ)
	   (and (< (cons-size (occ-name occ))
		   (cons-size occ))
		(< (cons-size (occ-outs occ))
		   (cons-size occ))
		(< (cons-size (occ-fn   occ))
		   (cons-size occ))
		(< (cons-size (occ-ins  occ))
		   (cons-size occ))))
  :rule-classes (:linear))

(in-theory (disable occ-accessors-defuns))
(in-theory (disable occ-syntax-okp))

(defun occs-syntax-okp (occs)
  (declare (xargs :guard t))
  (if (atom occs)
      (eq occs nil)
    (and (occ-syntax-okp (car occs))
         (occs-syntax-okp (cdr occs)))))

(defun module-syntax-okp (module)
  (declare (xargs :guard t))
  (and (true-listp-at-least-n+1 module 4)
       (let ((md-name   (md-name   module))
             (md-ins    (md-ins    module))
             (md-outs   (md-outs   module))
             (md-sts    (md-sts    module))
             (md-occs   (md-occs   module)))
         (and (symbolp           md-name)
              (symbol-listp      md-ins)
              (no-duplicatesp-eq md-ins)
              (symbol-listp      md-outs)
              (no-duplicatesp-eq md-outs)
              (symbol-listp      md-sts)
              (no-duplicatesp-eq md-sts)
              (symbol-alistp     md-occs)
              ;; (consp             md-ins)    ; One input?
              ;; (consp             md-outs)   ; One output?
              (consp             md-occs)   ; One occurrence?
              (occs-syntax-okp md-occs)))))

;;;  For the lemmas that follow, it is important that the "md" functions
;;;  are disabled or they will not fire.

(defthm md-name-info
  (implies (module-syntax-okp module)
	   (symbolp (md-name module))))

(defthm md-ins-info
  (implies (module-syntax-okp module)
	   (and (symbol-listp      (md-ins module))
		(true-listp        (md-outs module))
		(no-duplicatesp-eq (md-ins module)))))

(defthm md-outs-info
  (implies (module-syntax-okp module)
	   (and (symbol-listp      (md-outs module))
		(true-listp        (md-outs module))
		(no-duplicatesp-eq (md-outs module)))))

;;;   :monitor (:rewrite md-outs-info) t

(defthm md-sts-info
  (implies (module-syntax-okp module)
	   (and (symbol-listp      (md-sts module))
		(true-listp        (md-outs module))
		(no-duplicatesp-eq (md-sts module)))))

(defthm md-occs-info
  (implies (module-syntax-okp module)
	   (and (symbol-alistp    (md-occs module))
		(true-listp        (md-outs module))
		(occs-syntax-okp  (md-occs module)))))

(defthm cons-size-md-lessp-eql
  (and (<= (cons-size (md-name module))
	   (cons-size module))
       (<= (cons-size (md-ins  module))
	   (cons-size module))
       (<= (cons-size (md-outs module))
	   (cons-size module))
       (<= (cons-size (md-sts  module))
	   (cons-size module))
       (<= (cons-size (md-occs module))
	   (cons-size module)))
  :rule-classes (:linear))

(defthm cons-size-md-lessp
  (implies (consp module)
	   (and (<= (cons-size (md-name module))
		    (cons-size module))
		(<= (cons-size (md-ins  module))
		    (cons-size module))
		(<= (cons-size (md-outs module))
		    (cons-size module))
		(<= (cons-size (md-sts  module))
		    (cons-size module))
		(<= (cons-size (md-occs module))
		    (cons-size module))))
  :rule-classes (:linear))

(in-theory (disable md-accessors-defuns))
(in-theory (disable module-syntax-okp))

(defun net-syntax-okp (netlist)
  (declare (xargs :guard t))
  (if (atom netlist)
      (eq netlist nil)
    (and (module-syntax-okp (car netlist))
         (net-syntax-okp (cdr netlist)))))

;;;  Here are a couple of forward chaining rules.  Do I really need them
;;;  after proving everything above?

(defthm occ-syntax-okp-forward
  (implies (occ-syntax-okp occ)
           (and (true-listp-at-least-n+1 occ 3)
                (let ((occ-name (occ-name occ))
                      (occ-outs (occ-outs occ))
                      (occ-fn   (occ-fn   occ))
                      (occ-ins  (occ-ins  occ)))
                  (and (symbolp           occ-name)
                       (symbol-listp      occ-outs)
                       (no-duplicatesp-eq occ-outs)
                       (symbolp           occ-fn)
                       (symbol-listp      occ-ins)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable occ-syntax-okp))))

(defthm alistp-symbol-listp-symbol-alistp-are-true-list
  (implies (or (alistp        lst)
	       (symbol-listp  lst)
	       (symbol-alistp lst))
	   (true-listp lst)))

(defthm module-syntax-okp-forward
  (implies (module-syntax-okp module)
           (and (true-listp-at-least-n+1 module 4)
                (let ((md-name   (md-name   module))
                      (md-ins    (md-ins    module))
                      (md-outs   (md-outs   module))
                      (md-sts    (md-sts    module))
                      (md-occs   (md-occs   module)))
                  (and (symbolp           md-name)
                       (symbol-listp      md-ins)
                       (no-duplicatesp-eq md-ins)
                       (symbol-listp      md-outs)
                       (no-duplicatesp-eq md-outs)
                       (symbol-listp      md-sts)
                       (no-duplicatesp-eq md-sts)
                       (symbol-alistp     md-occs)
                       ;; (consp             md-ins) ; One input?
                       ;; (consp             md-outs) ; One output?
                       (consp             md-occs) ; One occurrence?
                       (occs-syntax-okp   md-occs)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable module-syntax-okp))))


(defthm net-syntax-okp-forward-to-symbol-alistp
  (implies (net-syntax-okp x)
           (symbol-alistp x))
  :rule-classes :forward-chaining
  :hints (("Goal"
	   :in-theory (enable module-syntax-okp net-syntax-okp md-name))))

(defthm net-syntax-okp-forward-to-alistp
  (implies (net-syntax-okp x)
           (alistp x))
  :rule-classes :forward-chaining)

(defthm net-syntax-okp-delete-eq-module-netlist
  (implies (net-syntax-okp netlist)
           (net-syntax-okp (delete-eq-module fn netlist))))

(defthm assoc-eq-of-non-fn-netlist
  (implies (and (net-syntax-okp netlist)
		(atom (assoc-eq fn netlist)))
           (equal (assoc-eq fn netlist) nil)))

(defthm true-listp-assoc-eq-fn-netlist
  (implies (net-syntax-okp netlist)
	   (true-listp (assoc-eq fn netlist))))

(defthm assoc-eq-fn-of-empty-netlist-is-nil
  (implies (atom netlist)
	   (equal (assoc-eq fn netlist) nil)))

(defthm assoc-eq-of-netlist-is-module-okp
  (implies (and (symbolp fn)
		(assoc-eq fn netlist)
		(net-syntax-okp netlist))
           (module-syntax-okp (assoc-eq fn netlist)))
  :hints (("Goal"
	   :in-theory (disable module-syntax-okp))))

(defthm net-syntax-okp-forward-to-something
  (implies (and (net-syntax-okp netlist)
		(symbolp fn)
		(not (primp fn))
		(consp (assoc-eq fn netlist)))
	   (module-syntax-okp (assoc-eq fn netlist)))
  :rule-classes :forward-chaining)

;;;  Facts that would be expensive to have around because of the
;;;  function symbols involved on the left-hand side, so we globaly
;;;  disable them and enable them when appropriate.

(deflabel some-netlist-lookup-facts-section)

(defthm assoc-eq-fn-of-non-empty-netlist-is-consp
  (implies (and (net-syntax-okp netlist)
		(not (atom (assoc-eq fn netlist))))
	   (and (consp (assoc-eq fn netlist))
		(consp (cdr (assoc-eq fn netlist)))
		(consp (cddr (assoc-eq fn netlist)))
		(consp (cdddr (assoc-eq fn netlist)))
		(consp (cddddr (assoc-eq fn netlist))))))

(defthm not-cdr-assoc-eq-fn-netlist-implies-no-module
  (implies (and (net-syntax-okp netlist)
                (atom (cdr (assoc-eq fn netlist))))
           (not (cdr (assoc-eq fn netlist)))))

(defthm not-cddr-assoc-eq-fn-netlist-implies-no-module
  (implies (and (net-syntax-okp netlist)
                (atom (cddr (assoc-eq fn netlist))))
           (not (cddr (assoc-eq fn netlist)))))

(defthm not-cdddr-assoc-eq-fn-netlist-implies-no-module
  (implies (and (net-syntax-okp netlist)
                (atom (cdddr (assoc-eq fn netlist))))
           (not (cdddr (assoc-eq fn netlist)))))

(defthm not-cddddr-assoc-eq-fn-netlist-implies-no-module
  (implies (and (net-syntax-okp netlist)
                (atom (cddddr (assoc-eq fn netlist))))
           (not (cddddr (assoc-eq fn netlist)))))

(deftheory some-netlist-lookup-facts
  (set-difference-theories (current-theory :here)
			   (current-theory 'some-netlist-lookup-facts-section)))

(in-theory (disable some-netlist-lookup-facts))


;;;  Identify a set of symbols for this book.

(deftheory syntax-section
  (set-difference-theories (current-theory :here)
			   (current-theory 'syntax-defuns-section)))

