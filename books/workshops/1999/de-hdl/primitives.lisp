
;;;  primitives.lisp                              Warren A. Hunt, Jr.

(in-package "ACL2")
(include-book "measure")

(deflabel primitives-defuns-section)

;;;  The list below identifies the primitive functions and their
;;;  respective arities.

(defconst *primitives*
  '((ff    (ins a)        (outs x)    (sts q)     (dep (x)))
    (ff2   (ins a b)      (outs x y)  (sts q r)   (dep (x) (y)))

    (gnd   (ins)          (outs x)    (sts)       (dep (x)))
    (vdd   (ins)          (outs x)    (sts)       (dep (x)))

    (buf   (ins a)        (outs x)    (sts)       (dep (x a)))
    (not   (ins a)        (outs x)    (sts)       (dep (x a)))

    (and   (ins a b)      (outs x)    (sts)       (dep (x a b)))
    (or    (ins a b)      (outs x)    (sts)       (dep (x a b)))
    (nand  (ins a b)      (outs x)    (sts)       (dep (x a b)))
    (nor   (ins a b)      (outs x)    (sts)       (dep (x a b)))
    (xor   (ins a b)      (outs x)    (sts)       (dep (x a b)))
    (if    (ins a b c)    (outs x)    (sts)       (dep (x a b c)))

    (and3  (ins a b c)    (outs x)    (sts)       (dep (x a b c)))
    (and4  (ins a b c d)  (outs x)    (sts)       (dep (x a b c d)))
    (or3   (ins a b c)    (outs x)    (sts)       (dep (x a b c)))
    (or4   (ins a b c d)  (outs x)    (sts)       (dep (x a b c d)))
    (nand3 (ins a b c)    (outs x)    (sts)       (dep (x a b c)))
    (nand4 (ins a b c d)  (outs x)    (sts)       (dep (x a b c d)))
    (nor3  (ins a b c)    (outs x)    (sts)       (dep (x a b c)))
    (nor4  (ins a b c d)  (outs x)    (sts)       (dep (x a b c d)))
    ))

(defthm symbol-alistp-*primitives*
  (and (alistp *primitives*)
       (symbol-alistp *primitives*)))

(defun primp (fn)
  (declare (xargs :guard t))
  (cdr (assoc-eq fn *primitives*)))

(defthm symbol-alistp-primp
  (and (alistp (primp fn))           ;;;  I seem to need this conjunct in spite
       (symbol-alistp (primp fn))))  ;;;  of forward chaining rules to this one.

;;;  Why do I need the next event?  The definition of
;;;  OCC-ARITY-OKP requires it, but why?

(defthm consp-assoc-eq-primp-values
  (implies (primp fn)
           (and (consp (assoc-eq 'ins  (primp fn)))
                (consp (assoc-eq 'outs (primp fn)))
                (consp (assoc-eq 'sts  (primp fn))))))

(defun primp-ins  (fn)
  (declare (xargs :guard (primp fn)))
  (cdr (assoc-eq 'ins  (primp fn))))

(defun primp-outs (fn)
  (declare (xargs :guard (primp fn)))
  (cdr (assoc-eq 'outs (primp fn))))

(defun primp-sts  (fn)
  (declare (xargs :guard (primp fn)))
  (cdr (assoc-eq 'sts  (primp fn))))

(defun primp-deps (fn)
  (declare (xargs :guard (primp fn)))
  (cdr (assoc-eq 'deps (primp fn))))

(defthm primp-fns-okp
  (implies (primp fn)
	   (and (symbol-listp  (primp-ins  fn))
		(symbol-listp  (primp-outs fn))
		(symbol-listp  (primp-sts  fn))
		(symbol-alistp (primp-deps fn)))))

(defthm assoc-primp-fn
  (implies (and (symbolp fn)
                (primp fn)
                (not (consp (assoc 'sts (primp fn)))))
           (not (assoc 'sts (primp fn)))))

(in-theory (disable primp))

;;;  Identify a set of symbols for this book.

(deftheory primtives-section
  (set-difference-theories (current-theory :here)
			   (current-theory 'primitives-defuns-section)))
