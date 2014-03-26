; By John Cowles, modified by Matt Kaufmann.

(in-package "ACL2")

(include-book "term-lemmas" :load-compiled-file nil)

(defthm pseudo-termp-cadr
  (implies (and (pseudo-termp x)
                (consp x)
                (not (equal (car x) 'quote)))
           (pseudo-termp (cadr x)))
  :hints (("Goal" :expand (pseudo-termp x)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((pseudo-termp (cadr x))))))

(defthm pseudo-termp-caddr
  (implies (and (pseudo-termp x)
                (consp x)
                (not (equal (car x) 'quote)))
           (pseudo-termp (caddr x)))
  :hints (("Goal" :expand (pseudo-termp x)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((pseudo-termp (caddr x))))))

(defthm pseudo-termp-term-list-to-type-term
  (implies (and (pseudo-term-listp x)
		(symbolp unary-op-name))
           (pseudo-termp (term-list-to-type-term unary-op-name x))))

(defthm pseudo-termp-opener
  (implies (and (consp x)
                (symbolp (car x))
                (not (equal (car x) 'quote)))
           (equal (pseudo-termp x)
                  (pseudo-term-listp (cdr x)))))

(defthm pseudo-term-listp-opener
  (and (implies (atom x)
                (equal (pseudo-term-listp x)
                       (equal x nil)))
       (implies (consp x)
                (equal (pseudo-term-listp x)
                       (and (pseudo-termp (car x))
                            (pseudo-term-listp (cdr x)))))))

(defthm pseudo-termp-list-cdr
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (cdr x)))
  :rule-classes
  (:rewrite :forward-chaining))

(defthm pseudo-termp-car
  (implies (pseudo-term-listp x)
           (pseudo-termp (car x)))
  :rule-classes
  (:rewrite :forward-chaining))

(defthm pseudo-termp-cadr-from-pseudo-term-listp
  (implies (pseudo-term-listp x)
           (pseudo-termp (cadr x)))
  :rule-classes
  (:rewrite :forward-chaining))

(defthm pseudo-term-listp-del
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (del a x))))

(defthm pseudo-term-listp-append
  (implies (and (pseudo-term-listp x)
                (pseudo-term-listp y))
           (pseudo-term-listp (append x y))))

(defthm pseudo-term-listp-bagdiff
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (bagdiff x y))))

(defthm pseudo-term-listp-bagint
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (bagint x y))))

(defthm pseudo-term-listp-binary-op_fringe
  (implies (and (symbolp binary-op-name)
		(not (equal binary-op-name 'quote))
		(pseudo-termp x))
           (pseudo-term-listp (binary-op_fringe binary-op-name x))))

(defthm psuedo-termp-binary-op_tree
  (implies (and (pseudo-term-listp l)
		(symbolp binary-op-name)
                (symbolp fix-name)
                (not (equal binary-op-name 'quote))
		(atom constant-name))
           (pseudo-termp (binary-op_tree binary-op-name constant-name fix-name l)))
  :rule-classes
  (:rewrite
   (:forward-chaining
    :trigger-terms
    ((binary-op_tree binary-op-name constant-name fix-name l)))))

(defthm
  pseudo-term-listp-remove-duplicates-memb
  (implies (pseudo-term-listp lst)
	   (pseudo-term-listp (remove-duplicates-memb lst))))