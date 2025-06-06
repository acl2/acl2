; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "hol")
(include-book "terms")
(include-book "../utilities/alist-subsetp")

(defun typ1 (flg x) ; expand-type

; Flg is nil at the top level, when x is intended to be a type expression as
; recognized by weak-hol-typep except that x might use the :arrow*
; abbreviation.  Otherwise, when flg is not nil, x is a list.

  (declare (xargs :guard t))
  (cond
   ((null flg)
    (cond
     ((or (not (true-listp x))
          (atom x))
      x)
     (t (case (car x)
          (:arrow* (typ1 t (cdr x)))
          (:atom x)
          ((:arrow :hash)
           (list 'list (car x) (typ1 nil (nth 1 x)) (typ1 nil (nth 2 x))))
          ((:list :option)
           (list 'list (car x) (typ1 nil (nth 1 x))))
          (t (er hard? 'typ
                 "Illegal type encountered: ~x0."
                 x))))))
   (t
    (case-match x
      ((a b)
       `(list :arrow ,(typ1 nil a) ,(typ1 nil b)))
      ((a & . &)
       `(list :arrow ,(typ1 nil a) ,(typ1 t (cdr x))))
      (& (er hard? 'typ
             "Illegal list following :arrow*, ~x0."
             x))))))

(defmacro typ (type-expr) ; expand-type
  (typ1 nil type-expr))

(in-theory (disable hol-valuep hpp))

(defun hta-name (name)
  (declare (xargs :guard (symbolp name)))
  (suffix-symbol "$HTA" name))

; The theory table has the following keys:
; - :name is the name of the current HOL theory;
; - :prop is the zero-ary predicate that implies each axiom introduced by the
;   theory;
; - :hta-term is a term denoting the hol type alist, which gives meaning to
;   each type (atom <name>) by associating <name> with a term that denotes a
;   set of HOL values of that type;
; - :typed-fns is a list of doublets (fn type), where fn is to be
;   introduced with the given polymorphic type (an :arrow type), in reverse
;   order from their appearance; and
; - :axioms is a list of axioms to be added by the theory, each of which will
;   have a call of :prop as its hypothesis, where these axioms are in reverse
;   order from their appearance.

; Note that :hta-term is not an htap; rather, it is a term denoting an htap.

(local
 (defthm error1-state-p-forward-to-state-p
   (implies (error1-state-p s)
            (state-p s))
   :hints (("Goal" :in-theory (enable error1-state-p)))
   :rule-classes :forward-chaining))

(defun open-theory-fn (name prop hta-term hta-keys ctx state)
  (declare (xargs :stobjs state
                  :guard (error1-state-p state)
                  :guard-hints (("Goal" :in-theory (disable nth nth-expand)))))
  (let* ((world (w state))
         (tbl (table-alist :hol-theory world))
         (hta-name (and (symbolp name) ; for guard
                        (hta-name name))))
    (cond ((table-alist :hol-theory world)
           (let ((old-name (cdr (hons-assoc-equal :name tbl))))
             (er soft ctx
                 "It is illegal to open the theory ~x0 because ~#1~[the ~
                  theory with :name ~x2~/a theory (with no :name)~] is ~
                  currently open."
                 name
                 (if old-name 0 1)
                 old-name)))
          (t
           (value `(progn (defun ,hta-name () ,hta-term)
                          (table :hol-theory nil
                                 '((:name . ,name)
                                   (:prop . ,prop)
                                   (:typed-fns . nil)
                                   (:axioms . nil)
                                   (:theorems . nil)
                                   (:hta-name . ,hta-name)
                                   (:hta-keys . ,hta-keys))
                                 :clear)))))))
  
(defmacro open-theory (name &key prop hta-term hta-keys)
  (declare (xargs :guard (and name
                              (symbolp name)
                              (symbolp prop))))
  (let ((prop (or prop
                  (suffix-symbol "$PROP" name)))
        (hta-term (or hta-term
                      '(hta0)))
        (hta-keys (or hta-keys
                      '(:num :bool))))
    `(make-event (open-theory-fn ',name
                                 ',prop
                                 ',hta-term
                                 ',hta-keys
                                 'open-theory
                                 state))))

(defun hpp-hyps (args arg-types)
  (declare (xargs :guard (and (true-listp args)
                              (true-listp arg-types))))
  (cond ((endp args) nil)
        (t (list* `(hpp ,(car args) hol::hta)
                  `(equal (hp-type ,(car args)) (typ ,(car arg-types)))
                  (hpp-hyps (cdr args) (cdr arg-types))))))

(defun add-index (sym index)
  (declare (xargs :guard (and (symbolp sym)
                              (atom index))))
  (packn-pos (list sym index)
             sym))

(defun hol-axiom (hol-name args arg-types def tbl thmp)
  (declare (xargs :guard (and (symbolp hol-name)
                              (true-listp args)
                              (true-listp arg-types))))
  (let ((hta-name (cdr (hons-assoc-equal :hta-name tbl)))
        (prop (cdr (hons-assoc-equal :prop tbl))))
    `(defthm ,hol-name
       (implies ,(if args
                     `(and ,@(hpp-hyps args arg-types)

; When hol::hta is to be bound to a specific hta, free variable matching is
; more likely to work if we introduce hol::hta after a hypothesis of the form
; (hpp var hol::hta).

                           (alist-subsetp (,hta-name) hol::hta)
                           (force (,prop)))
                   `(force (,prop)))
                ,(if thmp
                     `(equal ,def (hp-true))
                   def)))))

(defun hol-axioms (hol-name defs tbl index thmp acc)

; Index is a natural number to be used as a suffix on hol-name, when there is
; more than one member of defs.  Otherwise flg is nil.

  (declare (xargs :guard (and (symbolp hol-name)
                              (true-listp defs)
                              (or (null index)
                                  (integerp index)))))
  (cond ((endp defs) acc)
        (t (let ((def (car defs))
                 (hol-name-1 (if index
                                 (add-index hol-name index)
                               hol-name)))
             (case-match def
               ((':forall pairs formula)
                (cond
                 ((not (and (symbol-alistp pairs)
                            (doublet-listp pairs)))
                  (er hard? 'defhol
                      "Illegal pairs, ~x0"
                      pairs))
                 (t
                  (hol-axioms hol-name (cdr defs) tbl
                              (and index (1+ index))
                              thmp
                              (cons (hol-axiom hol-name-1
                                               (strip-cars pairs)
                                               (strip-cadrs pairs)
                                               formula
                                               tbl
                                               thmp)
                                    acc)))))
               (&
                (hol-axioms hol-name (cdr defs) tbl
                            (and index (1+ index))
                            thmp
                            (cons (hol-axiom hol-name-1
                                             nil
                                             nil
                                             def
                                             tbl
                                             thmp)
                                  acc))))))))

(defun check-hol-term (fn-lst def hta-keys ctx wrld state)
  (declare (xargs :stobjs state :mode :program))
  (case-match def
    ((':forall pairs term)
     (cond ((and (symbol-alistp pairs)
                 (doublet-listp pairs)
                 (hol-termp term hta-keys fn-lst (strip-cars pairs) wrld))
            (value nil))
           (t (er soft ctx
                  "The following definition for ~&0 has illegal syntax:~|~x1"
                  fn-lst def))))
    (& (cond ((hol-termp def hta-keys fn-lst nil wrld)
              (value nil))
             (t (er soft ctx
                    "The following definition for ~&0 has illegal syntax:~|~x1"
                    fn-lst def))))))

(defun check-hol-terms (fn-lst defs hta-keys ctx wrld state)
  (declare (xargs :stobjs state :mode :program))
  (cond ((null defs) (value nil))
        ((atom defs)
         (er soft ctx
             ":DEFS is not a true list!"))
        (t (er-progn
            (check-hol-term fn-lst (car defs) hta-keys ctx wrld state)
            (check-hol-terms fn-lst (cdr defs) hta-keys ctx wrld state)))))

(defmacro check-hol-terms-event (fn-lst ctx defs)
  `(make-event
    (er-progn
     (check-hol-terms ',fn-lst
                      ',defs
                      (cdr (assoc-eq :hta-keys
                                     (table-alist :hol-theory (w state))))
                      ',ctx
                      (w state)
                      state)
     (value '(value-triple nil)))
    :on-behalf-of :quiet
    :check-expansion t
    :expansion? (value-triple nil)))

(defun check-hol-fns-types (fns hta-keys ctx state)
  (declare (xargs :stobjs state :mode :program))
  (cond ((null fns) (value nil))
        ((atom fns)
         (er soft ctx
             "The :FNS argument must be a true list."))
        ((not (and (consp (car fns))
                   (consp (cdr (car fns)))
                   (null (cddr (car fns)))))
         (er soft ctx
             "The :FNS argument should contain a list of doublets ~
              (two-element lists), but the following member of that list is ~
              not a double:~|~x0"
             (car fns)))
        ((hol-typep+ (cadar fns) hta-keys t)
         (check-hol-fns-types (cdr fns) hta-keys ctx state))
        (t (er soft ctx
               "The function symbol ~x0 is associated in :FNS with the ~
                following illegal type:~|~x1"
               (caar fns)
               (cadar fns)))))

(defmacro check-hol-fns-types-event (fns ctx)
  `(make-event
    (er-progn
     (check-hol-fns-types ',fns
                          (cdr (assoc-eq :hta-keys
                                         (table-alist :hol-theory (w state))))
                          ',ctx
                          state)
     (value '(value-triple nil)))
    :on-behalf-of :quiet
    :check-expansion t
    :expansion? (value-triple nil)))

(defun hol-name (sym)
  (declare (xargs :guard (symbolp sym)))
  (prefix-symbol "HOL{" (suffix-symbol "}" sym)))

(defmacro defhol (&key fns defs thm goal name)
  (declare (xargs :guard
                  (cond (fns (and defs
                                  (not thm)
                                  (not goal)
                                  (not name)))
                        (t (and (not defs)
                                (iff thm (not goal)) ; exactly one of thm, goal
                                name)))))
  (let ((hol-name (hol-name (or name (caar fns)))))
    (cond
     (thm
      (let ((key :theorems))
        `(table :hol-theory
                ,key
                (let ((tbl (table-alist :hol-theory world)))
                  (hol-axioms ',hol-name
                              '(,thm)
                              tbl
                              nil
                              t
                              (cdr (assoc-eq ,key tbl)))))))
     (goal
      (let ((key :goals))
        `(table :hol-theory
                ,key
                (let ((tbl (table-alist :hol-theory world)))
                  (acons ',hol-name ',goal (cdr (assoc-eq ,key tbl)))))))
     (t
      `(progn (check-hol-fns-types-event ,fns defhol)
              (check-hol-terms-event ,(strip-cars fns) defhol ,defs)
              (table :hol-theory
                     :typed-fns
                     (append ',fns
                             (cdr (assoc-eq :typed-fns
                                            (table-alist :hol-theory world)))))
              (table :hol-theory
                     :axioms
                     (let ((tbl (table-alist :hol-theory world)))
                       (hol-axioms ',hol-name
                                   ',defs
                                   tbl
                                   ,(if (cdr defs) 0 nil)
                                   nil
                                   (cdr (assoc-eq :axioms tbl)))))
              (value-triple ',(if (consp fns) fns (car fns))))))))

(defun close-theory-sigs/types (hta-name typed-fns prop sigs type-thms)
  (declare (xargs :guard (and (symbol-alistp typed-fns)
                              (doublet-listp typed-fns)
                              (true-listp sigs)
                              (true-listp type-thms))))
  (cond
   ((endp typed-fns)
    (mv (cons `((,prop) => *)
              (reverse sigs))
        (reverse type-thms)))
   (t
    (let* ((typed-fn (car typed-fns))
           (fn (car typed-fn))
           (type (cadr typed-fn)))
      (close-theory-sigs/types
       hta-name
       (cdr typed-fns)
       prop
       (cons `((,fn *) => *)
             sigs)
       (cons `(defthm ,(add-suffix fn "$TYPE")
                (implies (force (,prop))
                         (and (hpp (,fn (typ ,type)) (,hta-name))
                              (equal (hp-type (,fn (typ ,type)))
                                     (typ ,type)))))
             type-thms))))))

(defun close-theory-locals (typed-fns)
  (declare (xargs :guard (symbol-alistp typed-fns)))
  (cond ((endp typed-fns) nil)
        (t (cons `(local (defun ,(caar typed-fns) (x) x))
                 (close-theory-locals (cdr typed-fns))))))

(defun close-theory-encapsulate (prop hta-name typed-fns axioms theorems)
  (declare (xargs :guard (and (and (symbol-alistp typed-fns)
                                   (doublet-listp typed-fns)
                                   (alistp axioms)
                                   (alistp theorems)))
                  :verify-guards nil))
  (mv-let (sigs types)
    (close-theory-sigs/types hta-name typed-fns prop nil nil)
    `(encapsulate ,sigs
       (local (defun ,prop () nil))
       ,@(close-theory-locals typed-fns)
       ,@types
       ,@axioms
       ,@theorems)))

(local
 (defthm true-listp-mv-nth-1-close-theory-sigs/types
   (implies (true-listp type-thms)
            (true-listp
             (mv-nth 1
                     (close-theory-sigs/types
                      hta-name typed-fns prop sigs type-thms))))))

(verify-guards close-theory-encapsulate)

(defun close-theory-fn (ctx state)
  (declare (xargs :stobjs state :guard (error1-state-p state)))
  (let* ((tbl (table-alist :hol-theory (w state)))
         (name (cdr (hons-assoc-equal :name tbl)))
         (hta-name (and (symbolp name) ; for guard
                        (hta-name name)))
         (typed-fns (reverse (true-list-fix ; for guard
                              (cdr (hons-assoc-equal :typed-fns tbl)))))
         (axioms (reverse (true-list-fix ; for guard
                           (cdr (hons-assoc-equal :axioms tbl)))))
         (theorems (reverse (true-list-fix ; for guard
                             (cdr (hons-assoc-equal :theorems tbl))))))
    (cond ((null tbl)
           (er soft ctx
               "There is no theory to close."))
          ((not (symbolp name)) ; impossible
           (er soft ctx
               "The :NAME entry in the :HOL-THEORY table is ~x0, which is not ~
                a symbol!"
               name))
          ((not (and (symbol-alistp typed-fns)
                     (doublet-listp typed-fns)))
           (er soft ctx
               "The :TYPED-FNS entry in the :HOL-THEORY table is ~x0, which ~
                is not a list of pairs (sym typ) where sym is a symbol."
               typed-fns))
          ((not (alistp axioms))
           (er soft ctx
               "The :AXIOMS entry in the :HOL-THEORY table is ~x0, which ~
                is not a symbol-alistp!"
               axioms))
          ((not (alistp theorems))
           (er soft ctx
               "The :THEOREME entry in the :HOL-THEORY table is ~x0, which ~
                is not a symbol-alistp!"
               theorems))
          (t (value (close-theory-encapsulate
                     (cdr (hons-assoc-equal :prop tbl))
                     hta-name
                     typed-fns
                     axioms
                     theorems))))))

(defmacro close-theory (&key verbose)
  (let ((form `(make-event (close-theory-fn 'close-theory state))))
    (if verbose
        form
      `(with-output :off :all! :on error
         ,form))))

(defun defgoal-form (name wrld)
  (declare (xargs :mode :program))
  (let* ((tbl (table-alist :hol-theory wrld))
         (goals (cdr (assoc-eq :goals tbl)))
         (hol-name (hol-name name))
         (body (cdr (assoc-eq hol-name goals))))
    (and body
         (case-match body
           ((':forall pairs formula)
            (cond
             ((not (and (symbol-alistp pairs)
                        (doublet-listp pairs)))
              (er acl2::hard 'defgoal
                  "Illegal pairs for name ~x0: ~x1"
                  name pairs))
             (t
              (hol-axiom hol-name
                         (strip-cars pairs)
                         (strip-cadrs pairs)
                         formula
                         (table-alist :hol-theory wrld)
                         t))))
           (&
            (hol-axiom (hol-name name)
                       nil
                       nil
                       body
                       (table-alist :hol-theory wrld)
                       t))))))

(defmacro defgoal (name body &rest rest)
  `(make-event
    (let ((form (defgoal-form ',name (w state))))
      (cond
       ((null form)
        (er acl2::soft 'defgoal
            "There is no goal associated with the name, ~x0."
            ',name))
       ((not (equal ',body (caddr form)))
        (er acl2::soft 'defgoal
            "MISMATCH: The body of the defgoal form submitted ~
             for the name ~x0 was~|~x1~|but the expected body was ~x2."
            ',name ',body (caddr form)))
       (t
        (value (list* 'defthm (cadr form) ',body ',rest)))))))
