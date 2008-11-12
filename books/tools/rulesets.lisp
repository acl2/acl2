

(in-package "ACL2")

(program)


(defun get-ruleset (name world)
  (let* ((ruleset-alist (table-alist 'ruleset-table world)))
    (cdr (assoc name ruleset-alist))))

(defmacro ruleset (name)
  `(get-ruleset ,name world))

(defun is-ruleset (name world)
  (let* ((ruleset-alist (table-alist 'ruleset-table world)))
    (consp (assoc name ruleset-alist))))

(defun ruleset-designatorp (x world)
  (cond ((or (symbolp x)
             (and (consp x)
                  (not (keywordp (car x)))))
         (theoryp! (list x) world))
        ((runep x world) t)
        ((and (consp x) (symbolp (car x)) (eq (cdr x) nil)) t)
        ((and (consp x)
              (consp (cdr x))
              (not (cddr x)))
         (if (eq (car x) :ruleset)
             (or (is-ruleset (cadr x) world)
                 (cw "**NOTE**:~%~x0 is not a ruleset.~%" (cadr x)))
           (or (eq (car x) :executable-counterpart-theory)
               (eq (car x) :current-theory)
               (cw "**NOTE**:~%~x0 is not a valid keyword for a ruleset ~
designator.~%" (car x)))))
        (t (cw "**NOTE**:~%~x0 is not a valid ruleset designator.~%" x))))

(defun ruleset-designator-listp (x world)
  (if (atom x)
      (eq x nil)
    (and (ruleset-designatorp (car x) world)
         (ruleset-designator-listp (cdr x) world))))





(defmacro def-ruleset (name form)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (let ((world (w state))
          (name ',name))
      (if (is-ruleset name world)
          (er soft 'def-ruleset
              "~x0 is already a ruleset.  Use add-to-ruleset or def-ruleset! ~
               instead.~%" name)
        (let ((result ,form))
          (if (ruleset-designator-listp result world)
              (value `(table ruleset-table ',name ',result))
            (er soft 'def-ruleset "Invalid ruleset specified~%")))))))

(defmacro add-to-ruleset (name form)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (let ((world (w state))
          (name ',name))
      (if (is-ruleset name world)
          (let ((result ,form))
            (if (ruleset-designator-listp result world)
                (value `(table ruleset-table ',name
                               (union-equal ',result (ruleset ',name))))
              (er soft 'add-to-ruleset "Invalid ruleset specified~%")))
        (er soft 'add-to-ruleset
            "~x0 is not already a ruleset.  Use def-ruleset, def-ruleset! ~
             or add-to-ruleset! instead.~%" name)))))

(defmacro def-ruleset! (name form)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (let* ((world (w state))
           (name ',name)
           (result ,form))
      (if (ruleset-designator-listp result world)
          (value `(table ruleset-table ',name ',result))
        (er soft 'def-ruleset! "Invalid ruleset specified~%")))))

(defmacro add-to-ruleset! (name form)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (let* ((world (w state))
           (name ',name)
           (result ,form))
      (if (ruleset-designator-listp result world)
          (value `(table ruleset-table ',name
                         (union-equal ',result (ruleset ',name))))
        (er soft 'add-to-ruleset! "Invalid ruleset specified~%")))))


;; This is fragile; we don't recursively check rulesets that we're expanding.
(defun expand-ruleset1 (x world)
  (if (atom x)
      nil
    (let ((des (car x)))
      (if (or (atom des) (runep des world))
          (cons des (expand-ruleset1 (cdr x) world))
        (if (null (cdar x))
            (cons `(:executable-counterpart ,(caar x))
                  (expand-ruleset1 (cdr x) world))
          (case (car des)
            (:ruleset
             (append (expand-ruleset1 (ruleset (cadr des)) world)
                     (expand-ruleset1 (cdr x) world)))
            (:executable-counterpart-theory
             (append (executable-counterpart-theory (cadr des))
                     (expand-ruleset1 (cdr x) world)))
            (:current-theory
             (append (executable-counterpart-theory (cadr des))
                     (expand-ruleset1 (cdr x) world)))))))))

(defun expand-ruleset (x world)
  (if (ruleset-designator-listp x world)
      (expand-ruleset1 x world)
    (er hard 'expand-ruleset "~x0 is not a valid ruleset.~%" x)))


(defmacro enable* (&rest x)
  `(union-theories-fn
    (current-theory :here)
    (expand-ruleset ',x world)
    t world))

(defmacro disable* (&rest x)
  `(set-difference-theories-fn
    (current-theory :here)
    (expand-ruleset ',x world)
    t world))


(defun e/d*-fn (theory e/d-list enable-p)
  (declare (xargs :guard (and (true-list-listp e/d-list)
                              (or (eq enable-p t)
                                  (eq enable-p nil)))))
  (cond ((atom e/d-list) theory)
        (enable-p (e/d*-fn `(UNION-THEORIES ,theory
                                           (expand-ruleset ',(car e/d-list) world))
                           (cdr e/d-list) nil))
        (t (e/d*-fn `(SET-DIFFERENCE-THEORIES ,theory
                                              (expand-ruleset ',(car e/d-list) world))
                    (cdr e/d-list) t))))

(defmacro e/d** (&rest theories)
  (declare (xargs :guard (true-list-listp theories)))
  (cond ((atom theories) nil)
        (t (e/d*-fn nil theories t))))

(defmacro e/d* (&rest theories)
  (declare (xargs :guard (true-list-listp theories)))
  (cond ((atom theories) '(current-theory :here))
        (t (e/d*-fn '(current-theory :here)
                    theories t))))

(defmacro ruleset-theory (ruleset)
  `(expand-ruleset (ruleset ,ruleset) world))


#||

(logic)

(local
 (encapsulate
  nil
  (include-book
   ;; This is on a separate line so that this book won't appear to depend on
   ;; the make-event subdir.
   "make-event/assert" :dir :system)

 (def-ruleset! foo '(append reverse))

 (def-ruleset! bar '((:ruleset foo) nth))

 (add-to-ruleset foo '((consp)))

 (in-theory (enable* (:ruleset foo)))

 (assert! (let ((ens (ens state)))
            (active-runep '(:definition binary-append))))

 (in-theory (disable* (:ruleset bar)))

 (assert! (let ((ens (ens state)))
            (not (active-runep '(:definition binary-append)))))

 (in-theory (e/d* ((:ruleset bar)) ((:ruleset foo))))

 (assert! (let ((ens (ens state)))
            (and (not (active-runep '(:definition binary-append)))
                 (active-runep '(:definition nth)))))))

||#
