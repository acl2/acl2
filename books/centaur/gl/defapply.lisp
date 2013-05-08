


(in-package "GL")

(include-book "clause-processors/generalize" :dir :system)

(include-book "tools/mv-nth" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "gl-util")

(include-book "misc/hons-help2" :dir :system)

(defthmd len-open-for-defapply
  (equal (len (cons a b))
         (+ 1 (len b))))

(defthmd nth-open-for-defapply
  (implies (syntaxp (quotep n))
           (equal (nth n (cons a b))
                  (if (zp n)
                      a
                    (nth (1- n) b)))))

(defstub apply-stub (f args) t)

(program)

(defun make-list-of-nths (sym start n)
  (declare (xargs :guard (and (natp start)
                              (natp n))))
  (if (zp n)
      nil
    (cons `(nth ,start ,sym)
          (make-list-of-nths sym (1+ start) (1- n)))))
  
(defmacro ecc (call)
  (declare (xargs :guard (consp call)))
  (if (member-eq (car call) acl2::*ec-call-bad-ops*)
      call
    `(ec-call ,call)))

(defun make-mv-call (f args world)
  (let* ((stobjs-out (getprop f 'stobjs-out nil 'current-acl2-world world)))
    (if (and stobjs-out (< 1 (length stobjs-out)))
        `(mv-list ,(length stobjs-out)
                  (ecc (,f . ,args)))
      `(ecc (,f . ,args)))))

(defun make-apply-entry (f world)
  (let* ((formals (getprop f 'formals nil 'current-acl2-world world)))
    `((and (eq f ',f)
           (true-listp args)
           (eql (len args) ,(length formals)))
      ,(make-mv-call f (make-list-of-nths 'args 0 (length formals)) world))))

(defun make-apply-clique-entries (clique world)
  (if (atom clique)
      nil
    (cons (make-apply-entry (car clique) world)
          (make-apply-clique-entries (cdr clique) world))))

(defun make-apply-entries (fns world acc)
  (if (atom fns)
      (prog2$ (flush-hons-get-hash-table-link acc)
              nil)
    (if (hons-get (car fns) acc)
        (make-apply-entries (cdr fns) world acc)
      (let* ((clique (or (wgetprop (car fns) 'recursivep) (list (car fns))))
             (acc (acl2::hons-put-list clique t acc)))
        (append (make-apply-clique-entries clique world)
                (make-apply-entries (cdr fns) world acc))))))

(defun double-rewrite-formals (formals)
  (if (atom formals)
      nil
    (cons `(double-rewrite ,(car formals))
          (double-rewrite-formals (cdr formals)))))

(defun apply-rw-name (apply fn)
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name apply) "-" (symbol-name fn))
   apply))

(defun apply-rw-thms (clique name world)
  (if (atom clique)
      nil
    (let* ((fn (car clique))
           (formals (wgetprop fn 'formals)))
      (cons `(defthm ,(apply-rw-name name fn)
               (equal (,name ',fn (list . ,formals))
                      (,fn . ,(double-rewrite-formals formals)))
               :hints (("goal" :in-theory
                        (e/d** (minimal-theory
                                ;; (:executable-counterpart-theory :here)
                                (equal) (len) (nth) (binary-+) (not)
                                (zp)
                                (:definition ,name) 
                                len-open-for-defapply
                                nth-open-for-defapply))
                        :do-not '(preprocess))
                       (and stable-under-simplificationp
                            ;; Special case for HIDE and functions that
                            ;; normalize to a constant.
                            '(:expand ((:free ,formals (,fn . ,formals)))))))
            (apply-rw-thms (cdr clique) name world)))))
            
                 


(defun make-apply-rewrites (name fns world)
  (if (atom fns)
      nil
    (append (b* ((recursivep (getprop (car fns) 'recursivep nil
                                      'current-acl2-world world)))
              (apply-rw-thms (or recursivep (list (car fns))) name world))
            (make-apply-rewrites name (cdr fns) world))))

(def-ruleset! defapply-guards '((:executable-counterpart eqlablep)
                                (:executable-counterpart equal)))

(defun mk-arity-table (lst w)
  (if (atom lst)
      nil
    (cons (cons (car lst)
                (len (getprop (car lst) 'formals nil 'current-acl2-world w)))
          (mk-arity-table (cdr lst) w))))


(defun make-apply (name fns world)
  (declare (xargs :mode :program))
  `(progn
     (defun ,(intern-in-package-of-symbol
              (concatenate 'string (symbol-name name) "-ARITIES")
              name)
       ()
       (declare (xargs :guard t))
       ',(mk-arity-table fns world))
     (encapsulate nil
       (local (in-theory (e/d** ((:ruleset defapply-guards)
                                 (:rules-of-class :type-prescription :here)))))
       (defund ,name (f args)
         (declare (xargs :guard t
                         :normalize nil))
         (cond
          ,@(make-apply-entries fns world nil)
          (t (apply-stub f args))))
       (table g-apply-table ',name ',fns))
     (encapsulate nil
       (local (in-theory (e/d** ((:ruleset defapply-guards)
                                 (:rules-of-class :type-prescription
                                                  :here)))))
       . ,(make-apply-rewrites name fns world))))


;; Functions that return MVs need to be passed to DEFAPPLY in dependency
;; order.  This is because we need to prove, if (FOO X) returns three values,
;; (EQUAL (LIST (MV-NTH 0 (FOO X))
;;              (MV-NTH 1 (FOO X))
;;              (MV-NTH 2 (FOO X)))
;;        (FOO X))
;; If one of the branches of FOO is a call of BAR, also returning three values,
;; then the proof of the above will reduce to the same theorem about BAR.
;; Therefore we need to have proven this about BAR before tackling FOO.
;; It could happen that this problem occurs in a mutually-recursive fashion, in which
;; case we'd need to introduce a flag function, etc.  Blech.

(defmacro defapply (name fns)
  `(make-event (make-apply ',name ',fns (w state))))
