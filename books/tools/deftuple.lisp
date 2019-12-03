(in-package "ACL2")

(include-book "types-misc")
(include-book "std/util/bstar" :dir :system)
(program)



;; (defun pretty-args (hons-opt args acc)
;;   (if (atom args)
;;       acc
;;     (pretty-args hons-opt (cdr args)
;;                  (cons `(lst (if ,(car args)
;;                                  (,(if hons-opt 'hons 'cons)
;;                                   (,(if hons-opt 'hons-list 'list)
;;                                    ',(car args) ,(car args))
;;                                   lst)
;;                                lst))
;;                        acc))))

(defun pretty-args (hons-opt args)
  (if (atom args)
      nil
    (if hons-opt
        (cons `(hons-list ',(car args) ,(car args))
              (pretty-args hons-opt (cdr args)))
      (cons `(list ',(car args) ,(car args))
            (pretty-args hons-opt (cdr args))))))

#|
(defun int-sym (i s)
  (cons i s))

or for pretty

(defun int-sym (i s)
  (list 'intsym (list 'i i) (list 's s)))
||#
(defun deftuple-constructor (name components guard-opt hons-opt
                                  compact-opt pretty-opt)
  (let* ((args (components-names components))
         (cons (if hons-opt 'hons 'cons)))
    `(defun ,name ,args
       ,@(if guard-opt
             `((declare (xargs :guard t)))
           nil)
       ,(if pretty-opt
            `(,(if hons-opt 'hons-list 'list)
              ',name
              ,@(pretty-args hons-opt args))
          (if compact-opt
              (argtree cons args)
            `(,(if hons-opt 'hons-list 'list) ,@args))))))






;; (defun pretty-structurep (lst)
;;   (if (endp lst)
;;       nil
;;     (let ((arg (component-name (car lst))))
;;       (cons `(let ((,arg (assoc ',arg (cdr x))))
;;                (or (not ,arg) (consp (cdr ,arg))))
;;             (pretty-structurep (cdr lst))))))

(defun pretty-structurep (components x)
  (if (atom components)
      `((eq ,x nil))
    (let ((n (component-name (car components))))
      `((consp ,x)
        (consp (car ,x))
        (eq (caar ,x) ',n)
        (consp (cdar ,x))
        (eq (cddar ,x) nil)
        ,@(pretty-structurep (cdr components) `(cdr ,x))))))

#|
(defun int-sym-structurep (x) (consp x))

or


||#
(defun deftuple-structure-recognizer (name comps guard-opt
                                           compact-opt pretty-opt)
  (let* ((ncomps (length comps))
         (tests (if pretty-opt
                    `((consp x) (eq (car x) ',name)
                      ,@(pretty-structurep comps '(cdr x)))
                  (if compact-opt
                      (recog-consp-list ncomps 'x)
                    `((true-listp x) (= (length x) ,ncomps))))))
    `(defun ,(appsyms (list name 'structurep)) (x)
       ,@(if guard-opt `((declare (xargs :guard t))) nil)
       ,@(if (< (len tests) 2)
             tests
           `((and ,@tests))))))


#|
(defthm int-sym-structurep-compound-recognizer
  (implies (int-sym-structurep x)
           (consp x))
  :rule-classes :compound-recognizer)
||#
(defun deftuple-compound-rec-thm (name compact-opt)
  `(defthm ,(packsyms (list name 'p-compound-recognizer))
     (implies (,(appsyms (list name 'structurep)) x)
              ,(if compact-opt `(consp x)
                 `(and (consp x) (true-listp x))))
              :rule-classes :compound-recognizer))


#|
(defthm int-sym-structurep-int-sym
  (int-sym-structurep (int-sym i s))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((int-sym i s)))))
||#
(defun deftuple-constructor-structure-recognizer-thm (name components)
  (let ((call (cons name (components-names components))))
    `(defthm ,(packsyms (list name '-structurep- name))
       (,(appsyms (list name 'structurep)) ,call)
       :rule-classes ((:forward-chaining :trigger-terms (,call))))))




#|
(defun int-sym-i (x)
  (car x))

(defun int-sym-s (x)
  (cdr x))
||#
(defun deftuple-accessor (name component ncomps n guard-opt
                               compact-opt pretty-opt)
  (let ((rec (appsyms (list name 'structurep)))
        (acc (if pretty-opt
                 (if (eq guard-opt :safe)
                     `(safe-car
                       (cdr (gentle-assoc ',(component-name component)
                                          (safe-cdr x))))
                   `(cadr (assoc-eq ',(component-name component)
                                    (cdr x))))
               (if compact-opt
                   (tree-accessor n ncomps 'x guard-opt)
                 (if (eq guard-opt :safe)
                     `(safe-nth ,(1- n) x)
                   `(nth ,(1- n) x))))))
    `(defun ,(appsyms (list name (component-name component))) (x)
       ,@(if guard-opt
             (if (eq guard-opt :safe)
                 `((declare (xargs :guard t)))
               `((declare (xargs :guard (,rec x)))))
           nil)
       ,acc)))

(defun deftuple-accessors-help (name components ncomps n guard-opt
                                compact-opt pretty-opt)
  (if (atom components)
      nil
    (cons (deftuple-accessor name (car components) ncomps n guard-opt
            compact-opt pretty-opt)
          (deftuple-accessors-help name (cdr components) ncomps (1+ n)
            guard-opt compact-opt pretty-opt))))

(defun deftuple-accessors (name components guard-opt compact-opt pretty-opt)
  (deftuple-accessors-help name components (length components) 1
    guard-opt compact-opt pretty-opt))


#|
(defthm int-sym-int-sym-i
  (equal (int-sym-i (int-sym i s)) i))

(defthm int-sym-int-sym-s
  (equal (int-sym-s (int-sym i s)) s))
||#

(defun deftuple-constructor-component-thms (name components call)
  (if (atom components)
      nil
    (cons (let* ((arg (component-name (car components)))
                 (acc (appsyms (list name arg))))
            `(defthm ,(appsyms (list name name arg))
               (equal (,acc ,call) ,arg)))
          (deftuple-constructor-component-thms name (cdr components) call))))

(defun deftuple-acc-call-list (name components)
  (if (atom components)
      nil
    (let* ((cname (component-name (car components)))
           (acc (appsyms (list name cname))))
      (cons `(,acc x)
            (deftuple-acc-call-list name (cdr components))))))
#|
(defthm int-sym-elim
  (implies (int-sym-structurep x)
           (equal (int-sym (int-sym-i x)
                           (int-sym-s x))
                  x))
  :rule-classes (:rewrite :elim))
||#
(defun deftuple-elim-thm (name components)
  (let ((accs (deftuple-acc-call-list name components)))
    `(defthm ,(appsyms (list name 'elim))
       (implies (,(appsyms (list name 'structurep)) x)
                (equal (,name ,@accs)
                       x))
       :rule-classes (:rewrite :elim)
       :hints (("Goal" :in-theory (enable true-listp-len-0
                                          nth-open))))))

#|
(def-pattern-match-constructor
  int-sym
  :unconditional
  (int-sym-i int-sym-s))
||#
(defun deftuple-binder (name components)
  `(def-patbind-macro ,name
     ,(accessor-list (list (cons name components)) components)))



;; (defun component-recognizer-list-compact (obj components)
;;   (cond ((endp components)
;;          nil)
;;         ((endp (cdr components))
;;          (let ((type (component-type (car components))))
;;            (if type
;;                `((,type ,obj))
;;              nil)))
;;         (t (mv-let (first second)
;;                    (split-list (floor (len components) 2) components
;;                                nil)
;;                    (append (component-recognizer-list-compact
;;                             `(car ,obj) first)
;;                            (component-recognizer-list-compact
;;                             `(cdr ,obj) second))))))

;; (defun component-recognizer-list-pretty (components)
;;   (if (endp components)
;;       nil
;;     (let ((type (component-type (car components)))
;;           (name (component-name (car components))))
;;       (if type
;;           (cons `(,type (cadr (assoc-eq ',name (cdr x))))
;;                 (component-recognizer-list-pretty
;;                  (cdr components)))
;;         (component-recognizer-list-pretty (cdr components))))))

;; (defun component-recognizer-list (obj components n)
;;   (if (atom components)
;;       nil
;;     (cons `(,(component-type (car components)) (nth ,n ,obj))
;;           (component-recognizer-list obj (cdr components) (1+ n)))))

(defun accessor-type-list (name components)
  (if (atom components)
      nil
    (let ((type (component-type (car components)))
          (cname (component-name (car components))))
      (if type
          (cons `(,type (,(appsyms (list name cname)) x))
                (accessor-type-list name (cdr components)))
        (accessor-type-list name (cdr components))))))
#|
(defun int-symp (x)
  (and (int-sym-structurep x)
       (integerp (int-sym-i x))
       (symbolp (int-sym-s x))))
||#
(defun deftuple-recognizer (name components guard-opt)
  (let* ((tests (accessor-type-list name components)))
    `(defun ,(packsyms (list name 'p)) (x)
       ,@(if guard-opt
             `((declare (xargs :guard t)))
           nil)
       (and (,(appsyms (list name 'structurep)) x)
            ,@tests))))

#|
(defthm int-symp-int-sym-structurep
  (implies (int-symp x)
           (int-sym-structurep x))
  :rule-classes (:rewrite :forward-chaining))
||#
(defun deftuple-recognizer-structure-recognizer (name)
  `(defthm ,(packsyms (list name 'p- name '-structurep))
     (implies (,(packsyms (list name 'p)) x)
              (,(appsyms (list name 'structurep)) x))
  :rule-classes (:rewrite :forward-chaining)))

#|
(defthm int-symp-i
  (implies (int-symp x)
           (integerp (int-sym-i x))))

(defthm int-symp-s
  (implies (int-symp x)
           (symbolp (int-sym-s x))))
||#

(defun deftuple-component-type-thms (name rec components)
  (if (atom components)
      nil
    (let ((type (component-type (car components)))
          (acc (appsyms (list name (component-name
                                    (car components))))))
      (if type
          (cons
           `(defthm ,(appsyms (list rec (component-name
                                           (car components))))
                (implies (,rec x)
                         (,type (,acc x))))
;;            `(make-event
;;              `(defthm ,',(appsyms (list rec (component-name
;;                                            (car components))))
;;                 (implies (,',rec x)
;;                          (,',type (,',acc x)))
;;                 ,@(if (most-recent-enabled-recog-tuple
;;                        ',type
;;                        (w state)
;;                        (global-val 'global-enabled-structure
;;                                    (w state)))
;;                       '(:rule-classes (:rewrite :type-prescription))
;;                     nil)))
           (deftuple-component-type-thms name rec (cdr components)))
        (deftuple-component-type-thms name rec (cdr components))))))


(defun component-type-list (components)
  (if (atom components)
      nil
    (let ((type (component-type (car components)))
          (name (component-name (car components))))
      (if type
          (cons `(,type ,name)
                (component-type-list (cdr components)))
        (component-type-list (cdr components))))))



#|
(defthm int-symp-int-sym
  (implies (and (integerp i)
                (symbolp s))
           (int-symp (int-sym i s)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms ((int-sym i s)))))
||#
(defun deftuple-recognizer-constructor-thm (name components)
  (let* ((tests (component-type-list components))
         (call `(,name ,@(components-names components)))
         (concl `(,(packsyms (list name 'p))
                  ,call)))
  `(defthm ,(packsyms (list name 'p- name))
     ,(if (< 0 (len tests))
          `(equal ,concl
                  ,@(if (< 1 (len tests))
                        `((and ,@tests))
                      tests))
        `(equal ,concl t)))))


(defun deftuple-defs (name components guard-opt hons-opt compact-opt
                           pretty-opt)
  `(,(deftuple-constructor name components guard-opt hons-opt
       compact-opt pretty-opt)
    ,(deftuple-structure-recognizer name components guard-opt
       compact-opt pretty-opt)
    ,(deftuple-compound-rec-thm name compact-opt)
    ,(deftuple-constructor-structure-recognizer-thm name components)
    ,@(deftuple-accessors name components guard-opt compact-opt pretty-opt)
    ,@(deftuple-constructor-component-thms name components
        `(,name ,@(components-names components)))
    ,(deftuple-elim-thm name components)
    ,(deftuple-binder name components)
    ,(deftuple-recognizer name components guard-opt)
    ,(deftuple-recognizer-structure-recognizer name)
    ,@(deftuple-component-type-thms name (packsyms (list name 'p))
       components)
    ,(deftuple-recognizer-constructor-thm name components)))

(defun deftuple-fn (name components kwalist)
  (let* ((guard-opt (kwassoc :guard t kwalist))
         (hons-opt (kwassoc :hons nil kwalist))
         (arithmetic-opt (kwassoc :arithmetic t kwalist))
         (pretty-opt (kwassoc :pretty nil kwalist))
         (compact-opt (and (not pretty-opt)
                           (kwassoc :compact nil kwalist)))
         (before-label (appsyms (list 'before name)))
         (difftheory `(set-difference-theories (current-theory :here)
                                               (current-theory
                                                ',before-label)))
         (function-theory (appsyms (list name 'functions)))
         (exec-theory (appsyms (list name 'executable-counterparts))))
    `(encapsulate
      nil
      ,@(if arithmetic-opt
            `((local (include-book
                      "arithmetic/top-with-meta" :dir :system)))
          nil)
      (deflabel ,before-label)
      ,@(deftuple-defs name components guard-opt hons-opt compact-opt
          pretty-opt)

      (deftheory ,function-theory
        (rules-of-type :DEFINITION ,difftheory))
      (deftheory ,exec-theory
        (rules-of-type :EXECUTABLE-COUNTERPART ,difftheory))
      (deftheory ,(appsyms (list name 'theorems))
        (set-difference-theories ,difftheory
                                 (union-theories
                                  (theory ',function-theory)
                                  (theory ',exec-theory))))
      (in-theory (disable ,function-theory ,exec-theory))
      (deftheory ,(appsyms (list name 'entire-theory))
        (set-difference-theories (universal-theory :here)
                                 (universal-theory ',before-label))))))

(defun translate-kwalist (kwalist)
  (if (atom kwalist)
      nil
    `(cons (cons (quote ,(caar kwalist))
                 ,(cdar kwalist))
           ,(translate-kwalist (cdr kwalist)))))


(defmacro deftuple-help (name components kwalist)
  (deftuple-fn name (munge-components components) kwalist))

(defmacro deftuple (name &rest kw-and-components)
  (mv-let (components kwalist)
          (strip-keywords kw-and-components)
          `(make-event
            (deftuple-fn ',name (munge-components ',components)
              ,(translate-kwalist kwalist)))))




;; (defun deftuple-function-defs (name components guard-opt hons-opt
;;                                     compact-opt)
;;   `(,(deftuple-recognizer name components guard-opt compact-opt)
;;     ,(deftuple-constructor name components guard-opt hons-opt
;;        compact-opt)
;;     ,@(deftuple-accessors name components guard-opt compact-opt)))

;; (defun deftuple-recognizer-constructor-thm (product)
;;   (let* ((tests (type-checklist (product-components product)))
;;          (constructor (product-name product))
;;          (constr-call (constructor-call product))
;;          (recognizer (product-recognizer product)))
;;     `(defthm ,(appsyms (list recognizer constructor))
;;        (implies (and ,tests)
;;                 (,recognizer ,constr-call)))))

;; (defun deftuple-accessor-type-thm (product)
;;   (let ((checklist (accessor-type-checklist product))
;;         (prodname (product-name product))
;;         (precog (product-recognizer product)))
;;     (if (eq checklist t)
;;         nil
;;       `((defthm ,(appsyms (list prodname 'accessor-types))
;;           (implies (,precog x)
;;                    ,checklist)
;;           :rule-classes (:rewrite :type-prescription))))))



;; (defun deftuple-theorems (name components compact-opt)
;;   (let ((product (list (cons name components))))
;;     `(,(product-compound-rec-thm product compact-opt)
;;       ,(deftuple-recognizer-constructor-thm product)
;;       ,(product-elim-thm product compact-opt)
;;       ,@(deftuple-accessor-type-thm product)
;;       ,@(product-arg-thms product components))))

;; (defun deftuple-defs (name components guard-opt hons-opt compact-opt)
;;   (append (deftuple-function-defs name components guard-opt hons-opt
;;             compact-opt)
;;           (deftuple-theorems name components compact-opt)
;;           (list (deftuple-pattern-matcher name components))))






;; (defun deftuple-fn (name components kwalist)
;;   (let* ((guard-opt (kwassoc :guard nil kwalist))
;;          (hons-opt (kwassoc :hons nil kwalist))
;;          (compact-opt (kwassoc :compact t kwalist))
;;          (before-label (appsyms (list 'before name)))
;;          (difftheory `(set-difference-theories (current-theory :here)
;;                                                (current-theory
;;                                                 ',before-label)))
;;          (function-theory (appsyms (list name 'functions)))
;;          (exec-theory (appsyms (list name 'executable-counterparts))))
;;     `(encapsulate
;;       nil
;;       (deflabel ,before-label)
;;       ,@(deftuple-defs name components guard-opt hons-opt compact-opt)

;;       (deftheory ,function-theory
;;         (rules-of-type :DEFINITION ,difftheory))
;;       (deftheory ,exec-theory
;;         (rules-of-type :EXECUTABLE-COUNTERPART ,difftheory))
;;       (deftheory ,(appsyms (list name 'theorems))
;;         (set-difference-theories ,difftheory
;;                                  (union-theories
;;                                   (theory ',function-theory)
;;                                   (theory ',exec-theory))))
;;       (in-theory (disable ,function-theory ,exec-theory))
;;       (deftheory ,(appsyms (list name 'entire-theory))
;;         (set-difference-theories (universal-theory :here)
;;                                  (universal-theory ',before-label))))))

;; (defmacro deftuple (name &rest kw-and-components)
;;   (mv-let (components kwalist)
;;           (strip-keywords kw-and-components)
;;           (deftuple-fn name (munge-components components)
;;             kwalist)))

#| Tests:
(deftuple cws-node
  :guard t
  (natp size)
  onset
  offset)

||#


#|
Model:



(deftuple int-sym (integerp i) (symbolp s))

expands to

(defun int-sym (i s) (cons i s))

(defun int-sym-structurep (x) (consp x))

(defthm int-sym-structurep-compound-recognizer
  (implies (int-sym-structurep x)
           (consp x))
  :rule-classes :compound-recognizer)

(defthm int-sym-structurep-int-sym
  (int-sym-structurep (int-sym i s))
  :rule-classes (:forward-chaining
                 :trigger-terms ((int-sym i s))))

(defun int-sym-i (x)
  (car x))

(defun int-sym-s (x)
  (cdr x))

(defthm int-sym-int-sym-i
  (equal (int-sym-i (int-sym i s)) i))

(defthm int-sym-int-sym-s
  (equal (int-sym-s (int-sym i s)) s))

(defthm int-sym-elim
  (implies (int-sym-structurep x)
           (equal (int-sym (int-sym-i x)
                           (int-sym-s x))
                  x))
  :rule-classes (:rewrite :elim))

(def-pattern-match-constructor
  int-sym
  :unconditional
  (int-sym-i int-sym-s))

(defun int-symp (x)
  (and (int-sym-structurep x)
       (integerp (int-sym-i x))
       (symbolp (int-sym-s x))))

(defthm int-symp-int-sym-structurep
  (implies (int-symp x)
           (int-sym-structurep x))
  :rule-classes (:rewrite :forward-chaining))

(defthm int-symp-i
  (implies (int-symp x)
           (integerp (int-sym-i x))))

(defthm int-symp-s
  (implies (int-symp x)
           (symbolp (int-sym-s x))))

(defthm int-symp-int-sym
  (equal (int-symp (int-sym i s))
         (and (integerp i)
              (symbolp s))))





(encapsulate
 (((constructor * *) => *)
  ((recognizer *) => *)
  ((accessor1 *) => *)
  ((accessor2 *) => *))
 (local (defun constructor (x y) (cons x y)))
 (local (defun recognizer (x) (consp x)))
 (local (defun accessor1 (x) (car x)))
 (local (defun accessor2 (x) (cdr x)))
 (defthm constructor-recognizer
   (recognizer (constructor x y)))
 (defthm accessor1-constructor
   (equal (accessor1 (constructor x y))
                     x))
 (defthm accessor2-constructor
   (equal (accessor2 (constructor x y))
          y))
 (defthm constructor-elim
   (implies (recognizer x)
            (equal (constructor (accessor1 x)
                                (accessor2 x))
                   x)))
 (defthm constructor-acl2-count
   (equal (acl2-count (constructor x y))
          (+ 1 (acl2-count x) (acl2-count y)))))

(defthm not-acl2-count-equal-implies-not-equal
  (implies (not (equal (acl2-count (constructor a b))
                       (acl2-count x)))
           (not (equal (constructor a b) x))))

(thm (not (equal (constructor a b) a)))

(thm (not (equal a (constructor a b))))

(defun constructor-nest-fn (car n acc)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      acc
    (constructor-nest-fn car (1- n) `(constructor ,car ,acc))))

(defmacro constructor-nest (car cdr n)
  (constructor-nest-fn car n cdr))

(thm (not (equal (constructor-nest b a 200) a)))

(thm (not (equal (constructor b (constructor b (constructor b a))) a)))


(defun cons-nest-fn (car n acc)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      acc
    (cons-nest-fn car (1- n) `(cons ,car ,acc))))

(defmacro cons-nest (car cdr n)
  (cons-nest-fn car n cdr))




||#


#|
defsum example:

(defun ptype (x)
  (declare (xargs :guard (consp x)))
  (car x))

(defsum nest
  (single (nest a))
  (atomic v))

(defun single (a)
  (declare (xargs :guard t))
  (cons 'single a))

(defthm ptype-single
  (equal (ptype (single a))
         'single))

(defun atomic (v)
  (declare (xargs :guard t))
  (cons 'atomic v))

(defthm ptype-atomic
  (equal (ptype (atomic v))
         'atomic))

(defun singlep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (eq (ptype x) 'single)))

(defthm singlep-single
  (singlep (single a))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((single a)))))

(defthm singlep-ptype
  (implies (singlep x)
           (equal (ptype x) 'single))
  :rule-classes :forward-chaining)

(defthm singlep-check-ptype
  (implies (not (equal (ptype x) 'single))
           (not (equal (single a) x))))

(defun atomicp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (eq (ptype x) 'atomic)))

(defthm atomicp-atomic
  (atomicp (atomic v))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((atomic v)))))

(defthm atomicp-ptype
  (implies (atomicp x)
           (equal (ptype x) 'atomic))
  :rule-classes :forward-chaining)

(defthm atomicp-check-ptype
  (implies (not (equal (ptype x) 'atomic))
           (not (equal (atomic v) x))))


(defun single-a (x)
  (declare (xargs :guard (singlep x)))
  (cdr x))

(defthm single-a-single
  (equal (single-a (single a)) a))

(defthm single-elim
  (implies (singlep x)
           (equal (single (single-a x))
                  x))
  :rule-classes (:rewrite :elim))

(defthm single-acl2-count
  (equal (acl2-count (single a))
         (+ 1 (acl2-count a))))

(defthm single-a-acl2-count
  (implies (equal (ptype x) 'single)
           (< (acl2-count (single-a x))
              (acl2-count x))))

(defun atomic-v (x)
  (declare (xargs :guard (atomicp x)))
  (cdr x))

(defthm atomic-v-atomic
  (equal (atomic-v (atomic v)) v))

(defthm atomic-elim
  (implies (atomicp x)
           (equal (atomic (atomic-v x))
                  x))
  :rule-classes (:rewrite :elim))

(defthm atomic-acl2-count
  (equal (acl2-count (atomic v))
         (+ 1 (acl2-count v))))

(def-pattern-match-constructor  (x)
  single
  (eq (ptype x) 'single)
  (single-a))

(def-pattern-match-constructor  (x)
  atomic
  (eq (ptype x) 'atomic)
  (atomic-v))

(defun nestp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (case (ptype x)
         (atomic (atomicp x))
         (single (and (singlep x)
                      (nestp (single-a x)))))))

(defthm nestp-atomic
  (implies (nestp x)
           (equal (atomicp x)
                  (equal (ptype x) 'atomic))))

(defthm nestp-single
  (implies (nestp x)
           (equal (singlep x)
                  (eq (ptype x) 'single))))

(defthm nestp-single-a
  (implies (and (nestp x)
                (equal (ptype x) 'single))
           (nestp (single-a x))))

(defthm nestp-compound-recognizer
  (implies (nestp x)
           (consp x))
  :rule-classes :compound-recognizer)

(in-theory (disable nestp singlep atomicp single-a atomic-v single
                    atomic ptype))


(defun nestp2 (x)
  (declare (xargs :guard (nestp x)))
  (case (ptype x)
    (atomic t)
    (single (nestp2 (single-a x)))))

(defun nestp3 (x)
  (declare (xargs :guard (nestp x)))
  (pattern-match x
    ((atomic v) t)
    ((single a) (nestp3 a))))

(defthm bad-type-prescription
  (nestp3 (singlep x))
  :rule-classes ((:type-prescription
                  :typed-term (singlep x))))




(in-theory (disable ptype atomic atomic-structurep single
                    single-structurep))

(defthm not-equal-single-atomic
  (not (equal (single a) (atomic v))))



||#



