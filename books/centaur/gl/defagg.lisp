

(in-package "GL")


(include-book "cutil/defaggregate" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "tools/pattern-match" :dir :system)

(logic)

(defund-inline tag (x)
  (declare (xargs :guard (consp x)))
  (car x))

(defthm tag-of-cons
  (equal (tag (cons a b))
         a)
  :hints(("Goal" :in-theory (enable tag))))

(defthm tag-forward-to-cons
  (implies (tag x)
           (consp x))
  :hints(("Goal" :in-theory (enable tag)))
  :rule-classes :forward-chaining)

(defthm tag-when-atom
  (implies (not (consp x))
           (equal (tag x) nil))
  :hints(("Goal" :in-theory (enable tag)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(program)

(defun list-to-tree-aux1 (depth lst)
  (declare (xargs :guard (and (natp depth)
                              (consp lst))))
  (cond ((atom (cdr lst)) (mv (car lst) nil))
        ((zp depth) (mv (car lst) (cdr lst)))
        (t (b* (((mv first rest) (list-to-tree-aux1 (1- depth) lst))
                ((when (atom rest))
                 (mv first rest))
                ((mv snd rest) (list-to-tree-aux1 (1- depth) rest)))
             (mv (cons first snd) rest)))))

(defthm list-to-tree-aux1-decr
  (implies (consp lst)
           (< (len (mv-nth 1 (list-to-tree-aux1 depth lst)))
              (len lst)))
  :rule-classes :linear)

(defun list-to-tree-aux (depth fst lst)
  (declare (xargs :guard (natp depth)
                  :measure (len lst)))
  (b* (((when (atom lst)) fst)
       ((mv snd rest) (list-to-tree-aux1 depth lst))
       (tree1 (cons fst snd))
       ((when (atom rest)) tree1))
    (list-to-tree-aux (1+ depth) tree1 rest)))

(defun list-to-tree (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (list-to-tree-aux 0 (car lst) (cdr lst))))

(defun alist-wrap-pairs (car/cdr alist)
  (declare (xargs :guard (alistp alist)))
  (if (atom alist)
      nil
    (cons (cons (caar alist)
                `(and (consp x)
                      (let* ((x (,car/cdr (the cons x))))
                        ,(cdar alist))))
          (alist-wrap-pairs car/cdr (cdr alist)))))

(defun mk-accs-alist (basename tree)
  (declare (xargs :guard t))
  (if (atom tree)
      (list (cons (cutil::da-accessor-name basename tree) 'x))
    (append (alist-wrap-pairs 'car (mk-accs-alist basename (car tree)))
            (alist-wrap-pairs 'cdr (mk-accs-alist basename (cdr tree))))))

(defun mk-accessors (accs-alist tag)
  (if (atom accs-alist)
      nil
    (cons `(defund-inline ,(caar accs-alist) (x)
             (declare (xargs :guard (and . ,(and tag
                                                 `((consp x)
                                                   (eq (tag x) ',tag))))))
             ,(if tag
                  `(let* ((x (cdr (the cons x))))
                     ,(cdar accs-alist))
                (cdar accs-alist)))
          (mk-accessors (cdr accs-alist) tag))))

(defun mk-constructor-aux (tree)
  (if (atom tree)
      tree
    `(cons ,(mk-constructor-aux (car tree))
           ,(mk-constructor-aux (cdr tree)))))

(defun mk-constructor (basename tag names tree notinline)
  `(,(if notinline 'defund 'defund-inline) ,basename ,names
     (declare (xargs :guard t))
     ,(if tag
          `(cons ',tag
                 ,(mk-constructor-aux tree))
        (mk-constructor-aux tree))))

(defun accessors-of-constructor (basename accs-alist fields all-fields)
  (if (atom fields)
      nil
    (let ((acc (caar accs-alist)))
      (cons `(defthm ,(intern-in-package-of-symbol
                       (concatenate 'string (symbol-name acc) "-OF-"
                                    (symbol-name basename))
                       basename)
               (equal (,acc (,basename . ,all-fields))
                      ,(car fields))
               :hints(("Goal" :in-theory (enable ,acc ,basename))))
            (accessors-of-constructor basename (cdr accs-alist) (cdr fields) all-fields)))))

(defun accessor-acl2-count-thms (basename accs-alist)
  (if (atom accs-alist)
      nil
    (let ((acc (caar accs-alist)))
      (cons `(defthm ,(intern-in-package-of-symbol
                       (concatenate 'string
                                    (symbol-name acc)
                                    "-ACL2-COUNT-THM")
                       basename)
               (implies (consp x)
                        (< (acl2-count (,acc x)) (acl2-count x)))
               :hints(("Goal" :in-theory (enable ,acc)))
               :rule-classes (:rewrite :linear))
            (accessor-acl2-count-thms basename (cdr accs-alist))))))

(defun defagg-fn (basename fields tag notinline)
  (b* ((tree (list-to-tree fields))
       (accs-alist (mk-accs-alist basename tree))
       (?accs (strip-cars accs-alist)))
    `(defsection ,basename
       ,(mk-constructor basename tag fields tree notinline)
       ,@(mk-accessors accs-alist tag)
       ,@(accessors-of-constructor basename accs-alist fields fields)
       ,@(accessor-acl2-count-thms basename accs-alist)
       ,@(and tag
              `((defthm ,(intern-in-package-of-symbol
                          (concatenate 'string "TAG-OF-" (symbol-name basename))
                          basename)
                  (equal (tag (,basename . ,fields))
                         ',tag)
                  :hints(("Goal" :in-theory (enable ,basename tag))))
                (defmacro ,(intern-in-package-of-symbol
                            (concatenate 'string (symbol-name basename) "-P")
                            basename)
                  (x)
                  `(eq (tag ,x) ',',tag))
                (def-pattern-match-constructor
                  (x) ,basename (eq (tag x) ',tag) ,accs))))))

(defmacro defagg (basename fields &key (tag 'nil tag-p) notinline)
  (defagg-fn basename fields
    (if tag-p tag (intern (symbol-name basename) "KEYWORD"))
    notinline))

(logic)

(local
 (defagg foo (a b) :tag :foo))





      

;; (defun da-accessors (name fields)
;;   (if (atom fields)
;;       nil
;;     (cons (cutil::da-accessor-name name (car fields))
;;           (da-accessors name (cdr fields)))))

;; ;; (defun da-tag-rec (name tag)
;; ;;   (let ((tag-rec-name (intern-in-package-of-symbol
;; ;;                        (concatenate 'string
;; ;;                                     (symbol-name name)
;; ;;                                     "-TAGP")
;; ;;                        name)))
;; ;;     `(defun ,tag-rec-name (x)
;; ;;        (declare (xargs :guard (consp x)))
;; ;;        (eq (car x) ',tag))))

;; (defun da-acl2-count-thm (name field)
;;   (b* ((acc (cutil::da-accessor-name name field))
;;        (?recog (cutil::da-recognizer-name name))
;;        (thm-name (intern-in-package-of-symbol
;;                   (concatenate 'string
;;                                (symbol-name acc)
;;                                "-ACL2-COUNT-THM")
;;                   name))
;;        (x (cutil::da-x name)))
;;     `(defthm ,thm-name
;;        (implies (consp ,x) ;; (or (,recog ,x) (consp ,x))
;;                 (< (acl2-count (,acc ,x)) (acl2-count ,x)))
;;        :hints (("goal" :in-theory (enable ,acc)))
;;        :rule-classes (:rewrite :linear))))

;; (defun da-acl2-count-thms (name fields)
;;   (if (atom fields)
;;       nil
;;     (cons (da-acl2-count-thm name (car fields))
;;           (da-acl2-count-thms name (cdr fields)))))

;; (defun da-consp-thm (name fields)
;;   (let* ((thm-name (intern-in-package-of-symbol
;;                     (concatenate 'string
;;                                  (symbol-name name)
;;                                  "-CONSP")
;;                     name)))
;;     `(defthm ,thm-name
;;        (consp (,name . ,fields))
;;        :rule-classes (;; :rewrite
;;                       :type-prescription))))

;; (defmacro da-extras (name fields &key (tag 'nil tagp)
;;                           (legiblep 'nil))
;;   (declare (ignorable legiblep))
;;   (let* (;; (recog (cutil::da-recognizer-name name))
;;          (accs (da-accessors name fields))
;;          (tag (if tagp tag name))
;;          (thms (da-acl2-count-thms name fields))
;;          (x    (cutil::da-x name)))
;;     `(progn
;;        (def-pattern-match-constructor
;;          (,x) ,name (eq (tag ,x) ',tag) ,accs)
;;         ,(da-consp-thm name fields)
;;        . ,thms)))


;; (defmacro da-with-extras (&rest rst)
;;   `(progn (cutil::defaggregate . ,rst)
;;           (da-extras . ,rst)))

;; #!CUTIL
;; (defmacro GL::defagg-fns (name fields &key tag require hons (legiblep 't)
;;                                (debugp 'nil))
;;   (declare (ignorable debugp))
;;   (and (or (symbolp name)
;;            (er hard 'defaggregate "Name must be a symbol.~%"))
;;        (or (symbol-listp fields)
;;            (er hard 'defaggregate "Fields must be a list of symbols.~%"))
;;        (or (and (symbolp tag)
;;                 (equal (symbol-package-name tag) "KEYWORD"))
;;            (er hard 'defaggregate "Tag must be a keyword symbol.~%"))
;;        (or (no-duplicatesp fields)
;;            (er hard 'defaggregate "Fields must be unique.~%"))
;;        (or (consp fields)
;;            (er hard 'defaggregate "There must be at least one field.~%"))
;;        (or (and (tuple-listp 2 require)
;;                 (symbol-listp (strip-cars require)))     
;;            (er hard 'defaggregate ":require must be a list of (name requirement) tuples.~%"))
;;        (or (no-duplicatesp (strip-cars require))
;;            (er hard 'defaggregate "The names given to :require must be unique.~%"))
;;        (or (cons-listp (strip-cadrs require))
;;            (er hard 'defaggregate "The requirements must be at least conses.~%"))
;;        (or (pseudo-term-listp (strip-cadrs require))
;;            (er hard 'defaggregate "The requierments must be terms.~%"))
;;        (let ((x (da-x name)))
;;          `(progn ,(da-make-recognizer name tag fields require legiblep)
;;                  ;; jared: removing this, it's not included in vl anymore
;;                  ;; ,(da-make-debugger name tag fields require legiblep)
;;                  ,(da-make-constructor name tag fields require hons legiblep)
;;                  ,@(da-make-accessors name tag fields legiblep)
;;                  (gl::def-pattern-match-constructor
;;                   (,x) ,name (eq (tag ,x) ',tag)
;;                   ,(gl::da-accessors name fields))))))


