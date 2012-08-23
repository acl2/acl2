

(in-package "GL")


(include-book "cutil/defaggregate" :dir :system)
(include-book "tools/flag" :dir :system)

(program)

(defun da-accessors (name fields)
  (if (atom fields)
      nil
    (cons (cutil::da-accessor-name name (car fields))
          (da-accessors name (cdr fields)))))

;; (defun da-tag-rec (name tag)
;;   (let ((tag-rec-name (intern-in-package-of-symbol
;;                        (concatenate 'string
;;                                     (symbol-name name)
;;                                     "-TAGP")
;;                        name)))
;;     `(defun ,tag-rec-name (x)
;;        (declare (xargs :guard (consp x)))
;;        (eq (car x) ',tag))))

(defun da-acl2-count-thm (name field)
  (let* ((acc (cutil::da-accessor-name name field))
         (recog (cutil::da-recognizer-name name))
         (thm-name (intern-in-package-of-symbol
                    (concatenate 'string
                                 (symbol-name acc)
                                 "-ACL2-COUNT-THM")
                    name))
         (x (cutil::da-x name)))
    `(defthm ,thm-name
       (implies (or (,recog ,x) (consp ,x))
                (< (acl2-count (,acc ,x)) (acl2-count ,x)))
       :hints (("goal" :in-theory (enable ,acc)))
       :rule-classes (:rewrite :linear))))

(defun da-acl2-count-thms (name fields)
  (if (atom fields)
      nil
    (cons (da-acl2-count-thm name (car fields))
          (da-acl2-count-thms name (cdr fields)))))

(defun da-consp-thm (name fields)
  (let* ((thm-name (intern-in-package-of-symbol
                    (concatenate 'string
                                 (symbol-name name)
                                 "-CONSP")
                    name)))
    `(defthm ,thm-name
       (consp (,name . ,fields))
       :rule-classes (:rewrite :type-prescription))))

(defmacro da-extras (name fields &key (tag 'nil tagp)
                          (legiblep 'nil))
  (declare (ignorable legiblep))
  (let* (;; (recog (cutil::da-recognizer-name name))
         (accs (da-accessors name fields))
         (tag (if tagp tag name))
         (thms (da-acl2-count-thms name fields))
         (x    (cutil::da-x name)))
    `(progn
       (def-pattern-match-constructor
         (,x) ,name (and (consp ,x) (eq (tag ,x) ',tag)) ,accs)
       ,(da-consp-thm name fields)
       . ,thms)))


(defmacro da-with-extras (&rest rst)
  `(progn (cutil::defaggregate . ,rst)
          (da-extras . ,rst)))

#!CUTIL
(defmacro GL::defagg-fns (name fields &key tag require hons (legiblep ''t))
  (and (or (symbolp name)
           (er hard 'defaggregate "Name must be a symbol.~%"))
       (or (symbol-listp fields)
           (er hard 'defaggregate "Fields must be a list of symbols.~%"))
       (or (and (symbolp tag)
                (equal (symbol-package-name tag) "KEYWORD"))
           (er hard 'defaggregate "Tag must be a keyword symbol.~%"))
       (or (no-duplicatesp fields)
           (er hard 'defaggregate "Fields must be unique.~%"))
       (or (consp fields)
           (er hard 'defaggregate "There must be at least one field.~%"))
       (or (and (tuple-listp 2 require)
                (symbol-listp (strip-cars require)))     
           (er hard 'defaggregate ":require must be a list of (name requirement) tuples.~%"))
       (or (no-duplicatesp (strip-cars require))
           (er hard 'defaggregate "The names given to :require must be unique.~%"))
       (or (cons-listp (strip-cadrs require))
           (er hard 'defaggregate "The requirements must be at least conses.~%"))
       (or (pseudo-term-listp (strip-cadrs require))
           (er hard 'defaggregate "The requierments must be terms.~%"))
       (let ((x (da-x name)))
         `(progn ,(da-make-recognizer name tag fields require legiblep)
                 ;; jared: removing this, it's not included in vl anymore
                 ;; ,(da-make-debugger name tag fields require legiblep)
                 ,(da-make-constructor name tag fields require hons legiblep)
                 ,@(da-make-accessors name fields legiblep)
                 (gl::def-pattern-match-constructor
                  (,x) ,name (and (consp ,x) (eq (gl::tag ,x) ',tag))
                  ,(gl::da-accessors name fields))))))


