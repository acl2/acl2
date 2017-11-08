



(in-package "AIGNET")

(include-book "std/util/define" :dir :system)
(include-book "tools/templates" :dir :system)
(program)

(std::def-primitive-aggregate statsmgr-field
  (name
   desc
   abbrev))

(defconst *statsmgr-field-keys* '(:desc :abbrev))

(define statsmgr-parse-field (x)
  (b* (((unless (and (consp x) (symbolp (car x))))
        (raise "Field must begin with a symbol: ~x0" x))
       (name (car x))
       ((mv kwd-alist rest) (std::extract-keywords `(statsmgr-field ,name)
                                                   *statsmgr-field-keys*
                                                   (cdr x) nil))
       ((when rest)
        (raise "Unexpected remainder: ~x0" rest))
       (desc (std::getarg :desc (symbol-name name) kwd-alist))
       (abbrev (std::getarg :abbrev (symbol-name name) kwd-alist)))
    (make-statsmgr-field :name name :desc desc :abbrev abbrev)))

(define statsmgr-parse-fields (x)
  (if (atom x)
      nil
    (cons (statsmgr-parse-field (car x))
          (statsmgr-parse-fields (cdr x)))))

(std::def-primitive-aggregate statsmgr
  (name
   fields
   prefix
   inline
   non-memoizable))

(defconst *statsmgr-keys* '(:prefix :inline :non-memoizable))

(define statsmgr-parse (x)
  (b* (((unless (and (consp x) (symbolp (car x))))
        (raise "Statsmgr definition must begin with a symbol: ~x0" x))
       (name (car x))
       ((mv kwd-alist fields) (std::extract-keywords `(defstatsmgr ,name)
                                                     *statsmgr-keys*
                                                     (cdr x) nil))
       (fields (statsmgr-parse-fields fields))
       (prefix (symbol-name (std::getarg :prefix name kwd-alist))))
    (make-statsmgr :name name :fields fields :prefix prefix
                   :inline (cdr (assoc :inline kwd-alist))
                   :non-memoizable (std::getarg :non-memoizable t kwd-alist))))


(define statsmgr-stobj-field (field prefix name)
  (b* (((statsmgr-field field)))
    (acl2::template-subst
     '(<prefix>-<field> :type (integer 0 *) :initially 0)
     :str-alist `(("<PREFIX>" . ,prefix)
                  ("<FIELD>" . ,(symbol-name field.name)))
     :pkg-sym name)))

(define statsmgr-stobj-fields (fields prefix name)
  (if (atom fields)
      nil
    (cons (statsmgr-stobj-field (car fields) prefix name)
          (statsmgr-stobj-fields (cdr fields) prefix name))))

(define statsmgr-field-incr-def (field prefix name)
  (b* (((statsmgr-field field)))
    (acl2::template-subst
     '(define incr-<prefix>-<field> (<name> &optional ((count natp) '1))
        (update-<prefix>-<field> (+ (lnfix count) (<prefix>-<field> <name>)) <name>))
     :str-alist `(("<PREFIX>" . ,prefix)
                  ("<FIELD>" . ,(symbol-name field.name)))
     :atom-alist `((<name> . ,name))
     :pkg-sym name)))

(define statsmgr-field-incr-defs (fields prefix name)
  (if (atom fields)
      nil
    (cons (statsmgr-field-incr-def (car fields) prefix name)
          (statsmgr-field-incr-defs (cdr fields) prefix name))))


(define statsmgr-field-incr-cond-def (field prefix name)
  (b* (((statsmgr-field field)))
    (acl2::template-subst
     '(define incr-<prefix>-<field>-cond (cond <name> &optional ((count natp) '1))
        (if cond
            (update-<prefix>-<field> (+ (lnfix count) (<prefix>-<field> <name>)) <name>)
          <name>))
     :str-alist `(("<PREFIX>" . ,prefix)
                  ("<FIELD>" . ,(symbol-name field.name)))
     :atom-alist `((<name> . ,name))
     :pkg-sym name)))

(define statsmgr-field-incr-cond-defs (fields prefix name)
  (if (atom fields)
      nil
    (cons (statsmgr-field-incr-cond-def (car fields) prefix name)
          (statsmgr-field-incr-cond-defs (cdr fields) prefix name))))

(define statsmgr-print-field (field prefix name abbrev)
  (b* (((statsmgr-field field)))
    (acl2::template-subst
     '(cw <string> <desc> (<prefix>-<field> <name>))
     
     :str-alist `(("<PREFIX>" . ,prefix)
                  ("<FIELD>" . ,(symbol-name field.name)))
     :atom-alist `((<name> . ,name)
                   (<string> . ,(if abbrev "~s0: ~x1   " "~s0: ~x1~%"))
                   (<desc> . ,(if abbrev field.abbrev field.desc)))
     :pkg-sym name)))

(define statsmgr-print-fields (fields prefix name abbrev)
  (if (atom fields)
      nil
    (cons (statsmgr-print-field (car fields) prefix name abbrev)
          (statsmgr-print-fields (cdr fields) prefix name abbrev))))





(define statsmgr-abbrev-def (x)
  (b* (((statsmgr x))
       (print-fields (statsmgr-print-fields x.fields x.prefix x.name t)))
    (acl2::template-subst
     '(define abbrev-<name> (<name>)
        (progn$ <print-fields>
                (cw "~%")))
     :str-alist `(("<PREFIX>" . ,x.prefix)
                  ("<NAME>" . ,(symbol-name x.name)))
     :atom-alist `((<name> . ,x.name))
     :splice-alist `((<print-fields> . ,print-fields))
     :pkg-sym x.name)))


(define statsmgr-print-def (x)
  (b* (((statsmgr x))
       (print-fields (statsmgr-print-fields x.fields x.prefix x.name nil)))
    (acl2::template-subst
     '(define print-<name> (<name>)
        (progn$ <print-fields>))
     :str-alist `(("<PREFIX>" . ,x.prefix)
                  ("<NAME>" . ,(symbol-name x.name)))
     :atom-alist `((<name> . ,x.name))
     :splice-alist `((<print-fields> . ,print-fields))
     :pkg-sym x.name)))


(define defstatsmgr-fn (form)
  (b* (((statsmgr x) (statsmgr-parse form)))
    `(progn
       (defstobj ,x.name
         ,@(statsmgr-stobj-fields x.fields x.prefix x.name)
         :inline ,x.inline
         :non-memoizable ,x.non-memoizable)

       ,@(statsmgr-field-incr-defs x.fields x.prefix x.name)
       ,@(statsmgr-field-incr-cond-defs x.fields x.prefix x.name)

       ,(statsmgr-print-def x)
       ,(statsmgr-abbrev-def x))))

(defmacro defstatsmgr (&rest args)
  (defstatsmgr-fn args))


(logic)
(local
 (progn
   (include-book "std/basic/defs" :dir :system)
   (defstatsmgr foostats
     :prefix foostats
     (bar :desc "bar count" :abbrev "bar")
     (baz :desc "baz count" :abbrev "baz")
     (fuz :desc "fuz count" :abbrev "fuz"))))
