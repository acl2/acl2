

(in-package "ACL2")

(include-book "fixtype")

(defconst *defbasetype-keys*
  '(:name
    :fix))

;; This is just deffixtype with defaults for the names and with :define t.  We
;; wouldn't need to take the equiv name as an input, but since we're defining
;; it we'd like it to be tags-searchable.
(defun defbasetype-fn (equiv pred keys)
  (declare (xargs :mode :program))
  (b* ((__function__ 'defbasetype-fn)
       ((mv kwd-alist args) (std::extract-keywords __function__
                                                   *defbasetype-keys*
                                                   keys nil))
       ((when args) (raise "Bad args: ~x0" args))
       (pkg (if (equal (symbol-package-name pred) "COMMON-LISP")
                'acl2::foo
              pred))
       (typename (or (std::getarg :name nil kwd-alist)
                     (b* ((predname (symbol-name pred))
                          (len (length predname))
                          (p? (char predname (- len 1)))
                          ((unless (eql p? #\P)) pred)
                          (dash? (char predname (- len 2)))
                          (newlen (- len (if (eql dash? #\-) 2 1))))
                       (intern-in-package-of-symbol
                        (subseq predname 0 newlen)
                        pkg))))
       (fix (or (std::getarg :fix nil kwd-alist)
                (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name typename) "-FIX")
                 pkg))))
    `(progn
       (fty::deffixtype ,typename :pred ,pred :fix ,fix :equiv ,equiv :define t)
       (verify-guards ,equiv))))

(defmacro defbasetype (equiv pred &rest keys)
  (defbasetype-fn equiv pred keys))


(defbasetype nat-equiv natp :fix nfix)

(defbasetype int-equiv integerp :fix ifix :name int)

(defbasetype rational-equiv rationalp :fix rfix)

(defbasetype number-equiv acl2-numberp :fix fix)

(defsection string-equiv
  (defund string-fix (x)
    (declare (xargs :guard t))
    (if (stringp x) x ""))

  (local (in-theory (enable string-fix)))

  (defthm stringp-of-string-fix
    (stringp (string-fix x))
    :rule-classes :type-prescription)

  (defthm string-fix-when-stringp
    (implies (stringp x)
             (equal (string-fix x) x)))

  (defbasetype string-equiv stringp))

(defsection symbol-equiv
  (defund symbol-fix (x)
    (declare (xargs :guard t))
    (if (symbolp x) x nil))

  (local (in-theory (enable symbol-fix)))

  (defthm symbolp-of-symbol-fix
    (symbolp (symbol-fix x))
    :rule-classes :type-prescription)
  
  (defthm symbol-fix-when-symbolp
    (implies (symbolp x)
             (equal (symbol-fix x) x)))

  (defbasetype symbol-equiv symbolp))

(defsection pos-equiv
  (defund pos-fix (x)
    (declare (xargs :guard t))
    (if (posp x) x 1))

  (local (in-theory (enable pos-fix)))

  (defthm posp-of-pos-fix
    (posp (pos-fix x))
    :rule-classes :type-prescription)
  
  (defthm pos-fix-when-posp
    (implies (posp x)
             (equal (pos-fix x) x)))

  (defbasetype pos-equiv posp))

(defsection char-equiv
  (defund char-fix (x)
    (declare (xargs :guard t))
    (if (characterp x) x (code-char 0)))

  (local (in-theory (enable char-fix)))

  (defthm characterp-of-char-fix
    (characterp (char-fix x))
    :rule-classes :type-prescription)
  
  (defthm char-fix-when-characterp
    (implies (characterp x)
             (equal (char-fix x) x)))

  (defbasetype char-equiv characterp :name char))

(defsection bool-equiv-is-just-iff
  (defund bool-fix (x)
    (declare (xargs :guard t))
    (and x t))
  
  (local (in-theory (enable bool-fix)))

  (defthm booleanp-of-bool-fix
    (booleanp (bool-fix x))
    :rule-classes :type-prescription)
  
  (defthm bool-fix-when-booleanp
    (implies (booleanp x)
             (equal (bool-fix x) x)))

  (fty::deffixtype bool :pred booleanp :fix bool-fix :equiv iff))

(local (defun center-in-n-char-field (str n)
         (let* ((len (length str)))
           (if (<= n (length str))
               (coerce str 'list)
             (let* ((diff (- n len))
                    (pre-num (floor diff 2))
                    (post-num (- diff pre-num)))
               (append (make-list pre-num :initial-element #\Space)
                       (coerce str 'list)
                       (make-list post-num :initial-element #\Space)))))))


(local
 (defun make-basetypes-table-rchars (table acc)
   (declare (xargs :mode :program))
   (b* (((when (atom table)) acc)
        (acc (revappend (center-in-n-char-field (string-downcase (symbol-name (fty::fixtype->name (cdar table)))) 18) acc))
        (acc (revappend (center-in-n-char-field (string-downcase (symbol-name (fty::fixtype->pred (cdar table)))) 18) acc))
        (acc (revappend (center-in-n-char-field (string-downcase (symbol-name (fty::fixtype->fix (cdar table)))) 18) acc))
        (acc (revappend (center-in-n-char-field (string-downcase (symbol-name (fty::fixtype->equiv (cdar table)))) 18) acc))
        (acc (cons #\Newline acc)))
     (make-basetypes-table-rchars (cdr table) acC))))

(make-event
 `(defxdoc fty::basetypes
    :parents (fty::fty)
    :short "A few base types with associated fixing functions and equivalence relations"

    :long (concatenate
           'string
           "<p>This book supports the @(see fixtype) typed reasoning approach
by associating fixing functions and equivalence relations with many of the
basic ACL2 built-in types.  This book makes the following associations (all in
the ACL2 package):</p>

@({
     Type Name        Predicate       Fixing function    Equiv relation
-------------------------------------------------------------------------
"
 ,(reverse (coerce (make-basetypes-table-rchars (cdar (table-alist 'fty::fixtypes (w state))) nil) 'string))
"
 })")))
           
  
