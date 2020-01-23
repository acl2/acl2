#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "definec" :ttags :all)

(defmacro defintrange1 (name min max)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (b* ((pkg (current-package state))
         (M (defdata::type-metadata-table (w state)))
         (A (defdata::type-alias-table (w state)))
         (th1 (make-sym ',name 'thm1 pkg))
         (th2 (make-sym ',name 'thm2 pkg))
         (th3 (make-sym ',name 'thm3 pkg))
         (namep (make-symbl `(,',name p) pkg))
         (type (cond ((equal ,min 0) 'acl2s::nat)
                     ((< 0 ,min) 'acl2s::pos)
                     ((<= ,max 0) 'acl2s::neg)
                     (t 'acl2s::integer)))
         (pred (make-symbl `(,type p) pkg))
         (rng `(and (,pred a)
                    (<= ,,min a)
                    (< a ,,max)))
         (type-of-type (type-of-type ',name M A))
         (alias? (!= type-of-type ',name)))
      (value
       (if alias?
           '(value-triple :invisible)
         `(progn
            (defdata-subtype ,',name ,type :strictp t)
            (defthm ,th1
              (implies (,namep a) ,rng)
              :rule-classes ((:forward-chaining)))
            (defthm ,th2
              (implies ,rng (,namep a))
              :rule-classes ((:rewrite :backchain-limit-lst 1)))
            (defthm ,th3
              (equal (,namep a) ,rng)
              :rule-classes :compound-recognizer)
            (in-theory (disable ,namep))))))))

(defmacro defintrange (name min max)
  "Define a datatype that includes all integers [min..max), i.e., >= min and < max"
  (declare (xargs :guard (symbolp name)))
  `(progn (defdata ,name (range integer (,min <= _ < ,max)))
          (defintrange1 ,name ,min ,max)))

#|
(defmacro defintrange (name min max)
  "Define a datatype that includes all integers [min..max), i.e., >= min and < max"
  (declare (xargs :guard (symbolp name)))
  `(make-event
    (b* ((pkg (current-package state))
         (th1 (make-sym ',name 'thm1 pkg))
         (th2 (make-sym ',name 'thm2 pkg))
         (th3 (make-sym ',name 'thm3 pkg))
         (namep (make-symbl `(,',name p) pkg))
         (type (cond ((equal ,min 0) 'acl2s::nat)
                     ((< 0 ,min) 'acl2s::pos)
                     ((<= ,max 0) 'acl2s::neg)
                     (t 'acl2s::integer)))
         (pred (make-symbl `(,type p) pkg))
         (rng `(and (,pred a)
                    (<= ,,min a)
                    (< a ,,max))))
      `(progn
         (defdata ,',name (range integer (,,min <= _ < ,,max)))
         (defdata-subtype ,',name ,type :strictp t)
         (defthm ,th1
           (implies (,namep a) ,rng)
           :rule-classes ((:forward-chaining)))
         (defthm ,th2
           (implies ,rng (,namep a))
           :rule-classes ((:rewrite :backchain-limit-lst 1)))
         (defthm ,th3
           (equal (,namep a) ,rng)
           :rule-classes :compound-recognizer)
         (in-theory (disable ,namep))))))
|#

(defmacro defnatrange (name max)
  "Define a datatype that includes all nats < max"
  (declare (xargs :guard (symbolp name)))
  `(defintrange ,name 0 ,max))

#|

:trans1 (defintrange foo1 0 1)
:trans1 (defintrange foo2 0 100)
:trans1 (defintrange foo3 2 100)
:trans1 (defintrange foo4 -100 0)
:trans1 (defintrange foo5 -2 100)
:trans1 (defintrange foo5 -2 (expt 2 10))

(defintrange foo1 0 1)
(defintrange foo2 0 100)
(defintrange foo3 2 100)
(defintrange foo4 -100 0)
(defintrange foo5 -2 100)
(defintrange foo5 -2 (expt 2 10))

|#

