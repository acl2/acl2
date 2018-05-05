; Typed Tuples
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection typed-tuplep
  :parents (kestrel-utilities)
  :short "Recognize typed tuples,
          i.e. true lists whose elements satisfy specified predicates."
  :long
  "<p>
   The macro is called as
   </p>
   @({
     (typed-tuplep type1 ... typeN object)
   })
   <p>
   where @('object') is a form
   and each @('typeI') is a function name or macro name or lambda expression.
   </p>
   <p>
   The macro call expands to
   </p>
   @({
     (let ((x object))
       (and (true-listp x)
            (equal (len x) N)
            (type1 (nth 0 x))
            ...
            (typeN (nth N-1 x))))
   })
   <p>
   When @('N') is 0, @('typed-tuplep') recognizes just @('nil').
   </p>
   <p>
   When called with no arguments, i.e. @('(typed-tuplep)'),
   the macro (arbitrarily) expands to @('t').
   </p>
   @(def typed-tuplep)"

  (define typed-tuplep-conjuncts ((component-types true-listp)
                                  (i natp)
                                  (variable symbolp)
                                  (rev-conjuncts true-listp))
    :returns (conjuncts true-listp :hyp (true-listp rev-conjuncts))
    (cond ((endp component-types) (reverse rev-conjuncts))
          (t (typed-tuplep-conjuncts
              (cdr component-types)
              (1+ i)
              variable
              (cons `(,(car component-types) (nth ,i ,variable))
                    rev-conjuncts)))))

  (defmacro typed-tuplep (&rest args)
    (or (null args)
        (let ((component-types (butlast args 1))
              (object (car (last args)))
              (variable 'x))
          `(let ((,variable ,object))
             (and (true-listp ,variable)
                  (equal (len ,variable) ,(len component-types))
                  ,@(typed-tuplep-conjuncts
                     component-types 0 variable nil)))))))
