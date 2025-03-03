; Standard Utilities Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defmacro+-implementation
  :parents (defmacro+)
  :short "Implementation of @(tsee defmacro+).")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defmacro+-extract-parents/short/long
  :parents (defmacro+-implementation)
  :short "Extract the XDOC keyword options from @(tsee defmacro+)."
  :long
  "<p>This is similar to @(tsee std::extract-keywords),
      but more restricted.
      We introduce a new function here,
      instead of using @(tsee std::extract-keywords),
      to reduce the book inclusions in the @(tsee defmacro+) book.
      If @(tsee std::extract-keywords) is refactored at some point,
      we could use that here and eliminate this more restricted function.</p>
   <p>The argument @('rest') of this function consists of
      the arguments of @(tsee defmacro+) after the name and macro arguments.
      See the definition of @(tsee defmacro+).</p>
   <p>This function returns two results.
      The first result is an alist
      from the keywords @(':parents'), @(':short'), and @(':long')
      to their corresponding values;
      if a keyword is not supplied, it is not in the alist.
      The second result consists of @('rest')
      without the keyword options.</p>"

  (defun defmacro+-find-parents/short/long (rest)
    (declare (xargs :guard (true-listp rest)))
    (if (endp rest)
        (mv nil nil)
      (let ((next (car rest)))
        (if (member-eq next '(:parents :short :long))
            (if (consp (cdr rest))
                (let ((val (cadr rest)))
                  (mv-let (alist rest)
                    (defmacro+-find-parents/short/long (cddr rest))
                    (if (assoc-eq next alist)
                        (prog2$
                         (er hard? 'defmacro+ "Duplicate keyword ~x0." next)
                         (mv nil nil))
                      (mv (acons next val alist) rest))))
              (prog2$
               (er hard? 'defmacro+ "Keyword ~x0 without a value." next)
               (mv nil nil)))
          (mv-let (alist rest)
            (defmacro+-find-parents/short/long (cdr rest))
            (mv alist (cons next rest)))))))

  (defthm alistp-of-mv-nth-0-of-defmacro+-find-parents/short/long
    (alistp (mv-nth 0 (defmacro+-find-parents/short/long rest))))

  (defthm true-listp-of-mv-nth-1-of-defmacro+-find-parents/short/long
    (true-listp (mv-nth 1 (defmacro+-find-parents/short/long rest)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defmacro+-fn
  :parents (defmacro+-implementation)
  :short "Event generated by @(tsee defmacro+)."

  (defun defmacro+-fn (name args rest)
    (declare (xargs :guard (and (symbolp name)
                                (true-listp rest))
                    :guard-hints (("Goal" :in-theory (disable mv-nth)))))
    (if (symbolp name)
        (mv-let (alist rest)
          (defmacro+-find-parents/short/long rest)
          (let ((parents-pair (assoc-eq :parents alist))
                (short-pair (assoc-eq :short alist))
                (long-pair (assoc-eq :long alist))
                (name-ref (concatenate 'string
                                       (symbol-package-name name)
                                       "::"
                                       (symbol-name name))))
            `(defsection ,name
               ,@(and parents-pair (list :parents (cdr parents-pair)))
               ,@(and short-pair (list :short (cdr short-pair)))
               ,@(if long-pair
                     (list :long `(concatenate 'string
                                               ,(cdr long-pair)
                                               "@(def " ,name-ref ")"))
                   (list :long `(concatenate 'string "@(def " ,name-ref ")")))
               (defmacro ,name ,args ,@rest))))
      (er hard? 'defmacro+ "The first argument ~x0 must be a symbol." name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defmacro+-macro-definition
  :parents (defmacro+-implementation)
  :short "Definition of the @(tsee defmacro+) macro."
  :long "@(def defmacro+)"

  (defmacro defmacro+ (name args &rest rest)
    `(make-event (defmacro+-fn ',name ',args ',rest))))
