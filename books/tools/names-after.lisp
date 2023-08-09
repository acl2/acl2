; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defun names-after (name prop wrld avoid-lst acc)
  (declare (xargs :mode :program ; because of access-event-tuple-namex
                  :guard (and (symbolp name)
                              (plist-worldp wrld)
                              (symbol-listp avoid-lst)
                              (symbol-listp acc))))
  (cond
   ((endp wrld)
    (er hard (cond ((eq prop 'formals)
                    'functions-after)
                   ((eq prop 'macro-body)
                    'macros-after)
                   (t ; implementation error
                    'names-after))
        "The symbol ~x0 is not a known name in the current ACL2 world."
        name))
   (t (let ((tuple (car wrld)))
        (cond
         ((eq (car tuple) 'event-landmark)
          (let ((namex (access-event-tuple-namex (cddr tuple))))
            (if (if (consp namex) (member-eq name namex) (eq name namex))
                acc
              (names-after name prop (cdr wrld) avoid-lst acc))))
         ((eq (cadr tuple) prop)
          (if (eq (cddr tuple) *acl2-property-unbound*)
              (names-after name
                           prop
                           (cdr wrld)
                           (cons (car tuple) avoid-lst)
                           acc)
            (names-after name
                         prop
                         (cdr wrld)
                         avoid-lst
                         (if (member-eq (car tuple) avoid-lst)
                             acc
                           (cons (car tuple) acc)))))
         (t (names-after name prop (cdr wrld) avoid-lst acc)))))))

(defun functions-after-fn (name wrld)
  (declare (xargs :mode :program
                  :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (cond
   ((symbolp name)
    (names-after name 'formals wrld nil nil))
   (t
    (er hard 'functions-after
        "The argument to ~x0 must be a symbol, but ~x1 is not."
        'functions-after name))))

(defmacro functions-after (name)
  (cond ((and (consp name)
              (eq (car name) 'quote)
              (consp (cdr name))
              (symbolp (cadr name))
              (null (cddr name)))
         (er hard 'macros-after
             "The argument to ~x0 must be a symbol, but ~x1 is a quoted ~
              symbol (a cons)."
             'functions-after name))
        (t `(functions-after-fn ',name (w state)))))

(defun macros-after-fn (name wrld)
  (declare (xargs :mode :program
                  :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (cond
   ((symbolp name)
    (names-after name 'macro-body wrld nil nil))
   (t
    (er hard 'macros-after
        "The argument to ~x0 must be a symbol, but ~x1 is not."
        'macros-after name))))

(defmacro macros-after (name)
  (cond ((and (consp name)
              (eq (car name) 'quote)
              (consp (cdr name))
              (symbolp (cadr name))
              (null (cddr name)))
         (er hard 'macros-after
             "The argument to ~x0 must be a symbol, but ~x1 is a quoted ~
              symbol (a cons)."
             'macros-after name))
        (t `(macros-after-fn ',name (w state)))))

(defxdoc functions-after
  :parents (events)
  :short "Function symbols introduced after a given event name"
  :long "<p>Evaluate @('(functions-after NAME)'), where @('NAME') is a symbol
 naming an event in the current ACL2 @(see world), to obtain a list of function
 symbols introduced after @('NAME') was introduced.  That list @('L') has no
 duplicates; moreover, for any symbols @('f1') and @('f2') in @('L'), @('f1')
 occurs before @('f2') in @('L') if and only if @('f1') was introduced before
 @('f2') in the current ACL2 world, except that the order is undefined when
 @('f1') and @('f2') were introduced in the same @(tsee mutual-recursion)
 event.</p>

 <p>To use this tool:</p>

 @({
 (include-book \"tools/names-after\" :dir :system)
 })

 <p>In a program you can invoke @('(functions-after-fn x wrld)') on an
 expression, @('x'), to obtain the result described above where @('NAME') is
 the value of @('x') and @('wrld') is an ACL2 @(see world).  In particular, the
 call @('(functions-after NAME)') macroexpands to @('(functions-after-fn
 'NAME (w state))').</p>

 <p>See @(see macros-after) for an utility to apply to obtain macro
 names.</p>")

(defxdoc macros-after
  :parents (events)
  :short "Macro names introduced after a given event name"
  :long "<p>Evaluate @('(macros-after NAME)'), where @('NAME') is a symbol
 naming an event in the current ACL2 @(see world), to obtain a list of macro
 names introduced after @('NAME') was introduced.  That list @('L') has no
 duplicates; moreover, for any symbols @('m1') and @('m2') in @('L'), @('m1')
 occurs before @('m2') in @('L') if and only if @('m1') was introduced before
 @('m2') in the current ACL2 world.</p>

 <p>To use this tool:</p>

 @({
 (include-book \"tools/names-after\" :dir :system)
 })

 <p>In a program you can invoke @('(macros-after-fn x wrld)') on an expression,
 @('x'), to obtain the result described above where @('NAME') is the value of
 @('x') and @('wrld') is an ACL2 @(see world).  In particular, the call
 @('(macros-after NAME)') macroexpands to @('(macros-after-fn 'NAME (w
 state))').</p>

 <p>See @(see functions-after) for an utility to apply to obtain function
 symbols.</p>")
