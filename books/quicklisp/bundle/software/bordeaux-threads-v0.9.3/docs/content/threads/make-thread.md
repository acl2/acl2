---
date: 2022-01-07T08:00:00Z
title: 'Function: MAKE-THREAD'
weight: 4
---

#### Syntax:

**make-thread** function *&key* name initial-bindings trap-conditions => thread

#### Arguments and values:

*function* -> a [function
designator](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#function_designator).\
*name* -> a
[string](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_s.htm#string)
or
[nil](http://www.lispworks.com/documentation/HyperSpec/Body/a_nil.htm#nil).\
*initial-bindings* -> an alist mapping special variable names to
values. Defaults to [\*default-special-bindings\*](default-special-bindings).\
*trap-conditions* -> if
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true),
wrap the thread function in a handler-case.

#### Description:

Creates and returns a thread named `name`, which will call the
function `function` with no arguments: when `function` returns, the
thread terminates.

The interaction between threads and dynamic variables is in some cases
complex, and depends on whether the variable has only a global binding
(as established by
e.g. [defvar](http://www.lispworks.com/documentation/HyperSpec/Body/m_defpar.htm)/[defparameter](http://www.lispworks.com/documentation/HyperSpec/Body/m_defpar.htm)/top-level
[setq](http://www.lispworks.com/documentation/HyperSpec/Body/s_setq.htm))
or has been bound locally (e.g. with
[let](http://www.lispworks.com/documentation/HyperSpec/Body/s_let_l.htm)
or
[let*](http://www.lispworks.com/documentation/HyperSpec/Body/s_let_l.htm))
in the calling thread.

- Global bindings are shared between threads: the initial value of a
  global variable in the new thread will be the same as in the
  parent, and an assignment to such a variable in any thread will be
  visible to all threads in which the global binding is visible.

- Local bindings, such as the ones introduced by `initial-bindings`,
  are local to the thread they are introduced in, except that

- Local bindings in the the caller of [make-thread](.) may or may not
  be shared with the new thread that it creates: this is
  implementation-defined. Portable code should not depend on
  particular behaviour in this case, nor should it assign to such
  variables without first rebinding them in the new thread.

#### Exceptional situations:

An error of
[type](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#type)
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
will be signaled if `function` is not a [function
designator](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#function_designator).\
An error of
[type](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#type)
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
will be signaled if `name` is anything other than
[nil](http://www.lispworks.com/documentation/HyperSpec/Body/a_nil.htm#nil)
or a [string](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_s.htm#string).

#### Affected by:

[**\*default-special-bindings\***](../default-special-bindings).

#### See also:

[**join-thread**](../join-thread)

#### Notes:

The threading model is implementation-dependent.
