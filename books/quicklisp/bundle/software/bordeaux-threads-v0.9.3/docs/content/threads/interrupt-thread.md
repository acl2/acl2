---
date: 2022-01-07T08:00:00Z
title: 'Function INTERRUPT-THREAD'
weight: 11
---

#### Syntax:

**interrupt-thread** thread function *&rest* arguments => thread

#### Arguments and values:

*thread* -> a [thread](../class-thread) object.\
*function* -> a function object.\
*arguments* -> values.

#### Description:

Interrupt `thread` and apply `function` to `arguments` within its
dynamic context, then continue with the interrupted path of execution.

Returns the thread object it acted on.

#### Exceptional situations:

An error of
[type](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#type)
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
will be signaled if `thread` is not a [**thread**](../class-thread) object.\
An error of
[type](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#type)
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
will be signaled if `function` is not a [function
designator](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#function_designator).

#### See also:

[**make-thread**](../make-thread), [**join-thread**](../join-thread)

#### Notes:

This may not be a good idea if `thread` is holding locks or doing
anything important.
