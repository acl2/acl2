---
date: 2022-01-07T08:00:00Z
title: Function CONDITION-NOTIFY
weight: 5
---

#### Syntax:

**condition-notify** condition-variable -> generalized-boolean

#### Arguments and values:

*condition-variable* -> a
[**condition-variable**](../condition-variable) object.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Notify one of the threads waiting for `condition-variable`.

Returns always
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false).

#### Exceptional situations:

Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `condition-variable` is not a
[**condition-variable**](../condition-variable) object.

#### See also:

[**condition-wait**](./condition-wait),
[**condition-broadcast**](./condition-broadcast)

#### Notes:

It is unspecified which thread gets a wakeup and does not necessarily
relate to the order in which the threads went to sleep.

**condition-notify** always returns
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false)
because not all implementations' primitives can tell whether or not
some threads were indeed woken up.
