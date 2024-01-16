---
date: 2022-01-07T08:00:00Z
title: Function ATOMIC-INTEGER-VALUE
weight: 7
---

#### Syntax:

**atomic-integer-value** atomic-integer => value

#### Arguments and values:

*atomic-integer* -> an [**atomic-integer**](../atomic-integer)
object.\
*value* -> a non-negative integer.

#### Description

Returns the current value of `atomic-integer`.

#### Exceptional situations:

Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `atomic-integer` is not an [**atomic-integer**](../atomic-integer)
object.

#### See also:

[**atomic-integer**](../atomic-integer),
[**make-atomic-integer**](../make-atomic-integer)

#### Notes:

None.
