---
date: 2022-01-07T08:00:00Z
title: Function ATOMIC-INTEGER-DECF
weight: 5
---

#### Syntax:

**atomic-integer-decf** atomic-integer *&optional* (delta 1) => new-value

#### Arguments and values:

*atomic-integer* -> an [**atomic-integer**](../atomic-integer)
object.\
*delta* -> an integer.\
*new-value* -> a non-negative integer.

#### Description

Decrements the value of `atomic-integer` by `delta`.

Returns the new value of `atomic-integer`.

#### Exceptional situations:

Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `atomic-integer` is not an [**atomic-integer**](../atomic-integer)
object.\
Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `delta` is not an integer.

#### See also:

[**atomic-integer**](../atomic-integer),
[**atomic-integer-incf**](../atomic-integer-incf),
[**make-atomic-integer**](../make-atomic-integer)

#### Notes:

None.
