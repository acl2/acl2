---
date: 2022-01-07T08:00:00Z
title: Function MAKE-ATOMIC-INTEGER
weight: 3
---

#### Syntax:

**make-atomic-integer** *&key* value => atomic-integer

#### Arguments and values:

*value* -> a non-negative integer.\
*semaphore* -> a [**semaphore**](../semaphore) object.

#### Description:

Creates an atomic integer `name` and initial value `value`.

#### Exceptional situations:

Signals a condition of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `value` is not a non-negative integer (an unsigned-byte).

#### See also:

[**atomic-integer**](../atomic-integer)

#### Notes:

None.
