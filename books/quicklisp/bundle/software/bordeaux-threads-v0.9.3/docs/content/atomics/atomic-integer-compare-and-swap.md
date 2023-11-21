---
date: 2022-01-07T08:00:00Z
title: Function ATOMIC-INTEGER-COMPARE-AND-SWAP
weight: 4
---

#### Syntax:

**atomic-integer-compare-and-swap** atomic-integer old new => generalized-boolean

#### Arguments and values:

*atomic-integer* -> an [**atomic-integer**](../atomic-integer)
object.\
*old*, *new* -> non-negative integers.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description

If the current value of `atomic-integer` is equal to `old`, replace it
with `new`.

Returns
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true)
if the replacement was successful, otherwise
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false).

#### Exceptional situations:

Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `atomic-integer` is not an [**atomic-integer**](../atomic-integer)
object.\
Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `old` is not a non-negative integer.\
Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `new` is not a non-negative integer.

#### See also:

[**atomic-integer**](../atomic-integer),
[**atomic-integer-incf**](../atomic-integer-incf),
[**atomic-integer-decf**](../atomic-integer-decf),
[**make-atomic-integer**](../make-atomic-integer)

#### Notes:

None.
