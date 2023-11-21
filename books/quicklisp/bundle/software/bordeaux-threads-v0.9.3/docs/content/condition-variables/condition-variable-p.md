---
date: 2022-01-07T08:00:00Z
title: Function CONDITION-VARIABLE-P
weight: 2
---

#### Syntax:

**condition-variable-p** datum => generalized-boolean

#### Arguments and values:

*datum* -> an object.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Returns
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true)
if `datum` is a [**condition-variable**](../condition-variable)
object, otherwise
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false).

#### Exceptional situations:

None.

#### See also:

[**condition-variable**](../condition-variable),
[**make-condition-variable**](../make-condition-variable)

#### Notes:

None.
