---
date: 2022-01-07T08:00:00Z
title: Function NATIVE-RECURSIVE-LOCK-P
weight: 9
---

#### Syntax:

**native-recursive-lock-p** lock => generalized-boolean

#### Arguments and values:

*lock* -> a [recursive-lock](../recursive-lock) object.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Returns
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true)
if `datum` is a native recursive lock, otherwise
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false).

#### Exceptional situations:

None.

#### See also:

[**recursive-lock**](../recursive-lock),
[**native-recursive-lock**](../native-recursive-lock)

#### Notes:

None.
