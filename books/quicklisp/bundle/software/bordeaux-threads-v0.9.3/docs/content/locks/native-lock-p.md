---
date: 2022-01-07T08:00:00Z
title: Function NATIVE-LOCK-P
weight: 7
---

#### Syntax:

**native-lock-p** lock => generalized-boolean

#### Arguments and values:

*lock* -> a [lock](../lock) object.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Returns
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true)
if `datum` is a native non-recursive lock, otherwise
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false).

#### Exceptional situations:

None.

#### See also:

[**lock**](../lock), [**native-lock**](../native-lock)

#### Notes:

None.
