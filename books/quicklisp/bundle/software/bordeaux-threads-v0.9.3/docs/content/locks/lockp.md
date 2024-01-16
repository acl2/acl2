---
date: 2022-01-07T08:00:00Z
title: Function LOCKP
weight: 2
---

#### Syntax:

**lockp** datum => generalized-boolean

#### Arguments and values:

*datum* -> an object.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Returns
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true)
if `datum` is a non-recursive lock, otherwise
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false).

#### Exceptional situations:

None.

#### See also:

[**lock**](../lock)

#### Notes:

None.
