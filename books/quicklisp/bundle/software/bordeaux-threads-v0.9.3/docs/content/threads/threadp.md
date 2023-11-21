---
date: 2022-01-07T08:00:00Z
title: 'Function: THREADP'
weight: 3
---

#### Syntax:

**threadp** object => generalized-boolean

#### Arguments and values:

*object* -> an
[object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object).\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Returns
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true)
if `object` is of
[type](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#type)
[**thread**](../class-thread), otherwise
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false).

#### Exceptional situations:

None.

#### Notes:

`(threadp object) == (typep object 'thread)`
