---
date: 2022-01-07T08:00:00Z
title: 'Function THREAD-ALIVE-P'
weight: 14
---

#### Syntax:

**thread-alive-p** thread => generalized-boolean

#### Arguments and values:

*thread* -> a [thread](../class-thread) object.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Returns true if `thread` has not finished or
[**destroy-thread**](../destroy-thread) has not been called on it.

#### Exceptional situations:

Signals a type error if `thread` is not a [thread](../class-thread)
object.

#### See also:

None.

#### Notes:

None.
