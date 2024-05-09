---
date: 2022-01-07T08:00:00Z
title: Function SEMAPHOREP
weight: 2
---

#### Syntax:

**semaphorep** datum => generalized-boolean

#### Arguments and values:

*datum* -> an object.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Returns
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true)
if `datum` is a [**semaphore**](../semaphore) object, otherwise
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false).

#### Exceptional situations:

None.

#### See also:

[**semaphore**](../semaphore), [**make-semaphore**](../make-semaphore)

#### Notes:

None.
