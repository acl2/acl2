---
date: 2022-01-07T08:00:00Z
title: Function SIGNAL-SEMAPHORE
weight: 4
---

#### Syntax:

**signal-semaphore** semaphore -> t

#### Arguments and values:

*semaphore* -> a
[**semaphore**](../semaphore) object.

#### Description:

Increment `semaphore` by `count`. If there are threads waiting on this
semaphore, then `count` of them are woken up.

Returns always
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true).

#### Exceptional situations:

Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `semaphore` is not a [**semaphore**](../semaphore) object.

#### See also:

[**make-semaphore**](./make-semaphore),
[**wait-on-semaphore**](./wait-on-semaphore)

#### Notes:

It is unspecified which thread gets a wakeup and does not necessarily
relate to the order in which the threads went to sleep.
