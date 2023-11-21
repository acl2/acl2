---
date: 2022-01-07T08:00:00Z
title: Function WAIT-ON-SEMAPHORE
weight: 5
---

#### Syntax:

**wait-on-semaphore** semaphore *&key* timeout -> generalized-boolean

#### Arguments and values:

*semaphore* -> a
[**semaphore**](../semaphore) object.\
*timeout* -> a non-negative real number.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Decrement the count of `semaphore` by 1 if the count is larger than zero.\
If the count is zero, blocks until `semaphore` can be decremented.
Returns
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true)
on success.

If `timeout` is given, it is the maximum number of seconds to wait. If
the count cannot be decremented in that time, returns
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false)
without decrementing the count.

#### Exceptional situations:

Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `semaphore` is not a [**semaphore**](../semaphore) object.\
Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `timeout` is neither nil nor a non-negative real number.

#### See also:

[**make-semaphore**](./make-semaphore),
[**wait-on-semaphore**](./wait-on-semaphore)

#### Notes:

It is unspecified which thread gets a wakeup and does not necessarily
relate to the order in which the threads went to sleep.

On Allegro, a non-null `timeout` is forced to a minimum of 100ms,
because Allegro does not provide a primitive for waiting with a
timeout, which is emulated using
[**with-timeout**](../../timeouts/with-timeout).
