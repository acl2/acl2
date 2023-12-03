---
date: 2022-01-07T08:00:00Z
title: Function ACQUIRE-LOCK, RELEASE-LOCK
weight: 11
---

#### Syntax:

**acquire-lock** lock &key (wait t) timeout => generalized-boolean\
**release-lock** lock => lock

#### Arguments and values:

*lock* -> a [**lock**](../lock) object.\
*wait* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).\
*timeout* -> a non-negative real number.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Acquire `lock` for the calling thread.

`wait` governs what happens if the lock is not available: if `wait` is
true, the calling thread will wait until the lock is available and
then acquire it; if `wait` is nil, `acquire-lock` will return
immediately. If `wait` is true, `timeout` may specify a maximum amount
of seconds to wait for the lock to become available.

`acquire-lock` returns
[true](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_t.htm#true)
if the lock was acquired, otherwise
[false](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#false).

#### Exceptional situations:

Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `lock` is not a [**lock**](../lock) object.\
Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `timeout` is neither nil nor a non-negative real number.

#### See also:

[**lock**](../lock)

#### Notes:

It is implementation-defined what happens if a thread attempts to
acquire a lock that it already holds.
