---
date: 2022-01-07T08:00:00Z
title: Function CONDITION-WAIT
weight: 4
---

#### Syntax:

**condition-wait** condition-variable lock *&key* timeout => generalized-boolean

#### Arguments and values:

*condition-variable* -> a
[**condition-variable**](../condition-variable) object.\
*lock* -> a [**lock**](../lock) object.\
*timeout* -> a non-negative real number.\
*generalized-boolean* -> a [generalized
boolean](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_g.htm#generalized_boolean).

#### Description:

Atomically release `lock` and enqueue the calling thread waiting for
`condition-variable`. The thread will resume when another thread has
notified it using [**condition-notify**](./condition-notify); it may
also resume if interrupted by some external event or in other
implementation-dependent circumstances: the caller must always test on
waking that there is threading to be done, instead of assuming that it
can go ahead.\
It is an error to call this function unless from the thread that holds
`lock`.

If `timeout` is nil or not provided, the call blocks until a
notification is received.\
If `timeout` is non-nil, the call will return after at most `timeout`
seconds (approximately), whether or not a notification has occurred.

Either **true** or **false** will be returned. **false** indicates
that the timeout has expired without receiving a
notification. **true** indicates that a notification was received.

#### Exceptional situations:

Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `condition-variable` is not a
[**condition-variable**](../condition-variable) object.\
Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `lock` is not a [**lock**](../lock) object.\
Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `timeout` is neither nil nor a non-negative real number.

#### See also:

[**condition-notify**](./condition-notify),
[**condition-broadcast**](./condition-broadcast)

#### Notes:

Due to implementation limitations, there is the possibility of
spurious wakeups, i.e. for **condition-wait** to return **true**
without the underlying condition being satisfied. Correct code must
always check whether the condition is satisfied, and otherwise call
**condition-wait** again, typically in a loop.
