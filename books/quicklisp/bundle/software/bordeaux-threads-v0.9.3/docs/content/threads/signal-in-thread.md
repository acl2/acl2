---
date: 2022-01-07T08:00:00Z
title: 'Function SIGNAL-IN-THREAD, WARN-IN-THREAD, ERROR-IN-THREAD'
weight: 12
---

#### Syntax:

**signal-in-thread** thread datum *&rest* arguments => thread\
**warn-in-thread** thread datum *&rest* arguments => thread\
**error-in-thread** thread datum *&rest* arguments => thread

#### Arguments and values:

*thread* -> a [thread](../class-thread) object.\
*datum, arguments* -> designators for a condition.

#### Description:

Interrupt `thread` and apply `signal/warn/error` passing `datum` and
`arguments`.

#### Exceptional situations:

None.

#### See also:

[**interrupt-thread**](../interrupt-thread),
[**error**](http://www.lispworks.com/documentation/HyperSpec/Body/f_error.htm),
[**signal**](http://www.lispworks.com/documentation/HyperSpec/Body/f_signal.htm),
[**warn**](http://www.lispworks.com/documentation/HyperSpec/Body/f_warn.htm)


#### Notes:

These functions are currently implemented on top of
[**interrupt-thread**](../interrupt-thread).
