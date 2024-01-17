---
date: 2022-01-07T08:00:00Z
title: Macro WITH-LOCK-HELD
weight: 12
---

#### Syntax:

**with-lock-held** (lock *&key* timeout) declaration\* forms\* => results

#### Arguments and values:

*lock* -> a [**lock**](../lock) object.\
*timeout* -> a non-negative real number.\
*declaration* -> a declare expression; not evaluated.\
*forms* -> an implicit progn.\
*results* -> the values returned by the forms.

#### Description:

Evaluates `forms`. Before the forms in BODY are evaluated, `lock` is
acquired as if by using [**acquire-lock**](../acquire-lock). After
the forms have been evaluated, or if a non-local control transfer is
caused (e.g. by `throw` or `signal`), the lock is released as if by
[**release-lock**](../release-lock).

#### Exceptional situations:

Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
is `lock` is not a [**lock**](../lock) object.\
Signals an error of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `timeout` is neither nil nor a non-negative real number.

#### See also:

[**lock**](../lock), [**acquire-lock**](../acquire-lock),
[**release-lock**](../release-lock)

#### Notes:

If the debugger is entered, it is unspecified whether the lock is
released at debugger entry or at debugger exit when execution is
restarted.
