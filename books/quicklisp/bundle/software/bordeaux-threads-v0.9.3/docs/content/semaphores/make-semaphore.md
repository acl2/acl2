---
date: 2022-01-07T08:00:00Z
title: Function MAKE-SEMAPHORE
weight: 3
---

#### Syntax:

**make-semaphore** *&key* name count => semaphore

#### Arguments and values:

*name* -> a string or nil.\
*count* -> non-negative integer.\
*semaphore* -> a [**semaphore**](../semaphore) object.

#### Description:

Creates a semaphore named `name` and with initial value `count`.

#### Exceptional situations:

Signals a condition of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `name` is neither a string nor nil.\
Signals a condition of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `count` is not a non-negative integer (an unsigned-byte).

#### See also:

[**semaphore**](../semaphore)

#### Notes:

On some implementations the library exposes the native type directly,
while on others there is a custom implementations using condition
variables and locks.
