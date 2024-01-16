---
date: 2022-01-07T08:00:00Z
title: Function MAKE-CONDITION-VARIABLE
weight: 3
---

#### Syntax:

**make-condition-variable** *&key* name => condition-variable

#### Arguments and values:

*name* -> a string or nil.\
*condition-variable* -> a [**condition-variable**](../condition-variable) object.

#### Description:

Creates a condition variable named `name`.

#### Exceptional situations:

Signals a condition of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `name` is neither a string nor nil.

#### See also:

[**condition-variable**](../condition-variable)

#### Notes:

On some implementations the library exposes the native type directly,
while on others there is a custom implementations using semaphores and
locks.
