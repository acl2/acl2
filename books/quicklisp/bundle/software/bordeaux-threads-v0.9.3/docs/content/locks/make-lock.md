---
date: 2022-01-07T08:00:00Z
title: Function MAKE-LOCK
weight: 10
---

#### Syntax:

**make-lock** *&key* name => lock

#### Arguments and values:

*name* -> a string or nil.\
*lock* -> a [**lock**](../lock) object.

#### Description:

Creates a non-recursive lock named `name`.

#### Exceptional situations:

Signals a condition of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `name` is neither a string nor nil.

#### See also:

[**lock**](../lock)

#### Notes:

A lock is also commonly known as a **mutex**.

On some implementations, the host lock type is always recursive.
