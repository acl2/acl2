---
date: 2022-01-07T08:00:00Z
title: Function MAKE-RECURSIVE-LOCK
weight: 13
---

#### Syntax:

**make-recursive-lock** *&key* name => lock

#### Arguments and values:

*name* -> a string or nil.\
*lock* -> a [**recursive-lock**](../recursive-lock) object.

#### Description:

Creates a recursive lock named `name`.

#### Exceptional situations:

Signals a condition of type
[**type-error**](http://www.lispworks.com/documentation/HyperSpec/Body/e_tp_err.htm#type-error)
if `name` is neither a string nor nil.

#### See also:

[**recursive-lock**](../recursive-lock)

#### Notes:

A lock is also commonly known as a **mutex**.
