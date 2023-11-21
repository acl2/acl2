---
date: 2022-01-07T08:00:00Z
title: Macro WITH-TIMEOUT
weight: 2
---

#### Syntax:

**with-timeout** (timeout) declaration\* forms\* => results

#### Arguments and values:

*timeout* -> a non-negative real number.\
*declaration* -> a declare expression; not evaluated.\
*forms* -> an implicit progn.\
*results* -> the values returned by the forms.

#### Description:

Execute `forms` and signal a condition of type
[**timeout**](../timeout) if the execution of `forms` does not
complete within `timeout` seconds.

#### Exceptional situations:

[**timeout**](../timeout), **not-implemented**

#### See also:

[**timeout**](../timeout)

#### Notes:

On implementations which do not support **with-timeout** natively and
don't support threads either it signals a condition of type
**not-implemented**.
