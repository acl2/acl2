---
date: 2022-01-07T08:00:00Z
title: Class CONDITION-VARIABLE
weight: 1
---

#### Class precedence list:

Implementation-defined.

#### Description:

This class represents condition variables.

#### See also:

[**make-condition-variable**](../make-condition-variable)

#### Notes:

On some implementations the library exposes the native type directly,
while on others there is a custom implementations using semaphores and
locks.
