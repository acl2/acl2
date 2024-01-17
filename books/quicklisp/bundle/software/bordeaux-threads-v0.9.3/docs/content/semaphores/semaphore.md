---
date: 2022-01-07T08:00:00Z
title: Class SEMAPHORE
weight: 1
---

#### Class precedence list:

Implementation-defined.

#### Description:

This class represents semaphores.

#### See also:

[**make-semaphore**](../make-semaphore)

#### Notes:

On some implementations the library exposes the native type directly,
while on others there is a custom implementations using condition
variables and locks.
