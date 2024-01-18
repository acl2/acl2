---
date: 2022-01-07T08:00:00Z
title: Class ATOMIC-INTEGER
weight: 1
---

#### Class precedence list:

atomic-integer, t.

#### Description:

This class represents an unsigned machine word that allows atomic
increment, decrement and swap.

#### See also:

[**make-atomic-integer**](../make-atomic-integer)

#### Notes:

Depending on the host implementation, the size of the integer is
either 32 or 64 bits.

This class is unavailble on Lisp implementations that lack underlying
atomic primitives. On some hosts, **atomic-integer** is implemented
using locks.
