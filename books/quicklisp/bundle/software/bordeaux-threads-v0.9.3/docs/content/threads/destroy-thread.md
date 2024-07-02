---
date: 2022-01-07T08:00:00Z
title: 'Function DESTROY-THREAD'
weight: 13
---

#### Syntax:

**destroy-thread** thread => thread

#### Arguments and values:

*thread* -> a [thread](../class-thread) object.

#### Description:

Terminates the thread `thread`.

#### Exceptional situations:

Signals [bordeaux-threads-error](../bordeaux-threads-error) if
attempting to destroy the calling thread, or a thread that already
terminated.

#### See also:

[**join-thread**](../join-thread)

#### Notes:

This should be used with caution: it is implementation-defined whether
the thread runs cleanup forms or releases its locks first.
