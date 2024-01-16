---
date: 2022-01-07T08:00:00Z
title: Documentation
---

## Raison d'être

Bordeaux-Threads is a minimal library that aims to provide the basic
concepts required for multi-threading programming, such as threads,
mutexes, semaphores and condition variables. Higher-level data
structures such as queues, mailboxes, thread pools, execution graphs,
etc... tend to be more specialized and are better left to other
libraries.

This document describes the second version of the API (APIv2), which
differs from the first version in a few key points and aims to provide
a more uniformous interface across all Common Lisp implementations.

## Migration from APIv1 to APIv2

APIv2 is mostly compatible with v1, and in most cases it should
suffice to replace all references to package `bordeaux-threads` (or
`bt`) with `bordeaux-threads-2` (or `bt2`).

For more details, there's a [blog
post](https://blog.cddr.org/posts/2023-05-27-bordeaux-threads-apiv2/).

## Host support

When Bordeaux-Threads was created, most Common Lisp implementations
were either single-threaded or provided user-space scheduling akin to
green threads, and therefore Bordeaux-Threads tried to support all
such implementations as well as possible.

Bordeaux-Threads APIV2 no longer supports single-threaded
implementations and was conceived to work best with hosts that provide
SMP threads.

In most cases Bordeaux-Threads simply wraps the primitives provided by
the host implementation. Whenever the primitives are absent from the
host, we try to provide an ersatz implementation that is optimized for
correctness and readability rather than performance.

The two absolutely necessary primitives are **threads** and
**locks**. **Semaphores** and **condition variables** can be
implemented in terms of one another, and that's the case on a few
implementations. **Atomic operations** vary greatly in what kind of
forms they operate on so we do not expose them, instead providing
slightly higher-level constructs.
