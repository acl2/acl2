---
date: 2022-01-07T08:00:00Z
title: 'Function JOIN-THREAD'
weight: 7
---

#### Syntax:

**join-thread** thread => multiple values

#### Arguments and values:

*thread* -> a [thread](../class-thread) object.

#### Description

Wait until `thread` terminates, or if it has already terminated,
return immediately.

The return values of the thread function are returned.

#### Examples


```
(let ((thread (bt2:make-thread
               (lambda () (values 1 2 3)))))
  (bt2:join-thread thread))

```
=> 1, 2, 3

#### Exceptional situations:

If a thread is terminated by an unhandled condition, or by
[**destroy-thread**](../destroy-thread), then the condition
[**abnormal-exit**](../abnormal-exit) is signaled.

#### See also:

[**make-thread**](./make-thread),
[**abnormal-exit**](../abnormal-exit)

#### Notes:

Due to how **join-thread** interacts with the dynamic environment
established by **make-thread**, it is not safe to join with a thread
that was created outside Bordeaux-Threads. For example, the following
code has undefined behaviour and might very well corrupt the image:

```
(mapcar #'bt2:join-thread (bt2:all-threads))
```

Bordeaux-Threads can only record instances of thread termination due
to unhandled conditions or the use of
[**destroy-thread**](../destroy-thread). In case of other ways to
terminate a thread, such as throwing to an implementation-specific tag
defined in the dynamic environment of the thread function, the
behaviour of **join-thread** is undefined.
