---
date: 2022-01-07T08:00:00Z
title: 'Function THREAD-YIELD'
weight: 9
---

#### Syntax:

**thread-yield** => No values.

#### Arguments and values:

Returns no values.

#### Description

Causes the calling thread to relinquish the CPU to allow other threads
to run.

#### Exceptional situations:

None.

#### Notes:

On modern implementations that use native OS (SMP) threads, this
function is of little use. On some older implementations where threads
are scheduled in user space, it may be necessary or desirable to call
this periodically.
