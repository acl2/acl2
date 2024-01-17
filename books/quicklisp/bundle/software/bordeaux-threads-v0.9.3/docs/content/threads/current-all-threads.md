---
date: 2022-01-07T08:00:00Z
title: 'Function CURRENT-THREAD, ALL-THREADS'
weight: 6
---

#### Syntax:

**current-thread** => thread\
**all-threads** => threads

#### Arguments and values:

*thread* -> a [thread](../class-thread) object.\
*threads* -> a list of [thread](../class-thread) objects.

#### Description:

**current-thread** returns the thread object representing the calling
thread.

**all-threads** returns a [fresh
list](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_f.htm#fresh)
of all running threads.

#### Exceptional situations:

None.

#### See also:

[**make-thread**](../make-thread)

#### Notes:

None.
