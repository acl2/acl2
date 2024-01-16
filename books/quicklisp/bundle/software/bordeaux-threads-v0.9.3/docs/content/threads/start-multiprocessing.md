---
date: 2022-01-07T08:00:00Z
title: 'Function START-MULTIPROCESSING'
weight: 10
---

#### Syntax:

**start-multiprocessing** => No values.

#### Arguments and values:

Returns no values.

#### Description:

If the host implementation uses user-level threads, start the
scheduler and multiprocessing, otherwise do nothing. It is safe to
call repeatedly.

#### Exceptional situations:

None.

#### Notes:

Only has an effect on Allegro, CMUCL and Lispworks.
