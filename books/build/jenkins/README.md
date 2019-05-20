ACL2 Books Jenkins Build Scripts

Authors: Jared Davis <jared@centtech.com>, David Rager <ragerdl@defthm.com>

## Introduction

Jenkins is a popular tool for implementing continuous integration servers.  Its
homepage is here:

     http://jenkins-ci.org/

This directory contains build scripts for use with Jenkins.  The general idea
is to allow Jenkins to watch for new commits, and then automatically build ACL2
and the books (using "make all") on several Lisp platforms and ACL2 variants:

       ACL2() on CCL           } with quicklisp
       ACL2(h) on CCL          }
       ACL2(r) on CCL          }
       ACL2(h) on SBCL         }

       ACL2(h) on GCL-ANSI     } without quicklisp
       ACL2() on GCL-CLTL1     }

Jenkins has a nice interface that lets you see the progress of these jobs, and
it generally takes care of mundane issues like:

    - updating your copy of the sources, using either
         * full builds from a fresh checkout, or
         * "svn update" to minimize rebuilding
    - preventing multiple builds from interfering with one another
    - preventing machines from getting overloaded
    - noticing that a job seems to be running forever
    - keeping recent logs so you can review them later
    - (optional) emails/irc notifications whenever things fail

## Instructions

To make it possible to use these scripts in other environments, each
script starts with:

   source $JENKINS_HOME/env.sh

So you should be able to easily set up a suitable env.sh that
configures your PATH to contain ccl, sbcl, etc.

You'll first want to setup a single configuration Jenkins project that
runs build-single.sh.  If you don't pass in a $TARGET
parameter, it will build the "manual" target.  This will build the
manual on CCL for ACL2(h).

You should next be able to setup a Jenkins "multi-configuration"
project that uses build-multi.sh.  You'll need to pass in a build target in
the $TARGET environment variable, and you'll need to setup the LISP
env variable as a Jenkins "Axis".  You'll also probably want to setup
Axes for `ACL2_HONS`, `ACL2_PAR`, and `ACL2_REAL`, where each axis has the
options of `"" t`.

Your `gcl` executable name must start with `gcl` to avoid building
with quicklisp.

The scripts use `startjob`, a which in its simplest form is just a
wrapper for `bash`.  In more complicated scenarios, `startjob` can be
used to build the books using a cluster.

Please contact David or Jared with any questions or feedback.
