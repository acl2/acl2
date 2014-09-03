Community ACL2 System and Books
====

The ACL2 theorem proving environment consists of two parts: The ACL2 System and The ACL2 Books.  This repository contains both.

### ACL2 System
The included version of the ACL2 System is the latest, under-development version of the <a href="http://www.cs.utexas.edu/users/moore/acl2">ACL2 Theorem Prover</a>.  It is updated only by the ACL2 authors, Matt Kaufmann and J Moore.

**WARNING**: The ACL2 System authors consider the snapshots of the system in this repository to be **experimental**; they may be incomplete, fragile, and unable to pass our own regression. If you want a stable system, you should instead download an official, released version of ACL2 from the <a href="http://www.cs.utexas.edu/users/moore/acl2">ACL2 Home Page</a>.


### ACL2 Books
The books/ directory of this repository comprises the Community Books, which are the canonical collection of open-source libraries for the ACL2 System</a>.

### Documentation

The <a href="http://www.cs.utexas.edu/users/moore/acl2/current/combined-manual/index.html">Combined ACL2 + Books Manual</a> has extensive documentation for many books, and also for ACL2 itself. You can follow a link on that page to download an offline copy.  That manual corresponds to the most recent ACL2 release; there is also a reasonably up-to-date <a href="http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index.html">manual that corresponds to this repository</a>.


### Obtaining the Source Code

#### Latest Stable Release

You may wish to download a pair of gzipped tarfiles: the <a href="http://www.cs.utexas.edu/users/moore/acl2/current/HTML/installation/installation.html">ACL2 System</a> and the <a href="http://acl2.org/index.html">ACL2 books</a>.  Make sure you grab the same version, which should generally be for the most recent ACL2 release.

In the future we expect that you will be able to check out both at once using <a href="http://git-scm.com">git</a> by checking out one of the Tags, using syntax such as the following.

`git clone git://github.com/acl2/acl2; cd acl2; git checkout acl2-7.0`


#### Experimental Development Version

To check out an effectively read-only copy of the repository using <a href="http://git-scm.com">git</a>, run:

`git clone git://github.com/acl2/acl2`

To check out a copy of the repository that can be used to write back to github, run:

`git clone https://github.com/acl2/acl2`

### Contributing

See the wiki page for <a href="https://code.google.com/p/acl2-books/wiki/ACL2RepoGitTips">our discussion on how to contribute</a>.

Even though we have merged the Community Books (formerly acl2-books) and ACL2 System (formerly acl2-devel) repositories into one, changes should be made only to the `books/` subdirectory unless you are Matt Kaufmann or J Moore, since everything outside `books/` is part of the ACL2 system.  (If you have suggestions for system changes, they should be emailed to <a href="mailto:kaufmann@cs.utexas.edu">Matt or J</a>, as has been done in the past.)

### Staying Informed

We invite anyone who is using this repository to join the <a href="http://groups.google.com/group/acl2-books">acl2-books mailing list</a>, which receives commit messages and other discussion related to ACL2 system- and book-related development.


### Contributors wanted!

Everyone can contribute documentation and advice to our <a href="http://code.google.com/p/acl2-books/w/list">Wiki</a> and discuss <a href="http://code.google.com/p/acl2-books/issues/list">problems and feature requests</a>.

If you would like to contribute to this repository, email <a href="mailto:jared@centtech.com">Jared Davis</a> or <a href="mailto:ragerdl@gmail.com">David Rager</a> and ask them to add you to the project.  Please note the <a href="http://code.google.com/p/acl2-books/wiki/CommittingCode">guidelines for book development</a>.
