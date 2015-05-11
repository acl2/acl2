Community ACL2 System and Books
===============================

The ACL2 theorem proving environment consists of two parts: The ACL2
System and The ACL2 Books.  This repository contains both.

### ACL2 System

The included version of the ACL2 System is the latest, under-development
version of the [ACL2 Theorem Prover][ACL2].  It is updated only by the
ACL2 authors, Matt Kaufmann and J Moore.

**WARNING**: The ACL2 System authors consider the snapshots of the
system in this repository to be **experimental**; they may be
incomplete, fragile, and unable to pass our own regression. If you want
a stable system, you should instead download an official, released
version of ACL2 from the [ACL2 Home Page][ACL2].

[ACL2]: http://www.cs.utexas.edu/users/moore/acl2 "ACL2 Home Page"

### ACL2 Books

The books/ directory of this repository comprises the Community Books,
which are the canonical collection of open-source libraries for the ACL2
System.

### Documentation

The [Combined ACL2 + Books Manual][combined manual] has extensive
documentation for many books, and also for ACL2 itself. You can follow a
link on that page to download an offline copy.  That manual corresponds
to the most recent ACL2 release; there is also a reasonably up-to-date
[manual that corresponds to this repository][manual].

[manual]: http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index.html
[combined manual]: http://www.cs.utexas.edu/users/moore/acl2/current/combined-manual/index.html


### Obtaining the Source Code

#### Latest Stable Release

You can download a gzipped tarfile or zip file for the latest release,
which includes the [ACL2 system][ACL2] and the [community
books][community books].  Simply click on the "release" button at the
top of github.com/acl2/acl2.  Alternatively you get a (read-only) copy
from git as follows:

```
git clone git://github.com/acl2-devel/acl2-devel acl2; cd acl2; git checkout 7.1
```

Your current directory is now a copy of ACL2 Version 7.1.  This
directory is intended for ACL2 use, not for modification using git
(discussed in Contributing, below).  Please see the [ACL2 home
page][ACL2], specifically its [installation
instructions][installation], for how to build an executable and
certify books in your new directory.

[ACL2]: http://www.cs.utexas.edu/users/moore/acl2 "ACL2 Home Page"
[installation]: http://www.cs.utexas.edu/users/moore/acl2/current/HTML/installation/installation.html
[git]: http://git-scm.com
[community books]: http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index.html?topic=ACL2____COMMUNITY-BOOKS


#### Experimental Development Version

To check out an effectively read-only copy of the repository using
[git], run:

```
git clone git://github.com/acl2/acl2
```

### Contributing

See the documentation for [how to contribute][git tips].

Even though we have merged the Community Books (formerly acl2-books) and
ACL2 System (formerly acl2-devel) repositories into one, changes should
be made only to the `books/` subdirectory unless you are Matt Kaufmann
or J Moore, since everything outside `books/` is part of the ACL2
system.  (If you have suggestions for system changes, they should be
emailed to [Matt or J](mailto:kaufmann@cs.utexas.edu), as has been done
in the past.)

[git tips]: http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index.html?topic=ACL2____GIT-QUICK-START

### Staying Informed

We invite anyone who is using this repository to join the [acl2-books
mailing list][acl2-books], which receives commit messages and other
discussion related to ACL2 system- and book-related development.

[acl2-books]: http://groups.google.com/group/acl2-books


### Contributors wanted!

Everyone can contribute documentation and advice to our [wiki] and
discuss [problems and feature requests][bugtracker].

If you would like to contribute to this repository, see the documentation topic [git-quick-start].
Please note the [guidelines for book development][books guidelines].

[git-quick-start]: http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/?topic=ACL2____GIT-QUICK-START
[wiki]: https://github.com/acl2/acl2/wiki
[bugtracker]: https://github.com/acl2/acl2/issues
[books guidelines]: https://github.com/acl2/acl2/wiki/Committing-code:-guidelines
