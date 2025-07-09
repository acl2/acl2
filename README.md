ACL2 System and Community Books
===============================

The ACL2 theorem proving environment consists of two parts: The ACL2
System and The ACL2 Books.  This repository contains both.

### ACL2 System

The included version of the ACL2 System is the latest, under-development
version of the [ACL2 Theorem Prover][ACL2].  It is updated only by the
ACL2 authors, Matt Kaufmann and J Moore.

[ACL2]: http://www.cs.utexas.edu/users/moore/acl2 "ACL2 Home Page"

**WARNING**: On rare occasions development versions of ACL2 may be
incomplete, fragile, or unable to pass the usual regression tests.  You
may choose to download an official ACL2 release as described on the
[ACL2 Home Page][ACL2] or below in this README.

### ACL2 Books

The `books/` directory of this repository comprises the Community Books,
which are the canonical collection of open-source libraries for the ACL2
System.  As the name suggests, they are updated by the ACL2 community.

### Documentation

- The [Combined ACL2 + Books Manual][dev-manual] is updated frequently
  to track the latest changes to this repository.

- If you are instead using official, released Version 8.6 of ACL2, see
  the [Version 8.6 Manual][release-manual] instead.

Each of these manuals can be downloaded for offline use by clicking the
download button on the right hand side of the upper toolbar while
browsing the manual.

[release-manual]: http://www.cs.utexas.edu/users/moore/acl2/current/combined-manual/index.html
[dev-manual]:  http://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html

### Obtaining the Source Code

While active development of ACL2 occurs at the `acl2/acl2` repo on
GitHub, stable releases are officially distributed from the
`acl2-devel/acl2-devel` fork, which exists for that purpose.

#### Latest Stable Release

You can download a gzipped tarfile or zip file for the latest release,
which includes the [ACL2 system][ACL2] and the [community
books][community books], from [the releases page][releases] on GitHub.

Alternatively you can obtain a copy of the latest release using
[`git`][git].  For example, do the following in a fresh directory
(note the "." at the end).

```
git clone -b 8.6 https://github.com/acl2-devel/acl2-devel .
```

The new directory `/path/to/somewhere/acl2/` will now contain a copy of
ACL2 Version 8.6.  Please see the [ACL2 home page][ACL2], specifically
its [installation instructions][installation], for how to build an
executable and certify books in your new directory.

[ACL2]:            http://www.cs.utexas.edu/users/moore/acl2 "ACL2 Home Page"
[installation]:    http://www.cs.utexas.edu/users/moore/acl2/current/HTML/installation/installation.html
[releases]:        https://github.com/acl2-devel/acl2-devel/releases/
[git]:             http://git-scm.com
[community books]: http://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____COMMUNITY-BOOKS

#### Experimental Development Version

To check out the latest development version of the repository using
`git`, you can (for example) do the following in a fresh directory
(note the "." at the end):

```
git clone https://github.com/acl2/acl2 .
```

### Contributing

See the documentation for [how to contribute][how-to-contribute].

[how-to-contribute]: http://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____HOW-TO-CONTRIBUTE

### Staying Informed

We invite anyone who is using this repository to join the [acl2-books
mailing list][acl2-books], which receives commit messages and other
discussion related to ACL2 system- and book-related development.

[acl2-books]: http://groups.google.com/group/acl2-books

### Contributors Wanted!

Everyone can contribute documentation and advice to our [wiki] and
discuss [problems and feature requests][bugtracker].

If you would like to contribute to this repository, see the
documentation topic [git-quick-start].  Please note the [guidelines for
book development][books guidelines].

[git-quick-start]:  http://www.cs.utexas.edu/users/moore/acl2/manuals/latest/?topic=ACL2____GIT-QUICK-START
[wiki]:             https://github.com/acl2/acl2/wiki
[bugtracker]:       https://github.com/acl2/acl2/issues
[books guidelines]: https://github.com/acl2/acl2/wiki/Committing-code:-guidelines
