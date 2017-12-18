Shellpool Installation
======================

Shellpool is now available via [Quicklisp](http://www.quicklisp.org/).

After setting up Quicklisp, you should be able to install Shellpool by just
quickloading it.  That is, after starting your Lisp, just run:

```
(ql:quickload "shellpool")
```

And Shellpool should be loaded.


### Development Versions

Note that the version of Shellpool that is distributed via Quicklisp may
occasionally be out of date.  If you want to use the development version
instead, you can do, e.g.,:

* Locate your quicklisp `local-projects` directory,
  e.g., `~/quicklisp/local-projects`

* Use git to clone `shellpool` into `local-projects/shellpool`, e.g.,:

```shell
$ cd ~/quicklisp/local-projects
$ git clone https://github.com/jaredcdavis/shellpool
```

