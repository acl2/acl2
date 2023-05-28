import os
import sexpdata


def main() -> int:
    dependency_data = None
    with open("Makefile-tmp.lsp", "r") as fp:
        file_data = sexpdata.load(fp)
        for l in file_data:
            if sexpdata.car(l) == sexpdata.Symbol(":DEPENDENCY-MAP"):
                dependency_data = sexpdata.cdr(l)
                break
    if not dependency_data:
        print("Couldn't find dependency data")
        return 1

    # Time to build the ninja file
    with open("build.ninja", 'w') as fp:
        fp.write(
            "rule cert\n  command = cd $$(mktemp -d) && cert.pl $in > /dev/null; rm -r $$PWD\n\n")
        for dependency in dependency_data:
            # Make all paths absolute
            dependency = [os.path.abspath(dep) for dep in dependency]
            cert = sexpdata.car(dependency)
            depends_on = sexpdata.cdr(dependency)
            fp.write(
                f"build {cert}: cert {sexpdata.car(depends_on)} | {' '.join(sexpdata.cdr(depends_on))}\n\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
