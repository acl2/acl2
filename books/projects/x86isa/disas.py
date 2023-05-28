#!/usr/bin/env python3

import sys
import subprocess


def main() -> int:
    byte_str = ' '.join(f'{int(x):02x}' for x in sys.argv[1:])
    print(byte_str)

    subprocess.run(['rasm2', '-D', byte_str])

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
