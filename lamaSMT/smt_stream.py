#!/usr/bin/python2

import subprocess
import re
import sys

pattern = re.compile(r"write\(4, \"(\(.*?)\\n")

proc = subprocess.Popen("strace -s 5000 " + " ".join(sys.argv[1:]), stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
for line in proc.communicate()[1].splitlines():
    match = pattern.search(line)
    if match:
        print match.group(1)
