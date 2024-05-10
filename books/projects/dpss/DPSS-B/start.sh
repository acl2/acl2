#!/bin/bash
##
## Copyright (C) 2023, Collins Aerospace
## All rights reserved.
##
## This software may be modified and distributed under the terms
## of the 3-clause BSD license.  See the LICENSE file for details.
##

echo "URL: http://localhost:8893"

docker run -d -p 8893:8888 -v ${PWD}/work:/home/jovyan/work --name z3-notebook z3 start.sh jupyter notebook --no-browser --NotebookApp.token='' --NotebookApp.password=''
