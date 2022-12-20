#!/bin/bash

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)

set -x
set -e
set -o pipefail

# resolve home directory of the project
HOME0="$(dirname "$(python3 -c "import os; print(os.path.realpath('$0'))")")"

# print the date and disk space for each executed line
PS4='+ $EPOCHREALTIME $(df -B 1 --output=used ~ | tail -n 1) ($LINENO) '

# install wget default-jre-headless
sudo apt install -y wget default-jre-headless

# download isabelle
wget -nv https://isabelle.in.tum.de/website-Isabelle2019/dist/Isabelle2019_linux.tar.gz
tar xzf Isabelle2019_linux.tar.gz

# download isabelle_c and isabelle_split
wget https://www.scss.tcd.ie/frederic.tuong/rtems_split.tar.gz
tar xzf rtems_split.tar.gz

# test: setup of the input
mkdir ~/smpmrsp01
(cd ~/smpmrsp01
 wget https://www.scss.tcd.ie/frederic.tuong/init_out.c0
 wget https://www.scss.tcd.ie/frederic.tuong/_modex_all.pml0
 )

# test: generation of the tree structure
export SPLIT_FILE_WRITE_RAW=''
export SPLIT_FILE_PREF="6" # this static path is depending on paths in the input's content, it is fine if it does not exist
export SPLIT_FILE_C="$HOME/smpmrsp01/init_out.c0"
export SPLIT_FILE_PML="$HOME/smpmrsp01/_modex_all.pml0"
source "$HOME0/core.sh" ~/Isabelle2019 -d ~/rtems_split

# test: inspecting the output
ls c pml
