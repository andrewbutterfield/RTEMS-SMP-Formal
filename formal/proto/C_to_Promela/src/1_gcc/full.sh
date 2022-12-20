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

# install git
sudo apt install -y git

# download rsb rtems
git clone https://git.rtems.org/rtems-source-builder rsb
(cd ~/rsb
 git checkout 1ea1c9cdc56313e33abf39fce23a2ddf308ff5b3 # pairing rsb and rtems for "rtems version 6"
 )
git clone git@gitrepos.estec.esa.int:external/rtems-smp-qualification-rtems.git rtems
(cd ~/rtems
 git checkout b9c5d08c7ec402e10df45ba7f23d8655a18c9dee # pairing rsb and rtems for "rtems version 6"
 )

# install rsb
sudo apt install -y bison flex texinfo unzip python libpython-dev
(cd ~/rsb/rtems
 ../source-builder/sb-set-builder --source-only-download 6/rtems-sparc
 ../source-builder/sb-set-builder --prefix=$HOME/6 6/rtems-sparc
 )

# install rtems
sudo apt install -y pax

cat > ~/rtems/config.ini <<EOF
[sparc/leon3]
RTEMS_SMP = True
BUILD_TESTS = True
EOF
  # [sparc/gr712rc]
  # RTEMS_SMP = True
  # BUILD_TESTS = True

  # [sparc/gr740]
  # RTEMS_SMP = True
  # BUILD_TESTS = True

export PATH=~/6/bin:$PATH

(cd ~/rtems
 ./waf configure
 ./waf -v > log 2>&1

# test: setup of the input
 source "$HOME0/core.sh" smpmrsp01 log

# test: generation of the preprocessed version (and the one with comments)
 cd build/sparc/leon3
 python3_gcc "['-E']" > ~/init.c_pp &
 python3_gcc "['-E', '-CC']" > ~/init.c_pp_CC
 wait
 )

# test: inspecting the output
ls ~/init.c_pp ~/init.c_pp_CC
