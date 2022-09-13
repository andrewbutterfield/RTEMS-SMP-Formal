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

# install opam
sudo apt install -y opam

# init opam
opam init -a
eval $(opam env)

# install a minimal version of frama-c.20.0 dependencies
sudo apt install -y autoconf graphviz libgmp-dev libgnomecanvas2-dev libgtksourceview2.0-dev zlib1g-dev
opam install -y --deps-only frama-c.20.0

# install a modified version of frama-c.20.0
wget https://www.scss.tcd.ie/frederic.tuong/Frama-C-snapshot.tar.gz
tar xzf Frama-C-snapshot.tar.gz
(cd Frama-C-snapshot
 autoconf
 ./configure
 make -j 6
 )

# test: setup of the input
mkdir ~/smpmrsp01
(cd ~/smpmrsp01
 wget https://www.scss.tcd.ie/frederic.tuong/init.c_pp0
 source "$HOME0/core1.sh" init.c_pp0 > init.i # an in-place replacement would also work
 )

# test: generation using the modified version of frama-c.20.0
source "$HOME0/core2.sh" ./Frama-C-snapshot ~/smpmrsp01/init.i ~/smpmrsp01/init_out.c # an input file ending with a .i as extension sets frama-c.20.0 to skip its preprocessing, otherwise a different preprocessing is applied by default

# test: inspecting the output
ls ~/smpmrsp01/init_out.c
