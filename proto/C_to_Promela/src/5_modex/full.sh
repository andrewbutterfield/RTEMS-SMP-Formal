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

# install wget unzip
sudo apt install -y wget unzip

# download modex
wget https://github.com/nimble-code/Modex/archive/master.zip # assuming it is working as with version e6319f5fb465ed4e2017a5b24b1d963efe3cd2da
unzip master.zip

# install modex
sudo apt install -y bison flex
(cd Modex-master
 make
 )

# test: setup of the input
wget https://www.scss.tcd.ie/frederic.tuong/init_out.c0

# test: generation of the model
source "$HOME0/core.sh" ~/Modex-master init_out.c0 _modex_all.pml0

# test: inspecting the output
ls _modex_all.pml0
