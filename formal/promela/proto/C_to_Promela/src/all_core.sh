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

# initialize arguments
dir_rtems_grep_pat="$1"
source "$HOME0/all_core_args.sh"

# prevent future scripts without arguments of using the current "$@" when called with 'source'
shift $#

# execute 1 | 2 | 3a
source "$HOME0/1_gcc/core.sh" "$dir_rtems_grep_pat" "$dir_rtems/log"
(cd "$dir_rtems/build/sparc/leon3"
 python3_gcc "['-E']"
 ) \
 | source "$HOME0/2_downgrade_c11/core.sh" \
 | source "$HOME0/3_frama_c/core1.sh" \
 > init.i

# execute 3b
source "$HOME0/3_frama_c/core2.sh" "$dir_frama_c" init.i init_out.c

# execute 4
source "$HOME0/4_downgrade_c99/core.sh" init_out.c > init_out.c0

# execute 5
dir_current="$PWD"
dir_tmp="$(mktemp -d)"
(cd "$dir_tmp"
 source "$HOME0/5_modex/core.sh" "$dir_modex" "$dir_current/init_out.c0" "$dir_current/_modex_all.pml0"
 )
(cd "$dir_tmp"
 source _modex_.cln
 ) &

# execute 6
if [ -z ${SPLIT_FILE_WRITE_RAW+x} ] ; then
    if [ -z ${SPLIT_FILE_WRITE_INDEX+x} ] ; then
        SPLIT_FILE_WRITE_RAW=''
        export SPLIT_FILE_WRITE_RAW
    else
        export SPLIT_FILE_WRITE_INDEX
    fi
else
    export SPLIT_FILE_WRITE_RAW
fi
export SPLIT_FILE_PREF="$dir_isabelle_split_pref" # this static path is depending on paths in the input's content, it is fine if it does not exist
export SPLIT_FILE_C="$dir_current/init_out.c0"
export SPLIT_FILE_PML="$dir_current/_modex_all.pml0"
source "$HOME0/6_isabelle_c/core.sh" "$dir_isabelle" -d "$dir_isabelle_c" -d "$HOME0/6_isabelle_c/src_split" -c

# test: inspecting the output
ls c pml

# test: optional settings
cat > init.thy <<EOF
theory init
  imports Isabelle_C.C_Main
begin
C_file \<open>init.i\<close>
end
EOF

# exit
wait
