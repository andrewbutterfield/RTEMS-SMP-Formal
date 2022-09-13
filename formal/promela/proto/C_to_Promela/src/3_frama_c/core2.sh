#

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)

frama_c="$1"
arg1="$2"
arg2="$3"
shift 3

"$frama_c/bin/frama-c" "$arg1" -c11 -machdep gcc_x86_32 -print -ocode "$arg2" "$@"
