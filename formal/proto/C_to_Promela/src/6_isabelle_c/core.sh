#

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)

isabelle="$1"
shift

[ -z ${SPLIT_FILE_EXEC+x} ] && SPLIT_FILE_EXEC="$PWD"
export SPLIT_FILE_EXEC

"$isabelle/bin/isabelle" build -o "parallel_proofs=3" -v -b "$@" Isabelle_Split_Exec
