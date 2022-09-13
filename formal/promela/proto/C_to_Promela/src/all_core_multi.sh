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
source "$HOME0/all_core_args.sh"
source "$HOME0/all_core_multi_args.sh"

pref_dir='0'

# prevent future scripts without arguments of using the current "$@" when called with 'source'
shift $#

# iterate on a list of patterns
function all_core {
    local dir1="$1"
    shift
    local pats="$@"
    local dir0="${HOME0}/_/${dir1}"
    mkdir -p "$dir0"

    cd "$dir0"
    local cpt=0
    for pat in $pats
    do
        local dir="${cpt}_$(echo "$pat" | tr '/.' '_')"
        mkdir "$dir"
        cd "$dir"
        "$HOME0/all_core.sh" "$pat"
        local proc=$?
        cd ..
        cpt=$(expr "$cpt" + 1)
        test $proc -eq 0 || break $proc
    done
}

function all_core0 {
    local dir1="$1"
    shift
    local main="$1"
    shift
    local pats="$@"
    local dir0="${HOME0}/_/$dir1"
    mkdir -p "$dir0"

    cd "$dir0"

    local cpt=0
    for pat in $pats
    do
        local pat0="$(echo "$pat" | tr '/.' '_')"
        local dir="${cpt}_${pat0}"
        echo "${pat0}" >> split_pat
        echo "${HOME0}/_/${pref_dir}/raw/$dir/init_out.c0" >> split_path_c
        echo "${HOME0}/_/${pref_dir}/raw/$dir/_modex_all.pml0" >> split_path_pml
        cpt=$(expr "$cpt" + 1)
    done
    
    local cpt=0
    local dir_main="${cpt}_$(echo "$main" | tr '/.' '_')"
    export SPLIT_FILE_C="${dir0}/../raw/${dir_main}/init_out.c0" # TODO should be optional
    export SPLIT_FILE_PML="${dir0}/../raw/${dir_main}/_modex_all.pml0" # TODO should be optional

    echo "$main" >> split_pat
    echo $SPLIT_FILE_C >> split_path_c
    echo $SPLIT_FILE_PML >> split_path_pml

    export SPLIT_FILE_PREF="$dir_isabelle_split_pref" # this static path is depending on paths in the input's content, it is fine if it does not exist
    export SPLIT_FILE_INDEX_PAT="${dir0}/split_pat"
    export SPLIT_FILE_INDEX_C="${dir0}/split_path_c"
    export SPLIT_FILE_INDEX_PML="${dir0}/split_path_pml"
    bash -- "$HOME0/6_isabelle_c/core.sh" "$dir_isabelle" -d "$dir_isabelle_c" -d "$HOME0/6_isabelle_c/src_split" -c # executing 'bash' instead of 'source' to prevent an 'export' side-effect
    unset SPLIT_FILE_C
    unset SPLIT_FILE_PML
    unset SPLIT_FILE_PREF
    unset SPLIT_FILE_INDEX_PAT
    unset SPLIT_FILE_INDEX_C
    unset SPLIT_FILE_INDEX_PML

    local proc=$?
    test $proc -eq 0 || break $proc
}

# execute a variant of all_core
export SPLIT_FILE_WRITE_RAW=''
all_core "${pref_dir}/raw" "$pats"
unset SPLIT_FILE_WRITE_RAW

# execute a variant of all_core
export SPLIT_FILE_WRITE_INDEX=''
all_core "${pref_dir}/index" "$pats"
unset SPLIT_FILE_WRITE_INDEX

# execute a variant of all_core
for main in $mains
do
    # execute a variant of all_core
    export SPLIT_FILE_WRITE_RAW=''
    all_core "$main/raw" "$main"
    unset SPLIT_FILE_WRITE_RAW

    # execute a variant of all_core
    export SPLIT_FILE_WRITE_INDEX=''
    all_core "$main/index" "$main"
    unset SPLIT_FILE_WRITE_INDEX

    # execute a variant of all_core
    export SPLIT_FILE_WRITE_DIFF=''
    all_core0 "$main/diff" "$main" "$pats"
    unset SPLIT_FILE_WRITE_DIFF
done
