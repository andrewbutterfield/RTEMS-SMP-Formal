#!/bin/bash

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)

set -x
set -e
set -o pipefail

exec ../../../src/Promela_to_C/src/testgen_yaml.sh --annotation_file spin.yml testsuites_spfreechain01.pml --annotation_file refine_sptests/testsuites_spfreechain01.rfn.yml --annotation "$(cat testsuites.cfg.yml)"
