#!/bin/bash

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)

set -x
set -e
set -o pipefail

../../../src/Promela_to_C/src/testgen_ml_spin.sh testsuites_spintrcritical10_1.pml testsuites_spintrcritical10_1.rfn --promela "$(cat testsuites.cfg)"
mv -i _ testsuites_spintrcritical10_1.auto_output

../../../src/Promela_to_C/src/testgen_ml_spin.sh testsuites_spintrcritical10_2.pml testsuites_spintrcritical10_2.rfn --promela "$(cat testsuites.cfg)"
mv -i _ testsuites_spintrcritical10_2.auto_output

../../../src/Promela_to_C/src/testgen_ml_spin.sh testsuites_spintrcritical10_3.pml testsuites_spintrcritical10_3.rfn --promela "$(cat testsuites.cfg)"
mv -i _ testsuites_spintrcritical10_3.auto_output

../../../src/Promela_to_C/src/testgen_ml_spin.sh testsuites_validation.pml testsuites_validation.rfn --promela "$(cat testsuites.cfg)"
mv -i _ testsuites_validation.auto_output
