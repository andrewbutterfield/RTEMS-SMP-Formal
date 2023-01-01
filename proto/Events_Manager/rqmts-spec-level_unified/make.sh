#!/bin/bash

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)

set -x
set -e
set -o pipefail

../../../src/Promela_to_C/src/testgen_ml_spin.sh model-events-mgr.pml testsuites.rfn --promela "$(cat testsuites.cfg)"
