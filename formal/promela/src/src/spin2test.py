# SPDX-License-Identifier: BSD-2-Clause
"""Converts Annotated SPIN counter-examples to program test code"""

# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.

import src.refine_command as refine

#

import logging
import sys
import yaml

#

refine.logger.setLevel(logging.DEBUG)
refine.logger.addHandler(logging.StreamHandler (sys.stderr))

def words(string):
    return string.rsplit(' ')

def main(testNumber, dir0, fileRoot, preFile, postFile, runFile, refFile, testFile):
    refine.logger.debug("\n\tSpin2Test (Coconut/Python)\n\n")
    refine.logger.debug("Test Number {}\n".format(testNumber))

    if int(testNumber) < 0:
        num = ""
    else:
        num = "-{}".format(testNumber)

    spinFile = dir0 + "gen/" + fileRoot + num + ".spn"

    summaryFormat = "!{} --({}`)-> [{};_;{};{}] >> {}\n"
    refine.logger.debug(
        summaryFormat.format(spinFile, refFile, preFile, postFile, runFile,
                             testFile))

    annote_lines = []
    with open(spinFile) as spinfile:
        debug_lines = ''
        for line in spinfile:
            if line[0:4] == "@@@ ":
                debug_lines = debug_lines + line
                annote_lines = annote_lines + [line[4:][:-1]]
        refine.logger.debug(debug_lines)

    annote_bundle = map(words, annote_lines)

    refine.logger.debug("Annotation Bundle:\n {}".format(annote_bundle))

    with open(refFile) as reffile:
        ref_dict = yaml.safe_load(reffile.read())
        refine.logger.debug("\nREFINE DUMP")
        refine.logger.debug(yaml.dump(ref_dict))

    cmd = refine.command(ref_dict)

    cmd.setupLanguage()
    for ln in annote_bundle:
        cmd.refineSPINLine_main(ln)

    refine.logger.debug("\nP-Ids in use: {}\n ".format(cmd.procIds))
    refine.logger.debug("\n\tRefinement Complete; No of processes = {}".format(
        len(cmd.procIds)))

    with open("gen/"+testFile, 'w') as tstfile:

        with open(preFile) as prefile:
            tstfile.write(prefile.read())

        for line in cmd.test_body():
            tstfile.write(line)

        with open(postFile) as postfile:
            tstfile.write(postfile.read())

        with open(runFile) as runfile:
            tstfile.write(runfile.read().format(testNumber))
