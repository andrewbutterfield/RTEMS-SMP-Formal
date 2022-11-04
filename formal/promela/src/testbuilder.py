#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-2-Clause
"""Runs SPIN to generate test code for all defined scenarios"""

# Copyright (C) 2021 Trinity College Dublin (www.tcd.ie)
#               Robert Jennings
#               Andrew Butterfield
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

import sys
import os
import glob
import shutil
import yaml
from pathlib import Path
from datetime import datetime


def clean(model):
    """Cleans out generated files in current directory"""
    print("Removing spin and test files for", model)
    files = glob.glob('pan')
    trails = glob.glob(model + '*.trail')
    files += trails
    files += glob.glob(model + '*.spn')
    if len(trails) == 1:
        files += glob.glob('tr-' + model + '.c')
    else:
        files += glob.glob('tr-' + model + '-*.c')
    for file in files:
        os.remove(file)


def archive(model):
    print(f"Archiving spin files for {model}")
    files = glob.glob(model + '*.trail')
    files += glob.glob(model + '*.spn')
    date = datetime.now().strftime("%Y%m%d-%H%M%S")
    archive_dir = Path(f"archive/{date}")
    archive_dir.mkdir(parents=True, exist_ok=True)
    for file in files:
        shutil.copy2(file, archive_dir)


def zero(modelfile):
    """Modifies model file to refer only to the top-level testcase source"""
    # Update {modelname}.yml
    print(f"Zeroing {modelfile}")
    with open(modelfile) as file:
        model0 = yaml.load(file, Loader=yaml.FullLoader)
    model0['source'] = ["testsuites/validation/ts-model-0.c"]
    with open(modelfile, 'w') as file:
        yaml.dump(model0, file)


def generate(model, testgen):
    """Generates all the test sources in the current directory"""
    # Check necessary files are present
    ready = True
    if not os.path.isfile(model + ".pml"):
        print("Promela file does not exist for model")
        ready = False
    if not os.path.isfile(model + "-pre.h"):
        print("Preconditions file does not exist for model")
        ready = False
    if not os.path.isfile(model + "-post.h"):
        print("Postconditions file does not exist for model")
        ready = False
    if not os.path.isfile(model + "-run.h"):
        print("Promela file does not exist for model")
        ready = False
    if not os.path.isfile(model + "-rfn.yml"):
        print("Refinement file does not exist for model")
        ready = False
    if not ready:
        sys.exit(1)

    # Generate trail, spin and c files
    print("Generating spin and test files for", model)
    os.system("spin -DTEST_GEN -run -E -c0 -e " + model + ".pml")
    no_of_trails = len(glob.glob(model + '*.trail'))
    if no_of_trails == 1:
        os.system("spin -T -t " + model + ".pml > " + model + ".spn")
        os.system(f"python {testgen} {model}")
        sys.exit(0)
    for i in range(no_of_trails):
        os.system("spin -T -t" + str(i + 1) + " " + model + ".pml > " +
                  model + "-" + str(i) + ".spn")
        os.system(f"python {testgen} {model} {i}")


def copy(model, codedir, rtems, modfile):
    """Copies C testfiles to test directory and updates the model file """
    # Remove old test files
    print("Removing old files for model " + model)
    files = glob.glob(codedir + "tr-" + model + '*.c')
    files += glob.glob(codedir + "tr-" + model + '*.h')
    files += glob.glob(codedir + "tc-" + model + '*.c')
    for file in files:
        os.remove(file)

    # Copy new test files
    print("Copying new files for model " + model)
    files = glob.glob("tr-" + model + '*.c')
    files += glob.glob("tr-" + model + '*.h')
    files += glob.glob("tc-" + model + '*.c')
    for file in files:
        shutil.copyfile(file, rtems + "testsuites/validation/" + file)

    # Update model-0.yml
    print(f"Updating {modfile} for model " + model)
    with open(modfile) as file:
        model0 = yaml.load(file, Loader=yaml.FullLoader)
    source_list = model0['source']
    source_set = set(source_list)
    files = glob.glob("tr-" + model + '*.c')
    files += glob.glob("tc-" + model + '*.c')
    for file in files:
        source_set.add('testsuites/validation/' + file)
    new_list = list(source_set)
    model0['source'] = sorted(new_list)
    with open(modfile, 'w') as file:
        yaml.dump(model0, file)


def get_config(source_dir):
    config = dict()
    with open(source_dir + "/testbuilder.yml") as file:
        global_config = yaml.load(file, Loader=yaml.FullLoader)
        for key, val in global_config.items():
            config[key] = val
    if Path("testbuilder.yml").exists():
        with open("testbuilder.yml") as file:
            local_config = yaml.load(file, Loader=yaml.FullLoader)
            for key, val in local_config.items():
                config[key] = val

    if {"spin2test", "rtems", "rsb", "simulator", "testyaml", "testcode", "testexe"} - config.keys():
        print("Please configure testbuilder.yml")
        sys.exit(1)
    return config


def main():
    """generates and deploys C tests from Promela models"""
    if not (len(sys.argv) == 2 and sys.argv[1] == "help"
            or len(sys.argv) == 3 and sys.argv[1] == "clean"
            or len(sys.argv) == 3 and sys.argv[1] == "archive"
            or len(sys.argv) == 2 and sys.argv[1] == "zero"
            or len(sys.argv) == 3 and sys.argv[1] == "generate"
            or len(sys.argv) == 3 and sys.argv[1] == "copy"
            or len(sys.argv) == 2 and sys.argv[1] == "compile"
            or len(sys.argv) == 2 and sys.argv[1] == "run"):
        print("USAGE:")
        print("help - these instructions")
        print("clean modelname - remove spin, test files")
        print("archive - archives spin files")
        print("zero  - remove all tesfiles from RTEMS")
        print("generate modelname - generate spin and test files")
        print("copy modelname - copy test files and configuration to RTEMS")
        print("compile - compiles RTEMS tests")
        print("run - runs RTEMS tests")
        sys.exit(1)

    source_dir = os.path.dirname(os.path.realpath(__file__))

    config = get_config(source_dir)

    if not Path.exists(Path(f"{source_dir}/spin2test.py"))\
            or not Path.exists(Path(f"{source_dir}/env")):
        print(f"Setup incomplete...")
        print(f"Please run the following before continuing:")
        print(f"cd {source_dir} && bash src.sh")
        print(f". {source_dir}/env/bin/activate")
        sys.exit(1)

    if sys.argv[1] == "help":
        with open(source_dir + "/testbuilder.help") as helpfile:
            print(helpfile.read())

    if sys.argv[1] == "generate":
        generate(sys.argv[2], config["spin2test"])

    if sys.argv[1] == "clean":
        clean(sys.argv[2])

    if sys.argv[1] == "archive":
        archive(sys.argv[2])

    if sys.argv[1] == "zero":
        zero(config["testyaml"])

    if sys.argv[1] == "copy":
        copy(sys.argv[2], config["testcode"], config["rtems"], config["testyaml"])

    if sys.argv[1] == "compile":
        os.chdir(config["rtems"])
        os.system("./waf configure")
        os.system("./waf")

    if sys.argv[1] == "run":
        os.chdir(config["rsb"])
        sim_command = config["simulator"] + " -leon3 -r s -m 2 "
        print("Doing " + sim_command + config["testexe"])
        os.system(sim_command + config["testexe"])


if __name__ == '__main__':
    main()
