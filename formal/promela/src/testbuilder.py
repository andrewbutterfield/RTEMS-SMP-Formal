#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-2-Clause
"""Runs SPIN to generate test code for all defined scenarios"""

# Copyright (C) 2021-24 Trinity College Dublin (www.tcd.ie)
#               James Gooding Hunt
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
import subprocess
import glob
import shutil
from functools import wraps
import yaml
from pathlib import Path
from datetime import datetime


def catch_subprocess_errors(func):
    @wraps(func)
    def wrapper(*args, **kwargs):
        try:
            result = func(*args, **kwargs)
        except subprocess.CalledProcessError as e:
            print(f"error executing: {e.cmd}")
            sys.exit(1)
        return result
    return wrapper


def all_steps(models, model_to_path, source_dir):
    if models == ["allmodels"]:
        models = list(model_to_path.keys())

    for model in models:
        path = model_to_path[model]
        config = get_config(source_dir, model)
        refine_config = get_refine_config(source_dir, model, path)
        clean(model, model_to_path, source_dir)
        generate_spin_files(model, path, config["spinallscenarios"],
                            refine_config)
        generate_test_files(model, path, config["spin2test"], refine_config)
        copy(model, path, config["testcode"], config["rtems"],
             config["testyaml"], config["testsuite"],
             refine_config["testfiletype"])

    compile(config["rtems"])
    run_simulator(config["simulator"], config["simulatorargs"],
                  config["testexe"], config["testsuite"])


def clean(model, model_to_path, source_dir):
    """Cleans out generated files in models directory"""
    cwd = os.getcwd()
    if model == "allmodels":
        models = list(model_to_path.keys())
    else:
        models = [model]
    for model_name in models:
        model_dir = model_to_path[model_name]
        config = get_config(source_dir, model_name)
        refine_config = get_refine_config(source_dir, model_name, model_dir)
        os.chdir(model_dir)
        print(f"Removing spin and test files for {model_name}")
        files = get_generated_files(model_name, config["testsuite"],
                                    refine_config["testfiletype"])
        for file in files:
            os.remove(file)
    os.chdir(cwd)


def archive(model, model_dir, testsuite, test_extension):
    cwd = os.getcwd()
    os.chdir(model_dir)
    print(f"Archiving spin and test files for {model}")
    files = get_generated_files(model, testsuite, test_extension)
    date = datetime.now().strftime("%Y%m%d-%H%M%S")
    archive_dir = Path(f"archive/{date}")
    archive_dir.mkdir(parents=True, exist_ok=True)
    for file in files:
        shutil.copy2(file, archive_dir)
    print(f"Files archived to {archive_dir}")
    os.chdir(cwd)


def zero(model_file, testsuite_name):
    """Modifies model file to refer only to the top-level testcase sources"""
    # Update {model_file}.yml
    print(f"Zeroing {testsuite_name}.yml")
    with open(model_file) as file:
        model_yaml = yaml.load(file, Loader=yaml.FullLoader)
    model_yaml['source'] = [f"testsuites/validation/tx-{testsuite_name}.c"
                           ,f"testsuites/validation/ts-{testsuite_name}.c"]
    with open(model_file, 'w') as file:
        yaml.dump(model_yaml, file)


def ready_to_generate(model, refine_config):
    """Checks if relevant files are in place for spin and test generation"""
    ready = True
    if not os.path.isfile(f"{model}.pml"):
        print("Promela file does not exist for model")
        ready = False
    if not os.path.isfile(f"{refine_config['preamble']}"):
        print("Preconditions file does not exist for model")
        ready = False
    if not os.path.isfile(f"{refine_config['postamble']}"):
        print("Postconditions file does not exist for model")
        ready = False
    if not os.path.isfile(f"{refine_config['runfile']}"):
        print("Promela file does not exist for model")
        ready = False
    if not os.path.isfile(f"{refine_config['refinefile']}"):
        print("Refinement file does not exist for model")
        ready = False
    return ready


@catch_subprocess_errors
def generate_spin_files(model, model_dir, spinallscenarios, refine_config):
    """Create spin files from model"""
    cwd = os.getcwd()
    os.chdir(model_dir)
    if not ready_to_generate(model, refine_config):
        sys.exit(1)
    print(f"Generating spin files for {model}")
    subprocess.run(f"spin {spinallscenarios} {model}.pml",
                   check=True, shell=True)
    no_of_trails = len(glob.glob(f"{model}*.trail"))
    if no_of_trails == 0:
        print("no trail files generated")
    else:
        for i in range(no_of_trails):
            subprocess.run(f"spin -T -t{i + 1} {model}.pml > {model}-{i}.spn",
                           check=True, shell=True)
    os.remove('pan')
    os.chdir(cwd)


@catch_subprocess_errors
def generate_test_files(model, model_dir, testgen, refine_config):
    """Create test files from spin files"""
    cwd = os.getcwd()
    os.chdir(model_dir)
    if not ready_to_generate(model, refine_config):
        sys.exit(1)
    print(f"Generating test files for {model}")
    no_of_trails = len(glob.glob(f"{model}*.trail"))
    if no_of_trails == 0:
        print("no trail files found")
    else:
        for i in range(no_of_trails):
            test_file = f"tr-{model}-{i}{refine_config['testfiletype']}"
            subprocess.run(f"python {testgen} {model} "
                           f"{refine_config['preamble']} "
                           f"{refine_config['postamble']} "
                           f"{refine_config['runfile']} "
                           f"{refine_config['refinefile']} "
                           f"{test_file} {i}",
                           check=True, shell=True)

    generate_testcase_file(model, refine_config, no_of_trails)
    os.chdir(cwd)


def generate_testcase_file(model, refine_config, no_of_trails):
    missing_files = list()
    for key in ["testcase_preamble", "testcase_runfile", "testcase_postamble"]:
        if not Path(refine_config[key]).exists():
            missing_files.append(refine_config[key])

    if not missing_files:
        file_name = f"tc-{model}{refine_config['testfiletype']}"
        with open(file_name, "w") as f:
            preamble = Path(refine_config["testcase_preamble"]).read_text()
            f.write(preamble)
            run = Path(refine_config["testcase_runfile"]).read_text()
            for i in range(no_of_trails):
                f.write(run.format(i))

            postamble = Path(refine_config["testcase_postamble"]).read_text()
            f.write(postamble)
    else:
        for file in missing_files:
            print(f"File not found: {file}")
        print(f"tc-{model}{refine_config['testfiletype']} "
              f"will not be generated")


def copy(model, model_path, codedir, rtems, modfile, testsuite_name,
         test_file_extension):
    """Copies C testfiles to test directory and updates the model file """
    cwd = os.getcwd()
    os.chdir(model_path)

    # Remove old test files
    print(f"Removing old files for model {model}")
    files = glob.glob(f"{codedir}tr-{model}*{test_file_extension}")
    files += glob.glob(f"{codedir}tr-{model}*.h")
    files += glob.glob(f"{codedir}tc-{model}{test_file_extension}")
    for file in files:
        os.remove(file)

    # Copy new test files
    print(f"Copying new files for model {model}")
    files = glob.glob(f"tr-{model}*{test_file_extension}")
    files += glob.glob(f"tr-{model}*.h")
    files += glob.glob(f"tc-{model}{test_file_extension}")
    files += glob.glob(f"../common/tr-{model}{test_file_extension}")
    for file in files:
        shutil.copyfile(file, f"{rtems}testsuites/validation/{file}")

    # Update {testsuite name}.yml
    print(f"Updating {testsuite_name}.yml for model {model}")
    with open(modfile) as file:
        model_yaml = yaml.load(file, Loader=yaml.FullLoader)
    source_list = model_yaml['source']
    source_set = set(source_list)
    files = glob.glob(f"tr-{model}*{test_file_extension}")
    files += glob.glob(f"tc-{model}{test_file_extension}")
    for file in files:
        source_set.add(f"testsuites/validation/{file}")
    new_list = list(source_set)
    model_yaml['source'] = sorted(new_list)
    with open(modfile, 'w') as file:
        yaml.dump(model_yaml, file)
    os.chdir(cwd)


@catch_subprocess_errors
def compile(rtems_dir):
    cwd = os.getcwd()
    os.chdir(rtems_dir)
    subprocess.run("./waf configure", check=True, shell=True)
    subprocess.run("./waf", check=True, shell=True)
    os.chdir(cwd)


@catch_subprocess_errors
def run_simulator(simulator_path, simulator_args, testexe, testsuite):
    sim_command = f"{simulator_path} {simulator_args}"
    print(f"Doing {sim_command} {testexe}")
    subprocess.run(f"{sim_command} {testexe} > {testsuite}-test.log",
                   check=True, shell=True)


def get_generated_files(model, testsuite, test_extension):
    trails = glob.glob(f"{model}*.trail")
    files = trails
    files += glob.glob(f"{model}*.spn")
    files += glob.glob(f"tc-{model}{test_extension}")
    if len(trails) == 1:
        files += glob.glob(f"tr-{model}-0{test_extension}")
    else:
        files += glob.glob(f"tr-{model}-*{test_extension}")
    files += glob.glob(f"{testsuite}-test.log")
    return files


def get_model_paths(config):
    models_file = Path(config["modelsfile"])
    model_to_absolute_path = dict()
    if models_file.exists():
        with open(models_file) as file:
            model_to_relative_path = yaml.load(file, Loader=yaml.FullLoader)
        print(f"GMP.M2RP {model_to_relative_path}")
        for model_path in model_to_relative_path.values():
            print(f"GMP.MP {model_path}")
            relative_path = Path(model_path)
            print(f"GMP.RP {relative_path}")
            absolute_path = Path(models_file.parent / relative_path.parent)
            print(f"GMP.AP {absolute_path}")
            model_name = relative_path.name
            print(f"GMP.MN {model_name}")
            model_to_absolute_path[model_name] = absolute_path
    else:
        print(f"modelsfile not found {models_file}")
        raise SystemExit()

    return model_to_absolute_path


def get_config(source_dir, model_name=""):
    config = dict()
    with open(f"{source_dir}/testbuilder.yml") as file:
        global_config = yaml.load(file, Loader=yaml.FullLoader)
        for key, val in global_config.items():
            config[key] = val
    if model_name and model_name != "allmodels":
        model_to_path = get_model_paths(config)
        print(f"GC.MN {model_name}")
        print(f"GC.M2P {model_to_path}")
        model_path = model_to_path[model_name]
        local_config_path = Path(model_path / "testbuilder.yml")
        if Path(local_config_path).exists():
            with open(local_config_path) as file:
                local_config = yaml.load(file, Loader=yaml.FullLoader)
                if local_config:
                    for key, val in local_config.items():
                        config[key] = val
    if "testsuite" not in config.keys():
        config["testsuite"] = "model-0"
    missing_keys = {
                    "spin2test", "modelsfile", "rtems", "rsb", "simulator",
                    "testyamldir", "testcode", "testexedir", "simulatorargs",
                    "spinallscenarios"
                    } - config.keys()
    if missing_keys:
        print("testbuilder.yml configuration is incomplete")
        print("The following configuration items are missing:")
        for key in missing_keys:
            print(key)
        sys.exit(1)
    config["testyaml"] = f"{config['testyamldir']}{config['testsuite']}.yml"
    config["testexe"] = f"{config['testexedir']}ts-{config['testsuite']}.exe"
    return config


def get_refine_config(source_dir, model, model_dir):
    refine_config = dict()
    with open(f"{source_dir}/refine-config.yml") as file:
        global_config = yaml.load(file, Loader=yaml.FullLoader)
        for key, val in global_config.items():
            refine_config[key] = val
    if Path(f"{model_dir}/refine-config.yml").exists():
        with open(f"{model_dir}/refine-config.yml") as file:
            local_config = yaml.load(file, Loader=yaml.FullLoader)
            if local_config:
                for key, val in local_config.items():
                    refine_config[key] = val
    missing_keys = {
                       "preamble", "postamble", "refinefile", "testfiletype",
                       "runfile", "testcase_preamble", "testcase_postamble",
                       "testcase_runfile"
                    } - refine_config.keys()
    if missing_keys:
        print("refine-config.yml configuration is incomplete")
        print("The following configuration items are missing:")
        for key in missing_keys:
            print(key)
        sys.exit(1)
    for key in ["preamble", "postamble", "refinefile", "runfile"]:
        refine_config[key] = f"{model}{refine_config[key]}"
    for key in ["testcase_preamble", "testcase_postamble", "testcase_runfile"]:
        refine_config[key] = f"tc-{model}{refine_config[key]}"
    return refine_config


def check_models_exist(modelnames, model_to_path, config):
    if modelnames == ["allmodels"]:
        return True
    else:
        all_models_exist = True
        for model in modelnames:
            if model not in model_to_path.keys():
                all_models_exist = False
                print(f"{model} not found in model file")
        if not all_models_exist:
            print(f"\nChoose model(s) from: ")
            for key in model_to_path.keys():
                print(key)
            print(f"\nOr update {config['modelsfile']}")
            raise SystemExit(1)


def main():
    """generates and deploys C tests from Promela models"""
    source_dir = os.path.dirname(os.path.realpath(__file__))
    if not (len(sys.argv) == 2 and sys.argv[1] == "help"
            or len(sys.argv) >= 3 and sys.argv[1] == "allsteps"
            or len(sys.argv) == 3 and sys.argv[1] == "clean"
            or len(sys.argv) == 3 and sys.argv[1] == "archive"
            or 2 <= len(sys.argv) <= 3 and sys.argv[1] == "zero"
            or len(sys.argv) == 3 and sys.argv[1] == "spin"
            or len(sys.argv) == 3 and sys.argv[1] == "gentests"
            or len(sys.argv) == 3 and sys.argv[1] == "copy"
            or len(sys.argv) == 2 and sys.argv[1] == "compile"
            or len(sys.argv) == 2 and sys.argv[1] == "run"):
        with open(f"{source_dir}/testbuilder.help") as helpfile:
            print(helpfile.read())
        sys.exit(1)

    if not Path.exists(Path(f"{source_dir}/spin2test.py")) \
            or not Path.exists(Path(f"{source_dir}/env")):
        print("Setup incomplete...")
        print("Please run the following before continuing:")
        print(f"cd {source_dir} && bash src.sh")
        print(f". {source_dir}/env/bin/activate")
        sys.exit(1)

    config = get_config(source_dir)
    model_to_path = get_model_paths(config)
    refine_config = dict()
    if len(sys.argv) >= 3:
        config = get_config(source_dir, sys.argv[2])
        model_to_path = get_model_paths(config)
        check_models_exist(sys.argv[2::], model_to_path, config)
        if sys.argv[2] != "allmodels":
            refine_config = get_refine_config(source_dir, sys.argv[2],
                                              model_to_path[sys.argv[2]])

    if sys.argv[1] == "help":
        with open(f"{source_dir}/testbuilder.help") as helpfile:
            print(helpfile.read())

    if sys.argv[1] == "allsteps":
        all_steps(sys.argv[2::], model_to_path, source_dir)

    if sys.argv[1] == "spin":
        generate_spin_files(sys.argv[2], model_to_path[sys.argv[2]],
                            config["spinallscenarios"], refine_config)

    if sys.argv[1] == "gentests":
        generate_test_files(sys.argv[2], model_to_path[sys.argv[2]],
                            config["spin2test"], refine_config)

    if sys.argv[1] == "clean":
        print(f"sys.argv clean model_to_path :: {type(model_to_path)}")
        clean(sys.argv[2], model_to_path, source_dir)

    if sys.argv[1] == "archive":
        archive(sys.argv[2], model_to_path[sys.argv[2]], config["testsuite"],
                refine_config["testfiletype"])

    if sys.argv[1] == "zero":
        zero(config["testyaml"], config["testsuite"])

    if sys.argv[1] == "copy":
        copy(sys.argv[2], model_to_path[sys.argv[2]], config["testcode"],
             config["rtems"], config["testyaml"], config["testsuite"],
             refine_config["testfiletype"])

    if sys.argv[1] == "compile":
        compile(config["rtems"])

    if sys.argv[1] == "run":
        run_simulator(config["simulator"], config["simulatorargs"],
                      config["testexe"], config["testsuite"])


if __name__ == '__main__':
    main()
