# SPDX-License-Identifier: BSD-2-Clause
# Runs SPIN to generate test code for all defined scenarios

# Copyright (C) 2023 Trinity College Dublin (www.tcd.ie)
#               James Gooding Hunt
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

from src.modules.promela_yacc.promela import yacc, ast, lex
import glob
import os
import sys
import yaml
import shutil
import subprocess
from dataclasses import dataclass
from typing import Union, List
from pathlib import Path
from datetime import datetime

import testbuilder


@dataclass
class ProgramWithNegations:
    expression: Union[ast.Assert, ast.LTL]
    node: Union[ast.InlineDef, ast.Proctype, ast.TypeDef, ast.Init,
                ast.Sequence, ast.LTL, ast.Assert]
    name: str = ""
    program: ast.Program = None


def format_negations_top_level_nodes(
        negations_in_node: List[ProgramWithNegations],
        node_partial_constructor: callable, checked_sub_nodes,
        remaining_sub_nodes) -> List[ProgramWithNegations]:
    negations_formatted = list()
    for negation in negations_in_node:
        negation.node = node_partial_constructor(checked_sub_nodes +
                                                 [negation.node] +
                                                 remaining_sub_nodes)
        negations_formatted.append(negation)
    return negations_formatted


def get_negations_top_level_node(node, node_partial_constructor) -> List[ProgramWithNegations]:
    checked_sub_nodes = []
    remaining_sub_nodes = remove_first_element(node)
    nodes_with_negations = []
    for sub_node in node:
        negations_in_sub_node = get_negations_in_node(sub_node)
        nodes_with_negations += format_negations_top_level_nodes(negations_in_sub_node, node_partial_constructor, checked_sub_nodes, remaining_sub_nodes)
        checked_sub_nodes.append(sub_node)
        remaining_sub_nodes = remove_first_element(remaining_sub_nodes)
    return nodes_with_negations


def get_negations_inline_and_proctype(node: Union[ast.InlineDef, ast.Proctype, ast.Init],
                                      node_partial_constructor) -> List[ProgramWithNegations]:
    nodes_with_negation = get_negations_top_level_node(
                    [node.body],
                    node_partial_constructor
                )
    negations = list()
    for node_with_negation in nodes_with_negation:
        node_with_negation.name = node.name
        negations.append(node_with_negation)
    return negations


def format_assertions_program(negations_in_program: List[ProgramWithNegations],
                              line_number: int, checked_nodes: list,
                              remaining_nodes: list) -> List[ProgramWithNegations]:
    return_val = list()
    for negation_in_program in negations_in_program:
        negation_in_program.program = ast.Program(checked_nodes
                                       + [(negation_in_program.node, line_number)]
                                       + remaining_nodes)
        return_val.append(negation_in_program)
    return return_val


def get_all_programs(program: ast.Program) -> List[ProgramWithNegations]:
    checked_nodes = []
    remaining_nodes = remove_first_element(program)
    nodes_with_negations = []
    for node in program:
        nodes = get_negations_in_node(node[0])
        nodes_with_negations += format_assertions_program(nodes, node[1],
                                                          checked_nodes, remaining_nodes)
        checked_nodes.append(node)
        remaining_nodes = remove_first_element(remaining_nodes)
    return nodes_with_negations


def get_negations_in_node(node) -> List[ProgramWithNegations]:
    if type(node) == ast.Assert:
        expression = ast.Assert(ast.Unary('!', node.expr))
        return [ProgramWithNegations(expression=expression, node=expression)]
    elif type(node) == ast.LTL:
        expression = ast.LTL(ast.Unary('!', node.formula), node.name)
        return [ProgramWithNegations(expression, name=node.name,
                                     node=expression)]
    elif type(node) == ast.Sequence:
        return get_negations_top_level_node(
            node,
            lambda node0: ast.Sequence(
                node0,
                context=node.context,
                is_option=node.is_option
            )
        )
    elif type(node) == ast.Options:
        return get_negations_top_level_node(
            node.options,
            lambda node0: ast.Options(
                node.type,
                node0
            )
        )
    elif isinstance(node, ast.Init) and not node.disable_negation:
        return get_negations_inline_and_proctype(
            node,
            lambda node0: ast.Init(
                node.name,
                node0[0],
                node.args,
                node.active,
                node.d_proc,
                node.priority,
                node.provided
            )
        )
    elif isinstance(node, ast.Proctype) and not node.disable_negation:
        return get_negations_inline_and_proctype(
            node,
            lambda node0: ast.Proctype(
                node.name,
                node0[0],
                node.args,
                node.active,
                node.d_proc,
                node.priority,
                node.provided
            )
        )
    elif type(node) == ast.InlineDef and not node.disable_negation:
        return get_negations_inline_and_proctype(
            node,
            lambda node0: ast.InlineDef(
                node.name,
                node.decl,
                node0[0]
            )
        )
    else:
        return []


def remove_first_element(elements: list):
    if elements:
        return elements[1::]
    else:
        return []


def flatten(iterator_of_items):
    for items in iterator_of_items:
        for item in items:
            yield item


def write_file(file_name, program):
    print(f"making file: {file_name}")
    with open(file_name, "w") as f:
        f.write(program.__str__())


def get_config(source_dir, model_dir=""):
    config = dict()
    required_keys = {"disable_negation_at", "max_trails", "spin_assert",
                     "spin_ltl"}
    with open(f"{source_dir}/automatic-testgen.yml") as file:
        global_config = yaml.load(file, Loader=yaml.FullLoader)
        for key, val in global_config.items():
            config[key] = val
    if model_dir:
        local_config_path = Path(f"{model_dir}/automatic-testgen.yml")
        if local_config_path.exists():
            with open(local_config_path) as file:
                local_config = yaml.load(file, Loader=yaml.FullLoader)
                if local_config:
                    for key, val in local_config.items():
                        config[key] = val
    missing_keys = required_keys - config.keys()
    if missing_keys:
        print("automatic-testgen.yml configuration is incomplete")
        print("The following configuration items are missing:")
        for key in missing_keys:
            print(key)
        sys.exit(1)
    return config


def get_generated_pml_files() -> List[str]:
    generated_pml_files = glob.glob("assert*.pml")
    generated_pml_files += glob.glob("ltl*.pml")
    return generated_pml_files


def get_generated_files() -> List[str]:
    generated_files = get_generated_pml_files()

    trails = glob.glob(f"*.trail")
    generated_files += trails
    generated_files += glob.glob(f"*.spn")
    generated_files += glob.glob(f"tc-*.c")
    if len(trails) == 1:
        generated_files += glob.glob(f"tr-*-0.c")
    else:
        generated_files += glob.glob(f"tr-*-*.c")
    generated_files += glob.glob(f"*-test.log")
    return generated_files


def get_programs(model_name):
    parser = yacc.Parser(ast, lex.Lexer())
    parsed = parser.parse(None, f"{model_name}.pml")
    return get_all_programs(parsed)


def write_all_programs(config, all_programs: List[ProgramWithNegations]):
    name_to_num = dict()
    for program in all_programs:
        if program.name not in config["disable_negation_at"]:
            if type(program.expression) == ast.LTL:
                file_name = f"ltl_{program.name}.pml"
                write_file(file_name, program.program)
            elif type(program.expression) == ast.Assert:
                if program.name not in name_to_num.keys():
                    name_to_num[program.name] = 0
                else:
                    name_to_num[program.name] += 1
                file_name = f"assert_{program.name}_{name_to_num[program.name]}.pml"
                write_file(file_name, program.program)


def generate_pml_files(config, model_name, model_dir):
    cwd = os.getcwd()
    os.chdir(model_dir)
    programs = get_programs(model_name)
    write_all_programs(config, programs)
    os.chdir(cwd)


def generate_spin_files(model_dir, config, refine_config):
    cwd = os.getcwd()
    os.chdir(model_dir)
    pml_files = get_generated_pml_files()
    for pml_file in pml_files:
        if pml_file.startswith("assert"):
            spinallscenarios = config["spin_assert"]
        elif pml_file.startswith("ltl"):
            ltl_name = pml_file.lstrip("ltl_").rstrip(".pml")
            spinallscenarios = f"{config['spin_assert']}{ltl_name}"
        pml_name = pml_file.rstrip(".pml")
        testbuilder.generate_spin_files(pml_name, os.getcwd(),
                                        spinallscenarios, refine_config)
    os.chdir(cwd)


@testbuilder.catch_subprocess_errors
def generate_test_files(model_name, model_dir,
                        testbuilder_config, refine_config):
    """Create test files from spin files"""
    cwd = os.getcwd()
    os.chdir(model_dir)
    if not testbuilder.ready_to_generate(model_name, refine_config):
        sys.exit(1)
    print(f"Generating test files for {model_name}")
    for pml_file in get_generated_pml_files():
        pml_name = pml_file.rstrip(".pml")
        no_of_trails = len(glob.glob(f"{pml_name}*.trail"))
        if no_of_trails == 0:
            print("no trail files found")
        elif no_of_trails == 1:
            test_file = f"tr-{pml_name}{refine_config['testfiletype']}"
            subprocess.run(
                f"python {testbuilder_config['spin2test']} "
                f"{pml_name} {refine_config['preamble']} "
                f"{refine_config['postamble']} "
                f"{refine_config['runfile']} "
                f"{refine_config['refinefile']} "
                f"{test_file}",
                check=True, shell=True)
        else:
            for i in range(no_of_trails):
                test_file = f"tr-{pml_name}-{i}{refine_config['testfiletype']}"
                subprocess.run(f"python {testbuilder_config['spin2test']} "
                               f"{pml_name} "
                               f"{refine_config['preamble']} "
                               f"{refine_config['postamble']} "
                               f"{refine_config['runfile']} "
                               f"{refine_config['refinefile']} "
                               f"{test_file} {i}",
                               check=True, shell=True)
    os.chdir(cwd)


def clean(model_name, model_dir):
    """Cleans out generated files in current directory"""
    print(f"Removing spin and test files for {model_name}")
    cwd = os.getcwd()
    os.chdir(model_dir)
    files = get_generated_files()
    for file in files:
        os.remove(file)
    os.chdir(cwd)


def archive(model_name, model_dir):
    """Archives generated files in current directory"""
    cwd = os.getcwd()
    os.chdir(model_dir)
    print(f"Archiving spin and test files for {model_name}")
    files = get_generated_files()
    date = datetime.now().strftime("%Y%m%d-%H%M%S")
    archive_dir = Path(f"archive/{date}")
    archive_dir.mkdir(parents=True, exist_ok=True)
    for file in files:
        shutil.copy2(file, archive_dir)
    print(f"Files archived to {archive_dir}")
    os.chdir(cwd)


def copy(model_dir, testbuilder_config):
    """Copies C testfiles to test directory and updates the model file """
    for pml_file in get_generated_pml_files():
        pml_name = pml_file.rstrip(".pml")
        testbuilder.copy(pml_name, model_dir, testbuilder_config["testcode"],
                         testbuilder_config["rtems"],
                         testbuilder_config["testyaml"],
                         testbuilder_config["testsuite"])


def main(args):
    """generates and deploys C tests from Promela models"""
    source_dir = os.path.dirname(os.path.realpath(__file__))
    if not (len(args) == 2 and args[1] == "help"
            or len(args) == 3 and args[1] == "clean"
            or len(args) == 3 and args[1] == "archive"
            or len(args) == 3 and args[1] == "genpmls"
            or len(args) == 3 and args[1] == "spin"
            or len(args) == 3 and args[1] == "gentests"
            or len(args) == 3 and args[1] == "copy"):
        with open(f"{source_dir}/automatic-testgen.help") as helpfile:
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
    testbuilder_config = testbuilder.get_config(source_dir)
    model_to_path = testbuilder.get_model_paths(testbuilder_config)
    refine_config = dict()
    command = args[1]
    model_name = ""
    if len(args) == 3:
        model_name = args[2]
        config = get_config(source_dir, model_to_path[model_name])
        testbuilder.check_models_exist([model_name], model_to_path,
                                       testbuilder_config)
        refine_config = testbuilder.get_refine_config(source_dir, model_name,
                                                      model_to_path[model_name])

    if command == "help":
        with open(f"{source_dir}/automatic_testgen.help") as helpfile:
            print(helpfile.read())

    if command == "genpmls":
        generate_pml_files(config, model_name, model_to_path[model_name])

    if command == "spin":
        generate_spin_files(model_to_path[model_name], config,
                            refine_config)

    if command == "gentests":
        generate_test_files(model_name, model_to_path[model_name],
                            testbuilder_config, refine_config)

    if command == "clean":
        clean(args[2], model_to_path[args[2]])

    if command == "archive":
        archive(model_name, model_to_path[model_name])

    if command == "copy":
        copy(model_to_path[model_name], testbuilder_config)


if __name__ == "__main__":
    main(sys.argv)

