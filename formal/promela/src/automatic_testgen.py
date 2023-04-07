from src.modules.promela_yacc.promela import yacc, ast, lex
import sys
import pathlib
import filecmp
import yaml
from dataclasses import dataclass
from typing import Union, List, Any
from pathlib import Path


@dataclass
class ProgramWithNegations:
    expression: Union[ast.Assert, ast.LTL]
    node: Union[ast.InlineDef, ast.Proctype, ast.TypeDef,
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


def get_negations_inline_and_proctype(node: Union[ast.InlineDef, ast.Proctype],
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


def get_config(source_dir):
    config = dict()
    required_keys = {"disable_negation_at", "max_trails", "spin_assert",
                     "spin_ltl"}
    with open(f"{source_dir}/automatic_tesgen.yml") as file:
        global_config = yaml.load(file, Loader=yaml.FullLoader)
        for key, val in global_config.items():
            config[key] = val
    if Path("automatic_tesgen.yml").exists():
        with open("automatic_tesgen.yml") as file:
            local_config = yaml.load(file, Loader=yaml.FullLoader)
            if local_config:
                for key, val in local_config.items():
                    config[key] = val
    missing_keys = required_keys - config.keys()
    if missing_keys:
        print("automatic_tesgen.yml configuration is incomplete")
        print("The following configuration items are missing:")
        for key in missing_keys:
            print(key)
        sys.exit(1)


def get_programs(model_file):
    parser = yacc.Parser(ast, lex.Lexer())
    parsed = parser.parse(None, model_file)
    return get_all_programs(parsed)


def write_all_programs(all_programs: List[ProgramWithNegations]):
    pathlib.Path("_").mkdir(exist_ok=True)
    name_to_num = dict()
    for program in all_programs:
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


def main(args):
    model_file = args[1]
    programs = get_programs(model_file)
    write_all_programs(programs)


if __name__ == "__main__":
    print(sys.argv)
    main(sys.argv)

