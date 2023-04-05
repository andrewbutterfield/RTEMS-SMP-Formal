from src.modules.promela_yacc.promela import yacc, ast, lex
import sys
import pathlib
import filecmp
from dataclasses import dataclass
from typing import Union, List, Any


@dataclass
class ProgramWithNegations:
    expression: Union[ast.Assert, ast.LTL]
    node: Union[ast.InlineDef, ast.Proctype, ast.TypeDef,
                ast.Sequence, ast.LTL, ast.Assert]
    name: str = ""
    program: ast.Program = None


def format_negations_top_level_nodes(
        negations_in_node: List[ProgramWithNegations],
        node_partial_constructor, checked_sub_nodes,
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


def format_assertions_program(negation_in_program: ProgramWithNegations,
                              line_number: int, checked_nodes: list,
                              remaining_nodes: list) -> ProgramWithNegations:
    negation_in_program.program = ast.Program(checked_nodes
                                   + [(negation_in_program.node, line_number)]
                                   + remaining_nodes)
    return negation_in_program


def get_all_programs(program: ast.Program) -> List[ProgramWithNegations]:
    checked_nodes = []
    remaining_nodes = remove_first_element(program)
    nodes_with_negations = []
    for node in program:
        for node_with_negation in get_negations_in_node(node[0]):
            nodes_with_negations.append(format_assertions_program(node_with_negation, node[1],
                                                              checked_nodes, remaining_nodes))
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


def main(args):
    model_file = args[1]
    parser = yacc.Parser(ast, lex.Lexer())
    parsed = parser.parse(None, model_file)
    all_programs = get_all_programs(parsed)
    pathlib.Path("_").mkdir(exist_ok=True)
    name_to_num = dict()
    for program in all_programs:
        if type(program.expression) == ast.LTL:
            file_name = f"_/ltl_{program.name}.pml"
            write_file(file_name, program.program)
        elif type(program.expression) == ast.Assert:
            if program.name not in name_to_num.keys():
                name_to_num[program.name] = 0
            else:
                name_to_num[program.name] += 1
            file_name = f"_/assert_{program.name}_{name_to_num[program.name]}.pml"
            write_file(file_name, program.program)


if __name__ == "__main__":
    print(sys.argv)
    main(sys.argv)

