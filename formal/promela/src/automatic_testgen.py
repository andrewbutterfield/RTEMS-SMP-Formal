from src.modules.promela_yacc.promela import yacc, ast, lex
import sys
import pathlib

class NegatedThing:
    def __init__(self, node, negated_expression):
        self.node = node
        self.negated_expression = negated_expression


def get_forest_ass001(node, node_partial_constructor):
    checked_sub_nodes = []
    remaining_sub_nodes = remove_first_element(node)
    nodes_with_negations = []
    for sub_node in node:
        t_t = (sub_node, None)
        my_func = lambda msg_t_ass: (msg_t_ass[0], node_partial_constructor(checked_sub_nodes + [msg_t_ass[1]] + remaining_sub_nodes))
        nodes_with_negations += [my_func(thing) for thing in get_negations_in_node(t_t[0])]
        checked_sub_nodes = checked_sub_nodes + [t_t[0]]
        remaining_sub_nodes = remove_first_element(remaining_sub_nodes)
    return nodes_with_negations


def get_negations_inline_and_proctype(node, node_partial_constructor):
    nodes_with_negation = get_forest_ass001(
                    [node.body],
                    node_partial_constructor
                )
    negations = list()
    for node_with_negation in nodes_with_negation:
        formatted_node = ((node.name, node_with_negation[0]), node_with_negation[1])
        negations.append(formatted_node)
    return negations


def format_assertion_program(negation_in_program, node, checked_nodes, remaining_nodes):
    return (negation_in_program[0], node[1]), \
           ast.Program(checked_nodes
                       + [(negation_in_program[1], node[1])]
                       + remaining_nodes)


def get_all_programs(program: ast.Program):
    checked_nodes = []
    remaining_nodes = remove_first_element(program)
    nodes_with_negations = []
    for node in program:
        nodes_with_negations += [format_assertion_program(negation_in_program, node, checked_nodes, remaining_nodes) for negation_in_program in get_negations_in_node(node[0])]
        checked_nodes = checked_nodes + [(node[0], node[1])]
        remaining_nodes = remove_first_element(remaining_nodes)
    return nodes_with_negations


def get_negations_in_node(node):
    if type(node) == ast.Assert:
        return [(node, ast.Assert(ast.Unary('!', node.expr), pos=node.pos))]
    elif type(node) == ast.LTL:
        return [(node, ast.LTL(ast.Unary('!', node.formula), name=node.name))]
    elif type(node) == ast.Sequence:
        return get_forest_ass001(
            node,
            lambda node0: ast.Sequence(
                node0,
                context=node.context,
                is_option=node.is_option
            )
        )
    elif type(node) == ast.Options:
        return get_forest_ass001(
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
        if type(program[0][0]) == ast.LTL:
            file_name = f"_/ltl_{program[0][0].name}.pml"
            write_file(file_name, program[1])
        elif type(program[0][0][1]) == ast.Assert:
            if program[0][0][0] not in name_to_num.keys():
                name_to_num[program[0][0][0]] = 0
            else:
                name_to_num[program[0][0][0]] += 1
            file_name = f"_/assert_{program[0][0][0]}_{name_to_num[program[0][0][0]]}.pml"
            write_file(file_name, program[1])


if __name__ == "__main__":
    print(sys.argv)
    main(sys.argv)
