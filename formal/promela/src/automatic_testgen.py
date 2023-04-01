from src.modules.promela_yacc.promela import yacc, ast, lex
import sys
import pathlib


def get_forest_ass00(cons_pair, dest_pair, node, cons_node):
    ts_pred = []
    ts_succ = tl(node)
    ts_res = []
    for tt0 in node:
        t_t = dest_pair(tt0)
        ts_pred0 = list(reversed(ts_pred))
        ts_res = [list(map((lambda msg_t_ass: (
        cons_pair((msg_t_ass[0], t_t[1])), cons_node(ts_pred0 + [cons_pair((msg_t_ass[1], t_t[1])), ] + ts_succ))), get_forest_ass(t_t[0]))), ] + ts_res
        ts_pred = [cons_pair((t_t[0], t_t[1])), ] + ts_pred
        ts_succ = tl(ts_succ)
    return list(flatten(reversed(ts_res)))


def get_forest_ass0(node, cons_node):
    return get_forest_ass00((lambda t_t: t_t[0]), (lambda t_t: (t_t, None)), node, cons_node)


def get_forest_ass0_proc_inl(node, cons_node):
    return list(map((lambda msg_t_ass: ((node.name, msg_t_ass[0]), msg_t_ass[1])), get_forest_ass0([node.body, ], lambda *args, **kwargs: cons_node((lambda node: node[0])(*args, **kwargs)))))


def get_forest_ass(node):
    if type(node) == ast.Assert:
        return [(node, ast.Assert(ast.Unary('!', node.expr), pos=node.pos)),]
    elif type(node) == ast.LTL:
        return [(node, ast.LTL(ast.Unary('!', node.formula), name=node.name)),]
    elif type(node) == ast.Sequence:
        return get_forest_ass0(node, (lambda node0: ast.Sequence(node0, context=node.context, is_option=node.is_option)))
    elif type(node) == ast.Options:
        return get_forest_ass0(node.options, (lambda node0: ast.Options(node.type, node0)))
    elif type(node) == ast.Program:
        return get_forest_ass00((lambda t_t: t_t), (lambda t_t: t_t), node, ast.Program)
    elif isinstance(node, ast.Proctype) and not node.disable_negation:
        return get_forest_ass0_proc_inl(node, (lambda node0: ast.Proctype(node.name, node0, node.args, node.active, node.d_proc, node.priority, node.provided)) if type(node) == ast.Proctype else (lambda node0: ast.Init(node.name, node0, node.args, node.active, node.d_proc, node.priority, node.provided)))
    elif type(node) == ast.InlineDef and not node.disable_negation:
        return get_forest_ass0_proc_inl(node, lambda node0: ast.InlineDef(node.name, node.decl, node0))
    else:
        return []


def tl(l):
    if l:
        _, *l = l
        return l
    else:
        return []


def flatten(l):
    return (x for xs in l for x in xs)


def write_promela_fic(node):
    if type(node) == ast.LTL:
        return [ast.LTL(ast.Unary('!', node.formula), name=node.name)]
    else:
        return list()


def write_file(file_name, program):
    print(f"making file: {file_name}")
    with open(file_name, "w") as f:
        f.write(program.__str__())


def main(args):
    model_file = args[1]
    parser = yacc.Parser(ast, lex.Lexer())
    parsed = parser.parse(None, model_file)
    forest_ass = get_forest_ass(parsed)
    pathlib.Path("_").mkdir(exist_ok=True)
    name_to_num = dict()
    for file in forest_ass:
        if type(file[0][0]) == ast.LTL:
            file_name = f"_/ltl_{file[0][0].name}.pml"
            write_file(file_name, file[1])
        elif type(file[0][0][1]) == ast.Assert:
            if file[0][0][0] not in name_to_num.keys():
                name_to_num[file[0][0][0]] = 0
            else:
                name_to_num[file[0][0][0]] += 1
            file_name = f"_/assert_{file[0][0][0]}_{name_to_num[file[0][0][0]]}.pml"
            write_file(file_name, file[1])


if __name__ == "__main__":
    print(sys.argv)
    main(sys.argv)
