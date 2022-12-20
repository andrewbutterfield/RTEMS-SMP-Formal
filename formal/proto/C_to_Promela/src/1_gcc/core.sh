#

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)

pat="$1"
file="$2"
args="$({ grep "$pat" "$file" || test $? -eq 141 ; } | grep -m 1 '\-c' | cut -d ' ' -f 3- || { err=$?; echo "Matching failed: \"$pat\" \"$file\"" >&2; exit $err; })" # SIGPIPE = 141

function python3_gcc {
    python3 - "$1" "$args" <<EOF || { err=$?; echo -e "Matching succeeded: \"$pat\" \"$file\"\npython3_gcc failed: \"$1\" \"$args\"" >&2; exit $err; }
import ast
import os
import sys

def flatten (l): return (x for xs in l for x in xs)

if sys.argv[1] == '' or sys.argv[2] == '':
    sys.exit (f'Empty arguments: "{sys.argv[1]}" "{sys.argv[2]}"')

try:
    argv1 = ast.literal_eval(sys.argv[1])
    argv2 = ast.literal_eval(sys.argv[2])
except ValueError:
    sys.exit (f'Value error: "{sys.argv[1]}" "{sys.argv[2]}"')
except SyntaxError:
    sys.exit (f'Syntax error: "{sys.argv[1]}" "{sys.argv[2]}"')

if type (argv1) != list or type (argv2) != list or len (argv2) <= 1:
    sys.exit (f'Wrong type of arguments: "{sys.argv[1]}" "{sys.argv[2]}"')

args = list (flatten (map (lambda x: argv1 if x[0:2] == '-o' else [x], argv2)))

os.execv (args[0], args)
EOF
}
