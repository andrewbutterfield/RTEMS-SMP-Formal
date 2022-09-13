#

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)

"$1/Src/modex" -Y "$2"
gcc -E -x c _modex_all.pml | sed 's|active proctype p_\(.*\)(|/*@ modex "\1" */\n&|' > "$3"
