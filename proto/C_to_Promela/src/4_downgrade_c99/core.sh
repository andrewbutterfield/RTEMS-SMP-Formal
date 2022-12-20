#

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)

perl -0777 -pe \
    's|{.   .}|{\n   /*@ C_insert begin */int zzzzzzzzzzzzzzzzzzz;/*@ end */\n}|s' \
    "$@"
