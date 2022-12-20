#

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)

sed \
    -e 's|__auto_type|__auto_type /*@ C_insert begin */ * /*@ end */|' \
    -e '1 i /*@ C_insert begin */typedef int __builtin_va_list;/*@ end */\n/*@ C_insert begin */typedef int __auto_type;/*@ end */\n' \
    -e 's|_Atomic|/*@ C_remove \\<open>_Atomic\\<close> */|' \
    -e 's|\[ \];|[ /*@ C_insert begin */ 1 /*@ end */ ];|' \
    -e 's|events\[\];|events[ /*@ C_insert begin */ 1 /*@ end */ ];|' \
    -e 's|\[ 0 \];|[ /*@ C_replace \\<open>0\\<close> begin */ 1 /*@ end */ ];|' \
    -e 's|_Noreturn|/*@ C_remove \\<open>_Noreturn\\<close> */|' \
    -e 's|_Static_assert\(.*\)|/*@ C_remove \\<open>_Static_assert\1\\<close> */|' \
    "$@"
