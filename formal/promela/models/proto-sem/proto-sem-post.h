/* SPDX-License-Identifier: BSD-2-Clause */

static void Runner( RtemsModelProtoSem_Context *ctx )
{
  T_log( T_NORMAL, "Runner running" );
  TestSegment4( ctx );
  T_log( T_NORMAL, "Runner finished" );
}
