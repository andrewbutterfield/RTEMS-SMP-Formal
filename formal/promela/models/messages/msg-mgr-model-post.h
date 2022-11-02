
static void Runner( RtemsModelMessageMgr_Context *ctx )
{
  T_log( T_NORMAL, "Runner running" );
  TestSegment3( ctx );
  T_log( T_NORMAL, "Runner finished" );
}
