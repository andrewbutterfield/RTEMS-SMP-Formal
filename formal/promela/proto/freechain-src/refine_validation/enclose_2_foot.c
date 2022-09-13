/* post-amble empty for now */
void RtemsModelChainsAPI_Run1(
)
{
  Context ctx;

  memset( &ctx, 0, sizeof( ctx ) );

  T_set_verbosity( T_NORMAL );

  TestSegment0( &ctx );
}

T_TEST_CASE( RtemsModelChainAPI1 )
{
  RtemsModelChainsAPI_Run1( );
}
