
// Task 0
static void Runner( RtemsModelSemMgr_Context *ctx )
{
  T_log( T_NORMAL, "Runner(Task 0) running" );
  TestSegment3( ctx );
  T_log( T_NORMAL, "Runner(Task 0) finished" );

  // Ensure we hold no semaphores
  ReleaseSema( ctx->runner_sema );
  //ReleaseSema( ctx->worker0_sema );
  //ReleaseSema( ctx->worker1_sema );
}


