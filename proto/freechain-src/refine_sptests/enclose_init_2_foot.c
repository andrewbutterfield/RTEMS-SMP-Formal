}

T_TEST_CASE(Chain_AutoGen) {
  TestSegment0();
}

static void Init(rtems_task_argument arg)
{
   T_run_initialize(&config);
   T_register();
   T_run_by_name("Chain_AutoGen");
}

/* =============================================== */
