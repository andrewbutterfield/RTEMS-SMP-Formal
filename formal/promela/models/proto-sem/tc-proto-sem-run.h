
/**
 * @fn void T_case_body_RtemsEventValSendReceive( void )
 */
T_TEST_CASE( RtemsModelProtoSem{0} )
{{
  RtemsModelProtoSem_Run{0}(
    EventSend,
    EventReceive,
    GetPendingEvents,
    THREAD_WAIT_CLASS_EVENT,
    STATES_WAITING_FOR_EVENT
  );
}}

/**
 * @fn void T_case_body_RtemsEventValSystemSendReceive( void )
 */
T_TEST_CASE( RtemsModelSystemProtoSem{0} )
{{
  RtemsModelProtoSem_Run{0}(
    EventSystemSend,
    EventSystemReceive,
    GetPendingSystemEvents,
    THREAD_WAIT_CLASS_SYSTEM_EVENT,
    STATES_WAITING_FOR_SYSTEM_EVENT
  );
}}