/* =============================================== */


const char rtems_test_name[] = "Chain_AutoGen";
// @@@ 0 NAME Chain_AutoGen
// @@@ 0 DEF MAX_SIZE 8
#define MAX_SIZE 8
// @@@ 0 DECL Node memory[MAX_SIZE]
item memory[MAX_SIZE] ;
// @@@ 0 DECL unsigned nptr NULL
// @@@ 0 DECL Control chain
rtems_chain_control chain ;

/* ===== TEST CODE SEGMENT 0 =====*/

void TestSegment0(void);
void TestSegment0(void) {
  item * nptr = NULL ;
  T_log(T_NORMAL,"@@@ 0 INIT");
  rtems_chain_initialize_empty(&chain);

#define str(s) #s
#define app(str, s) str(s)
#define xstr(s) app(str, s)
#define xT_eq_ptr(a, e) T_eq_ptr(a, e)
