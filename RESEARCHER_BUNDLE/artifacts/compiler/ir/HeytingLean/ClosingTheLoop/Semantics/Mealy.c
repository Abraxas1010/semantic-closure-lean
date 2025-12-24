// Lean compiler output
// Module: HeytingLean.ClosingTheLoop.Semantics.Mealy
// Imports: Init HeytingLean.ClosingTheLoop.MR.ClosureOperator
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ofMealy(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ofMealy___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_toMealy___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_toMealy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_stepOut(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_stepState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ofMealy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_stepState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_stepOut___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HeytingLean_ClosingTheLoop_MR_closeSelector___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_toMealy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HeytingLean_ClosingTheLoop_Semantics_Mealy_ctorIdx(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_stepState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_stepState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HeytingLean_ClosingTheLoop_Semantics_Mealy_stepState___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_stepOut___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Mealy_stepOut(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HeytingLean_ClosingTheLoop_Semantics_Mealy_stepOut___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ctorIdx(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ofMealy___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ofMealy___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ofMealy___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ofMealy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_ofMealy___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_toMealy___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_toMealy___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_toMealy___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_toMealy(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HeytingLean_ClosingTheLoop_Semantics_Coalgebra_toMealy___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_HeytingLean_ClosingTheLoop_MR_closeSelector___redArg(x_1, x_2, x_3);
lean_inc(x_1);
x_6 = l_HeytingLean_ClosingTheLoop_MR_closeSelector___redArg(x_1, x_2, x_3);
x_7 = lean_apply_1(x_6, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HeytingLean_ClosingTheLoop_Semantics_MRBridge_closeMachine(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HeytingLean_ClosingTheLoop_MR_ClosureOperator(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HeytingLean_ClosingTheLoop_Semantics_Mealy(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HeytingLean_ClosingTheLoop_MR_ClosureOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
