// Lean compiler output
// Module: HeytingLean.ClosingTheLoop.Cat.ClosureOperator
// Imports: Init HeytingLean.ClosingTheLoop.Cat.InverseEvaluation
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
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_close(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_close___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HeytingLean_ClosingTheLoop_Cat_evalAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_close___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_inc(x_4);
x_11 = lean_apply_1(x_10, x_4);
lean_inc(x_4);
x_12 = l_HeytingLean_ClosingTheLoop_Cat_evalAt___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_inc(x_11);
x_13 = lean_apply_5(x_9, x_11, x_4, x_11, x_12, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_close(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_HeytingLean_ClosingTheLoop_Cat_close___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HeytingLean_ClosingTheLoop_Cat_InverseEvaluation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HeytingLean_ClosingTheLoop_Cat_ClosureOperator(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HeytingLean_ClosingTheLoop_Cat_InverseEvaluation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
