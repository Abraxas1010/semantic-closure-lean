// Lean compiler output
// Module: HeytingLean.ClosingTheLoop.Cat.Selector
// Imports: Init Mathlib.CategoryTheory.Closed.Cartesian
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
lean_object* l_CategoryTheory_ihom_ev___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_evalAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_SelectorObj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_SelectorObj___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_evalAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_SelectorObj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_SelectorObj___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_SelectorObj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_1(x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_SelectorObj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HeytingLean_ClosingTheLoop_Cat_SelectorObj(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_evalAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 6);
lean_inc_ref(x_15);
lean_dec_ref(x_8);
lean_inc(x_11);
lean_inc(x_4);
x_16 = lean_apply_1(x_11, x_4);
lean_inc(x_16);
x_17 = lean_apply_1(x_15, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_12);
lean_inc(x_16);
lean_inc(x_14);
x_19 = lean_apply_2(x_12, x_14, x_16);
lean_inc(x_16);
lean_inc(x_3);
x_20 = lean_apply_2(x_12, x_3, x_16);
lean_inc(x_16);
x_21 = lean_apply_1(x_9, x_16);
lean_inc_n(x_16, 2);
x_22 = lean_apply_6(x_13, x_14, x_3, x_16, x_16, x_6, x_21);
x_23 = l_CategoryTheory_ihom_ev___redArg(x_5);
lean_dec_ref(x_5);
lean_inc(x_4);
x_24 = lean_apply_1(x_23, x_4);
lean_inc(x_10);
lean_inc(x_4);
lean_inc(x_19);
x_25 = lean_apply_5(x_10, x_19, x_20, x_4, x_22, x_24);
x_26 = lean_apply_5(x_10, x_16, x_19, x_4, x_18, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_evalAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_HeytingLean_ClosingTheLoop_Cat_evalAt___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_CategoryTheory_Closed_Cartesian(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HeytingLean_ClosingTheLoop_Cat_Selector(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_CategoryTheory_Closed_Cartesian(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
