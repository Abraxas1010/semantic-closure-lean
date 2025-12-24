// Lean compiler output
// Module: HeytingLean.ClosingTheLoop.Cat.YonedaViewNat
// Imports: Init HeytingLean.ClosingTheLoop.Cat.Selector
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
lean_object* l_Equiv_toIso___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_curryNatIso___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CategoryTheory_CartesianClosed_curry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homTensorLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homTensorLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homTensorLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CategoryTheory_CartesianClosed_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_curryNatIso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CategoryTheory_NatIso_ofComponents___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_curryNatIso___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homTensorLeft___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_3);
x_12 = lean_apply_2(x_10, x_3, x_6);
lean_inc(x_5);
lean_inc(x_3);
x_13 = lean_apply_2(x_10, x_3, x_5);
x_14 = lean_apply_4(x_11, x_3, x_6, x_5, x_7);
x_15 = lean_apply_5(x_9, x_12, x_13, x_4, x_14, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homTensorLeft___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_alloc_closure((void*)(l_HeytingLean_ClosingTheLoop_Cat_homTensorLeft___redArg___lam__0), 8, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, lean_box(0));
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homTensorLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HeytingLean_ClosingTheLoop_Cat_homTensorLeft___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_apply_1(x_10, x_3);
x_12 = lean_apply_5(x_9, x_5, x_4, x_11, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj___redArg___lam__0), 7, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, lean_box(0));
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HeytingLean_ClosingTheLoop_Cat_homSelectorObj(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_curryNatIso___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_CategoryTheory_CartesianClosed_curry), 8, 7);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
lean_closure_set(x_7, 4, x_6);
lean_closure_set(x_7, 5, x_4);
lean_closure_set(x_7, 6, x_5);
x_8 = lean_alloc_closure((void*)(l_CategoryTheory_CartesianClosed_uncurry), 8, 7);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_6);
lean_closure_set(x_8, 5, x_4);
lean_closure_set(x_8, 6, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Equiv_toIso___redArg(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_curryNatIso___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_HeytingLean_ClosingTheLoop_Cat_curryNatIso___redArg___lam__0), 6, 5);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_3);
lean_closure_set(x_6, 4, x_5);
x_7 = l_CategoryTheory_NatIso_ofComponents___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Cat_curryNatIso(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HeytingLean_ClosingTheLoop_Cat_curryNatIso___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HeytingLean_ClosingTheLoop_Cat_Selector(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HeytingLean_ClosingTheLoop_Cat_YonedaViewNat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HeytingLean_ClosingTheLoop_Cat_Selector(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
