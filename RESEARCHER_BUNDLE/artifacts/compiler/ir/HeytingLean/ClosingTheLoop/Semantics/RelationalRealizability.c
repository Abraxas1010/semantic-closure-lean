// Lean compiler output
// Module: HeytingLean.ClosingTheLoop.Semantics.RelationalRealizability
// Imports: Init Mathlib.Data.Set.Lattice HeytingLean.ClosingTheLoop.Semantics.KernelLaws HeytingLean.ClosingTheLoop.Semantics.Mealy HeytingLean.ClosingTheLoop.Semantics.LambdaIRBridge HeytingLean.ClosingTheLoop.Semantics.ProcessBridge HeytingLean.Process.Semantics
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
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_Instances_processSystem;
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_ReachSystem_kernel(lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_ReachSystem_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_ReachSystem_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_ReachSystem_kernel(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_HeytingLean_ClosingTheLoop_Semantics_Instances_processSystem() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Set_Lattice(uint8_t builtin, lean_object*);
lean_object* initialize_HeytingLean_ClosingTheLoop_Semantics_KernelLaws(uint8_t builtin, lean_object*);
lean_object* initialize_HeytingLean_ClosingTheLoop_Semantics_Mealy(uint8_t builtin, lean_object*);
lean_object* initialize_HeytingLean_ClosingTheLoop_Semantics_LambdaIRBridge(uint8_t builtin, lean_object*);
lean_object* initialize_HeytingLean_ClosingTheLoop_Semantics_ProcessBridge(uint8_t builtin, lean_object*);
lean_object* initialize_HeytingLean_Process_Semantics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HeytingLean_ClosingTheLoop_Semantics_RelationalRealizability(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Set_Lattice(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HeytingLean_ClosingTheLoop_Semantics_KernelLaws(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HeytingLean_ClosingTheLoop_Semantics_Mealy(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HeytingLean_ClosingTheLoop_Semantics_LambdaIRBridge(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HeytingLean_ClosingTheLoop_Semantics_ProcessBridge(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HeytingLean_Process_Semantics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HeytingLean_ClosingTheLoop_Semantics_Instances_processSystem = _init_l_HeytingLean_ClosingTheLoop_Semantics_Instances_processSystem();
lean_mark_persistent(l_HeytingLean_ClosingTheLoop_Semantics_Instances_processSystem);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
