// Lean compiler output
// Module: HeytingLean.ClosingTheLoop.Semantics.ProcessBridge
// Imports: Init HeytingLean.ClosingTheLoop.Semantics.KernelLaws HeytingLean.Process.Nucleus
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
LEAN_EXPORT lean_object* l_HeytingLean_ClosingTheLoop_Semantics_ProcessBridge_KprocKernel;
static lean_object* _init_l_HeytingLean_ClosingTheLoop_Semantics_ProcessBridge_KprocKernel() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HeytingLean_ClosingTheLoop_Semantics_KernelLaws(uint8_t builtin, lean_object*);
lean_object* initialize_HeytingLean_Process_Nucleus(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HeytingLean_ClosingTheLoop_Semantics_ProcessBridge(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HeytingLean_ClosingTheLoop_Semantics_KernelLaws(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HeytingLean_Process_Nucleus(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HeytingLean_ClosingTheLoop_Semantics_ProcessBridge_KprocKernel = _init_l_HeytingLean_ClosingTheLoop_Semantics_ProcessBridge_KprocKernel();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
