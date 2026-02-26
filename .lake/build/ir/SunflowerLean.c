// Lean compiler output
// Module: SunflowerLean
// Imports: public import Init public import SunflowerLean.Basic public import SunflowerLean.Slice public import SunflowerLean.Recurrence public import SunflowerLean.Spread public import SunflowerLean.LocalTuran public import SunflowerLean.BalanceCore public import SunflowerLean.PairWeight public import SunflowerLean.UnionBounds public import SunflowerLean.SpreadBalance public import SunflowerLean.Container public import SunflowerLean.SmallCases public import SunflowerLean.SATNative public import SunflowerLean.SATBridge public import SunflowerLean.SATUpperBound public import SunflowerLean.ErdosProblem20
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SunflowerLean_Basic(uint8_t builtin);
lean_object* initialize_SunflowerLean_Slice(uint8_t builtin);
lean_object* initialize_SunflowerLean_Recurrence(uint8_t builtin);
lean_object* initialize_SunflowerLean_Spread(uint8_t builtin);
lean_object* initialize_SunflowerLean_LocalTuran(uint8_t builtin);
lean_object* initialize_SunflowerLean_BalanceCore(uint8_t builtin);
lean_object* initialize_SunflowerLean_PairWeight(uint8_t builtin);
lean_object* initialize_SunflowerLean_UnionBounds(uint8_t builtin);
lean_object* initialize_SunflowerLean_SpreadBalance(uint8_t builtin);
lean_object* initialize_SunflowerLean_Container(uint8_t builtin);
lean_object* initialize_SunflowerLean_SmallCases(uint8_t builtin);
lean_object* initialize_SunflowerLean_SATNative(uint8_t builtin);
lean_object* initialize_SunflowerLean_SATBridge(uint8_t builtin);
lean_object* initialize_SunflowerLean_SATUpperBound(uint8_t builtin);
lean_object* initialize_SunflowerLean_ErdosProblem20(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SunflowerLean(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_Recurrence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_Spread(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_LocalTuran(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_BalanceCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_PairWeight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_UnionBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_SpreadBalance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_Container(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_SmallCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_SATNative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_SATBridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_SATUpperBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_ErdosProblem20(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
