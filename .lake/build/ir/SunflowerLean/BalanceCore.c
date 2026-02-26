// Lean compiler output
// Module: SunflowerLean.BalanceCore
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Finset.Card public import Mathlib.Data.Finset.Powerset public import Mathlib.Data.Finset.SDiff public import Mathlib.Data.Rat.Defs public import Mathlib.Tactic public import SunflowerLean.Basic public import SunflowerLean.LocalTuran public import SunflowerLean.Slice
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
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_freq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_coordDegree___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_cast___at___00Tactic_NormNum_evalRealSqrt_spec__4(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ratOfNat(lean_object*);
LEAN_EXPORT lean_object* l_freq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ratOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_cast___at___00Tactic_NormNum_evalRealSqrt_spec__4(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_freq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_4 = l_coordDegree___redArg(x_1, x_2, x_3);
x_5 = l_Nat_cast___at___00Tactic_NormNum_evalRealSqrt_spec__4(x_4);
x_6 = l_List_lengthTR___redArg(x_2);
lean_dec(x_2);
x_7 = l_Nat_cast___at___00Tactic_NormNum_evalRealSqrt_spec__4(x_6);
x_8 = l_Rat_div(x_5, x_7);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_freq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_freq___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Powerset(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_SDiff(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Rat_Defs(uint8_t builtin);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_SunflowerLean_Basic(uint8_t builtin);
lean_object* initialize_SunflowerLean_LocalTuran(uint8_t builtin);
lean_object* initialize_SunflowerLean_Slice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SunflowerLean_BalanceCore(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Powerset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_SDiff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Rat_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_LocalTuran(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
