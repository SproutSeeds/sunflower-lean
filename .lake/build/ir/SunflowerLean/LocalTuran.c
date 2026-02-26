// Lean compiler output
// Module: SunflowerLean.LocalTuran
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Finset.Card public import Mathlib.Data.Nat.Choose.Basic public import Mathlib.Algebra.BigOperators.Group.Finset.Basic public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma public import SunflowerLean.Basic
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
LEAN_EXPORT lean_object* l_coordDegree___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_filter___redArg(lean_object*, lean_object*);
extern lean_object* l_Nat_instAddCancelCommMonoid;
LEAN_EXPORT lean_object* l_totalBlockingCapacity___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coordDegree___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_blockingCapacity(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_blockingCapacity___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Multiset_decidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_coordDegree(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_coordDegree___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_totalBlockingCapacity(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_fast__choose(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_totalBlockingCapacity___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_coordDegree___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Multiset_decidableMem___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_coordDegree___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_coordDegree___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Multiset_filter___redArg(x_4, x_2);
x_6 = l_List_lengthTR___redArg(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_coordDegree(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_coordDegree___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_coordDegree___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_coordDegree___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_blockingCapacity___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_4 = l_coordDegree___redArg(x_1, x_2, x_3);
x_5 = l_List_lengthTR___redArg(x_2);
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Nat_fast__choose(x_4, x_6);
x_8 = lean_nat_sub(x_5, x_4);
lean_dec(x_4);
lean_dec(x_5);
x_9 = lean_nat_mul(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_blockingCapacity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_blockingCapacity___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_totalBlockingCapacity___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_blockingCapacity___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_totalBlockingCapacity___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_totalBlockingCapacity___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Nat_instAddCancelCommMonoid;
x_6 = l_Finset_sum___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_totalBlockingCapacity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_totalBlockingCapacity___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Nat_Choose_Basic(uint8_t builtin);
lean_object* initialize_Mathlib_Algebra_BigOperators_Group_Finset_Basic(uint8_t builtin);
lean_object* initialize_Mathlib_Algebra_BigOperators_Group_Finset_Sigma(uint8_t builtin);
lean_object* initialize_SunflowerLean_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SunflowerLean_LocalTuran(uint8_t builtin) {
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
res = initialize_Mathlib_Data_Nat_Choose_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Group_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Group_Finset_Sigma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
