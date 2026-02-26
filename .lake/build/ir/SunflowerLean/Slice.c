// Lean compiler output
// Module: SunflowerLean.Slice
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Finset.Lattice.Fold public import Mathlib.Data.Finset.SDiff public import Mathlib.Tactic public import SunflowerLean.Basic
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
LEAN_EXPORT lean_object* l_SunflowerLean_sliceReduce(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_coDegree___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_sliceReduce___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_SunflowerLean_sliceReduce___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_sliceReduce___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_coDegree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_slice___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_sliceReduce___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_sub___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_sliceReduce___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_SunflowerLean_sliceReduce___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_pairSlice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_slice(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_tSlice___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_pairSlice___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SunflowerLean_tSlice(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Finset_instDecidableRelSubset___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_SunflowerLean_sliceReduce___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_decidablePerm___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_sliceReduce___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Multiset_sub___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_SunflowerLean_sliceReduce___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Finset_instDecidableRelSubset___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_sliceReduce___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_SunflowerLean_sliceReduce___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_3);
lean_inc_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_SunflowerLean_sliceReduce___redArg___lam__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l_SunflowerLean_sliceReduce___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
x_7 = l_Multiset_filter___redArg(x_6, x_2);
x_8 = l_Finset_image___redArg(x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_sliceReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_SunflowerLean_sliceReduce___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_sliceReduce___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_SunflowerLean_sliceReduce___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_sliceReduce___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_SunflowerLean_sliceReduce___redArg___lam__2(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_slice___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_SunflowerLean_sliceReduce___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Multiset_filter___redArg(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_slice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_SunflowerLean_slice___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_tSlice___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_SunflowerLean_sliceReduce___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_tSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_SunflowerLean_sliceReduce___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_pairSlice___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_inc_ref(x_1);
x_7 = l_Multiset_ndinsert___redArg(x_1, x_3, x_6);
x_8 = l_SunflowerLean_sliceReduce___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_pairSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc_ref(x_2);
x_8 = l_Multiset_ndinsert___redArg(x_2, x_4, x_7);
x_9 = l_SunflowerLean_sliceReduce___redArg(x_2, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_coDegree___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_inc_ref(x_1);
x_7 = l_Multiset_ndinsert___redArg(x_1, x_3, x_6);
x_8 = l_SunflowerLean_sliceReduce___redArg(x_1, x_2, x_7);
x_9 = l_List_lengthTR___redArg(x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_SunflowerLean_coDegree(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_SunflowerLean_coDegree___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Lattice_Fold(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_SDiff(uint8_t builtin);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_SunflowerLean_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SunflowerLean_Slice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Lattice_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_SDiff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin);
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
