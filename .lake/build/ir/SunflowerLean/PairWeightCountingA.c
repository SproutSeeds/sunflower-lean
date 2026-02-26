// Lean compiler output
// Module: SunflowerLean.PairWeightCountingA
// Imports: public import Init public import SunflowerLean.BalanceCore
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
LEAN_EXPORT lean_object* l_CandidatesContaining___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_familyIn___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_BadForPair___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pairWeight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_familyOut___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BadForPair___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pairWeight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_familyIn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_ndinter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CandidatesContaining(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BadForPair___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_familyOut___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BadForPair___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pairWeight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CandidatesContaining___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pairWeight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BadForPair(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Finset_powerset___redArg(lean_object*);
uint8_t l_Multiset_decidableMem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_CandidatesContaining___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_familyOut___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_familyOut(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_CandidatesContaining___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Multiset_decidableMem___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_CandidatesContaining___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_CandidatesContaining___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Finset_powerset___redArg(x_2);
x_6 = l_Multiset_filter___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_CandidatesContaining(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_CandidatesContaining___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_CandidatesContaining___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_CandidatesContaining___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_BadForPair___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Multiset_ndinter___redArg(x_1, x_2, x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_6 = l_Multiset_ndinter___redArg(x_1, x_2, x_3);
lean_inc(x_6);
lean_inc_ref(x_1);
x_7 = l_List_decidablePerm___redArg(x_1, x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_inc_ref(x_1);
x_8 = l_Multiset_ndinter___redArg(x_1, x_3, x_4);
x_9 = l_List_decidablePerm___redArg(x_1, x_8, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_BadForPair___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_BadForPair___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
x_7 = l_CandidatesContaining___redArg(x_1, x_2, x_3);
x_8 = l_Multiset_filter___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BadForPair(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_BadForPair___redArg(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BadForPair___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_BadForPair___redArg___lam__0(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BadForPair___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_BadForPair(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_pairWeight___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
lean_inc(x_3);
lean_inc_ref(x_1);
x_7 = l_Multiset_decidableMem___redArg(x_1, x_3, x_5);
if (x_7 == 0)
{
goto block_19;
}
else
{
uint8_t x_20; 
lean_inc(x_6);
lean_inc(x_3);
lean_inc_ref(x_1);
x_20 = l_Multiset_decidableMem___redArg(x_1, x_3, x_6);
if (x_20 == 0)
{
goto block_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_List_lengthTR___redArg(x_2);
x_23 = l_Multiset_ndunion___redArg(x_1, x_5, x_6);
x_24 = l_List_lengthTR___redArg(x_23);
lean_dec(x_23);
x_25 = lean_nat_sub(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
x_26 = lean_nat_pow(x_21, x_25);
lean_dec(x_25);
return x_26;
}
}
block_19:
{
if (x_7 == 0)
{
uint8_t x_8; 
lean_inc(x_6);
lean_inc_ref(x_1);
x_8 = l_Multiset_decidableMem___redArg(x_1, x_3, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_List_lengthTR___redArg(x_2);
x_11 = l_Multiset_ndunion___redArg(x_1, x_5, x_6);
x_12 = l_List_lengthTR___redArg(x_11);
lean_dec(x_11);
x_13 = lean_nat_sub(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_pow(x_9, x_15);
lean_dec(x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_17 = lean_unsigned_to_nat(0u);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_pairWeight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_pairWeight___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_pairWeight___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_pairWeight___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_pairWeight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_pairWeight(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_familyIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_CandidatesContaining___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Multiset_filter___redArg(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_familyIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_familyIn___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_familyOut___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Multiset_decidableMem___redArg(x_1, x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_familyOut___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_familyOut___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Multiset_filter___redArg(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_familyOut(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_familyOut___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_familyOut___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_familyOut___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SunflowerLean_BalanceCore(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SunflowerLean_PairWeightCountingA(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_BalanceCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
