// Lean compiler output
// Module: SunflowerLean.BalanceCasesA
// Imports: public import Init public import SunflowerLean.UnionBounds
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
LEAN_EXPORT lean_object* l_pairWeightAvoiding___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BadForPairAvoiding___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pairWeightAvoiding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pairWeightAvoiding(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_CandidatesAvoiding___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_ndinter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pairWeightAvoiding___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CandidatesAvoiding___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_InFamilyAvoiding___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BadForPairAvoiding(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_InFamilyAvoiding___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_InFamilyAvoiding___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CandidatesAvoiding(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Finset_powerset___redArg(lean_object*);
uint8_t l_Multiset_decidableMem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_InFamilyAvoiding___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_InFamilyAvoiding___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BadForPairAvoiding___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_CandidatesAvoiding___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BadForPairAvoiding___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BadForPairAvoiding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_InFamilyAvoiding(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_CandidatesAvoiding___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_CandidatesAvoiding___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_CandidatesAvoiding___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Finset_powerset___redArg(x_2);
x_6 = l_Multiset_filter___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_CandidatesAvoiding(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_CandidatesAvoiding___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_CandidatesAvoiding___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_CandidatesAvoiding___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_BadForPairAvoiding___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_BadForPairAvoiding___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_BadForPairAvoiding___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
x_7 = l_CandidatesAvoiding___redArg(x_1, x_2, x_3);
x_8 = l_Multiset_filter___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BadForPairAvoiding(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_BadForPairAvoiding___redArg(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_BadForPairAvoiding___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_BadForPairAvoiding___redArg___lam__0(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BadForPairAvoiding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_BadForPairAvoiding(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_pairWeightAvoiding___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
lean_inc(x_3);
lean_inc_ref(x_1);
x_14 = l_Multiset_decidableMem___redArg(x_1, x_3, x_5);
if (x_14 == 0)
{
goto block_24;
}
else
{
uint8_t x_25; 
lean_inc(x_6);
lean_inc(x_3);
lean_inc_ref(x_1);
x_25 = l_Multiset_decidableMem___redArg(x_1, x_3, x_6);
if (x_25 == 0)
{
goto block_24;
}
else
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_26 = lean_unsigned_to_nat(0u);
return x_26;
}
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_List_lengthTR___redArg(x_2);
x_9 = l_Multiset_ndunion___redArg(x_1, x_5, x_6);
x_10 = l_List_lengthTR___redArg(x_9);
lean_dec(x_9);
x_11 = lean_nat_sub(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
x_12 = lean_nat_pow(x_7, x_11);
lean_dec(x_11);
return x_12;
}
block_24:
{
if (x_14 == 0)
{
uint8_t x_15; 
lean_inc(x_6);
lean_inc_ref(x_1);
x_15 = l_Multiset_decidableMem___redArg(x_1, x_3, x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_List_lengthTR___redArg(x_2);
x_18 = l_Multiset_ndunion___redArg(x_1, x_5, x_6);
x_19 = l_List_lengthTR___redArg(x_18);
lean_dec(x_18);
x_20 = lean_nat_sub(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_23 = lean_nat_pow(x_16, x_22);
lean_dec(x_22);
return x_23;
}
else
{
goto block_13;
}
}
else
{
lean_dec(x_3);
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_pairWeightAvoiding(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_pairWeightAvoiding___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_pairWeightAvoiding___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_pairWeightAvoiding___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_pairWeightAvoiding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_pairWeightAvoiding(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_InFamilyAvoiding___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_decidablePerm___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_InFamilyAvoiding___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Multiset_decidableMem___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_InFamilyAvoiding___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_InFamilyAvoiding___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_InFamilyAvoiding___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
x_7 = l_CandidatesAvoiding___redArg(x_1, x_3, x_4);
x_8 = l_Multiset_filter___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_InFamilyAvoiding(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_InFamilyAvoiding___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_InFamilyAvoiding___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_InFamilyAvoiding___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_InFamilyAvoiding___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_InFamilyAvoiding___redArg___lam__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SunflowerLean_UnionBounds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SunflowerLean_BalanceCasesA(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SunflowerLean_UnionBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
