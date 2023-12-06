// Lean compiler output
// Module: PadicLFunctions4.ZModProp
// Imports: Init Mathlib.RingTheory.WittVector.Compare Mathlib.Data.Opposite
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
lean_object* l_ZMod_commRing(lean_object*);
lean_object* l_ZMod_fintype(lean_object*, lean_object*);
lean_object* l_Semiring_toMonoidWithZero___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ZMod_units__fintype(lean_object*);
extern lean_object* l_UnitsInt_fintype;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instTopologicalSpaceZMod___boxed(lean_object*);
static lean_object* l_instTopologicalSpaceZMod___closed__1;
lean_object* l_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_TopologicalSpace_instCompleteLatticeTopologicalSpace(lean_object*);
LEAN_EXPORT lean_object* l_instTopologicalSpaceZMod(lean_object*);
lean_object* l_instFintypeUnits___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_instTopologicalSpaceZMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_TopologicalSpace_instCompleteLatticeTopologicalSpace(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instTopologicalSpaceZMod(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instTopologicalSpaceZMod___closed__1;
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instTopologicalSpaceZMod___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instTopologicalSpaceZMod(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ZMod_units__fintype(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_4 = l_ZMod_commRing(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Semiring_toMonoidWithZero___rarg(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_ZMod_fintype(x_1, lean_box(0));
x_9 = lean_alloc_closure((void*)(l_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_instFintypeUnits___rarg(x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_UnitsInt_fintype;
return x_11;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_RingTheory_WittVector_Compare(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Opposite(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PadicLFunctions4_ZModProp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_RingTheory_WittVector_Compare(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Opposite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instTopologicalSpaceZMod___closed__1 = _init_l_instTopologicalSpaceZMod___closed__1();
lean_mark_persistent(l_instTopologicalSpaceZMod___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
