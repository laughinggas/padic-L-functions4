// Lean compiler output
// Module: PadicLFunctions4.loc_const_dense
// Imports: Init Mathlib.NumberTheory.Padics.PadicIntegers Mathlib.Topology.ContinuousFunction.Compact Mathlib.Topology.ContinuousFunction.LocallyConstant
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
LEAN_EXPORT lean_object* l_inclusion(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_inclusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_LocallyConstant_toContinuousMap___elambda__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_inclusion___rarg(lean_object*);
LEAN_EXPORT lean_object* l_inclusion___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LocallyConstant_toContinuousMap___elambda__1___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_inclusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_inclusion___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_inclusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_inclusion(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_NumberTheory_Padics_PadicIntegers(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_ContinuousFunction_Compact(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_ContinuousFunction_LocallyConstant(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PadicLFunctions4_loc__const__dense(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_NumberTheory_Padics_PadicIntegers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_ContinuousFunction_Compact(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_ContinuousFunction_LocallyConstant(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
