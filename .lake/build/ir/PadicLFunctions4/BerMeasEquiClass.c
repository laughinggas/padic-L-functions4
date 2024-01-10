// Lean compiler output
// Module: PadicLFunctions4.BerMeasEquiClass
// Imports: Init PadicLFunctions4.padic_int_clopen PadicLFunctions4.padic_integral PadicLFunctions4.BerMeasEventuallyConstant PadicLFunctions4.BerMeasBerDist
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
LEAN_EXPORT lean_object* l_equi__class_equi__iso__Fin___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ZMod_commRing(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_equi__class_equi__iso__Fin___elambda__1___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ZMod_x27(lean_object*, lean_object*);
lean_object* l_ZMod_fintype(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ZMod_x27___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_equi__class_equi__iso__Fin___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_equi__class_equi__iso__Fin___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_equi__class_equi__iso__Fin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_equi__class_equi__iso__Fin___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_equi__class_equi__iso__Fin___elambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ZMod_val(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ZMod_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ZMod_fintype(x_1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_ZMod_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ZMod_x27(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_equi__class_equi__iso__Fin___elambda__1___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_3, x_5);
x_7 = lean_nat_pow(x_1, x_6);
lean_dec(x_6);
x_8 = lean_nat_mul(x_2, x_7);
lean_dec(x_7);
x_9 = l_ZMod_commRing(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_1(x_11, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_equi__class_equi__iso__Fin___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_nat_pow(x_1, x_3);
x_7 = lean_nat_mul(x_2, x_6);
x_8 = l_ZMod_val(x_7, x_4);
lean_dec(x_4);
lean_dec(x_7);
x_9 = lean_nat_mul(x_5, x_2);
x_10 = lean_nat_mul(x_9, x_6);
lean_dec(x_6);
lean_dec(x_9);
x_11 = lean_nat_add(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
x_12 = l_Nat_cast___at_equi__class_equi__iso__Fin___elambda__1___spec__1(x_1, x_2, x_3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_equi__class_equi__iso__Fin___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
x_8 = lean_nat_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_nat_mul(x_2, x_8);
lean_dec(x_8);
x_10 = l_ZMod_val(x_9, x_5);
lean_dec(x_9);
x_11 = lean_nat_pow(x_1, x_3);
x_12 = lean_nat_mul(x_2, x_11);
lean_dec(x_11);
x_13 = l_ZMod_val(x_12, x_4);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_15 = lean_nat_div(x_14, x_12);
lean_dec(x_12);
lean_dec(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_equi__class_equi__iso__Fin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_equi__class_equi__iso__Fin___elambda__2___boxed), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
x_8 = lean_alloc_closure((void*)(l_equi__class_equi__iso__Fin___elambda__1___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_5);
lean_closure_set(x_8, 3, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_equi__class_equi__iso__Fin___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_cast___at_equi__class_equi__iso__Fin___elambda__1___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_equi__class_equi__iso__Fin___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_equi__class_equi__iso__Fin___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_equi__class_equi__iso__Fin___elambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_equi__class_equi__iso__Fin___elambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_PadicLFunctions4_padic__int__clopen(uint8_t builtin, lean_object*);
lean_object* initialize_PadicLFunctions4_padic__integral(uint8_t builtin, lean_object*);
lean_object* initialize_PadicLFunctions4_BerMeasEventuallyConstant(uint8_t builtin, lean_object*);
lean_object* initialize_PadicLFunctions4_BerMeasBerDist(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PadicLFunctions4_BerMeasEquiClass(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PadicLFunctions4_padic__int__clopen(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PadicLFunctions4_padic__integral(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PadicLFunctions4_BerMeasEventuallyConstant(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PadicLFunctions4_BerMeasBerDist(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
