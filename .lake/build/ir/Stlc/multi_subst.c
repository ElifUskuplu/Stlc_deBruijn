// Lean compiler output
// Module: Stlc.multi_subst
// Imports: Init Stlc.basics Stlc.context Stlc.reductions
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
LEAN_EXPORT lean_object* l___private_Stlc_multi__subst_0__Trm_multi__subst_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Trm_add__term___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Stlc_multi__subst_0__Trm_multi__subst_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Trm_multi__subst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Trm_add__term(lean_object*);
LEAN_EXPORT lean_object* l___private_Stlc_multi__subst_0__Trm_context__type_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Trm_context__type(lean_object*, lean_object*);
uint8_t l_Multiset_decidableMem___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Trm_multi__subst___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Stlc_multi__subst_0__Trm_context__type_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Trm_add__term___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Trm_context__type___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Trm_add__term___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Trm_multi__subst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Trm_multi__subst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
case 1:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = l_Trm_multi__subst___closed__1;
lean_inc(x_8);
x_10 = l_Multiset_decidableMem___rarg(x_9, x_8, x_1);
if (x_10 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_11; 
lean_free_object(x_3);
x_11 = lean_apply_1(x_2, x_8);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Trm_multi__subst___closed__1;
lean_inc(x_12);
x_14 = l_Multiset_decidableMem___rarg(x_13, x_12, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_apply_1(x_2, x_12);
return x_16;
}
}
}
case 2:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_3, 1);
x_19 = l_Trm_multi__subst(x_1, x_2, x_18);
lean_ctor_set(x_3, 1, x_19);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = l_Trm_multi__subst(x_1, x_2, x_21);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
default: 
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Trm_multi__subst(x_1, x_2, x_25);
x_28 = l_Trm_multi__subst(x_1, x_2, x_26);
lean_ctor_set(x_3, 1, x_28);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Trm_multi__subst(x_1, x_2, x_29);
x_32 = l_Trm_multi__subst(x_1, x_2, x_30);
x_33 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Stlc_multi__subst_0__Trm_multi__subst_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_4, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_5, x_13, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Stlc_multi__subst_0__Trm_multi__subst_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Stlc_multi__subst_0__Trm_multi__subst_match__1_splitter___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Trm_context__type(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_nat_dec_eq(x_2, x_5);
if (x_7 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
lean_inc(x_6);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Trm_context__type___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Trm_context__type(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Stlc_multi__subst_0__Trm_context__type_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_2(x_3, x_2, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_5(x_4, x_8, x_9, x_7, x_2, lean_box(0));
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Stlc_multi__subst_0__Trm_context__type_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Stlc_multi__subst_0__Trm_context__type_match__1_splitter___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Trm_add__term___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_5, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_apply_1(x_1, x_5);
return x_7;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Trm_add__term(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Trm_add__term___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Trm_add__term___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Trm_add__term___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Trm_add__term___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Trm_add__term(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_basics(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_context(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_reductions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Stlc_multi__subst(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_basics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_context(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_reductions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Trm_multi__subst___closed__1 = _init_l_Trm_multi__subst___closed__1();
lean_mark_persistent(l_Trm_multi__subst___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
