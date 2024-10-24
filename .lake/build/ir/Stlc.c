// Lean compiler output
// Module: Stlc
// Imports: Init Stlc.basics Stlc.call_by_value Stlc.confluence Stlc.context Stlc.multi_subst Stlc.normalization Stlc.open_close Stlc.reductions Stlc.typing
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_basics(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_call__by__value(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_confluence(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_context(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_multi__subst(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_normalization(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_open__close(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_reductions(uint8_t builtin, lean_object*);
lean_object* initialize_Stlc_typing(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Stlc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_basics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_call__by__value(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_confluence(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_context(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_multi__subst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_normalization(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_open__close(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_reductions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Stlc_typing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
