// Lean compiler output
// Module: Theorem.example_separate.Ico_pow_choose_eq_pow_add_pow
// Imports: Init Theorem.example_separate.add_div_two Theorem.example_separate.Ico_pow_mul_choose Theorem.example_separate.Ico_choose_eq_Ico_choose_add Theorem.example_separate.Ico_choose_add_eq_mul_pred Theorem.example_separate.pred_Ico_choose Theorem.example_separate.pred_Ico_choose_eq_pred_pow
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
lean_object* initialize_Theorem_example__separate_add__div__two(uint8_t builtin, lean_object*);
lean_object* initialize_Theorem_example__separate_Ico__pow__mul__choose(uint8_t builtin, lean_object*);
lean_object* initialize_Theorem_example__separate_Ico__choose__eq__Ico__choose__add(uint8_t builtin, lean_object*);
lean_object* initialize_Theorem_example__separate_Ico__choose__add__eq__mul__pred(uint8_t builtin, lean_object*);
lean_object* initialize_Theorem_example__separate_pred__Ico__choose(uint8_t builtin, lean_object*);
lean_object* initialize_Theorem_example__separate_pred__Ico__choose__eq__pred__pow(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Theorem_example__separate_Ico__pow__choose__eq__pow__add__pow(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Theorem_example__separate_add__div__two(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Theorem_example__separate_Ico__pow__mul__choose(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Theorem_example__separate_Ico__choose__eq__Ico__choose__add(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Theorem_example__separate_Ico__choose__add__eq__mul__pred(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Theorem_example__separate_pred__Ico__choose(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Theorem_example__separate_pred__Ico__choose__eq__pred__pow(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
