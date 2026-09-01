// Lean compiler output
// Module: NCG.Grand.HSMatrixizationExact
// Imports: public import Init public meta import Init public import Mathlib public import NCG.Grand.GeoMeanOrderExact
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
static lean_once_cell_t lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__0;
static lean_once_cell_t lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__1;
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_QRE_vecOne___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_QRE_vecOne(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_2_ = lp_mathlib_Complex_ofReal(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_4_ = lp_mathlib_Complex_ofReal(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_QRE_vecOne___redArg(lean_object* v_inst_5_, lean_object* v_q_6_){
_start:
{
lean_object* v_fst_7_; lean_object* v_snd_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_fst_7_ = lean_ctor_get(v_q_6_, 0);
lean_inc(v_fst_7_);
v_snd_8_ = lean_ctor_get(v_q_6_, 1);
lean_inc(v_snd_8_);
lean_dec_ref(v_q_6_);
v___x_9_ = lean_apply_2(v_inst_5_, v_fst_7_, v_snd_8_);
v___x_10_ = lean_unbox(v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__0, &lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__0_once, _init_lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__0);
return v___x_11_;
}
else
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__1, &lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__1_once, _init_lp_DependencyProbe_NCG_QRE_vecOne___redArg___closed__1);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_QRE_vecOne(lean_object* v_n_13_, lean_object* v_inst_14_, lean_object* v_q_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_DependencyProbe_NCG_QRE_vecOne___redArg(v_inst_14_, v_q_15_);
return v___x_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_DependencyProbe_NCG_Grand_GeoMeanOrderExact(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_DependencyProbe_NCG_Grand_HSMatrixizationExact(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DependencyProbe_NCG_Grand_GeoMeanOrderExact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
