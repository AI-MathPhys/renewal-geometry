// Lean compiler output
// Module: NCG.Grand.StinespringDilationExact
// Imports: public import Init public meta import Init public import Mathlib public import NCG.Grand.RelEntropyInvarianceExact public import NCG.Grand.PetzSufficiencyExact
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
lean_object* lp_mathlib_Equiv_refl(lean_object*);
extern lean_object* lp_mathlib_Complex_instMul;
extern lean_object* lp_mathlib_Complex_instAddCommMonoid;
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
lean_object* lp_mathlib_Matrix_conjTranspose___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineCol___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_DependencyProbe_NCG_Petz_stineCol___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_DependencyProbe_NCG_Petz_stineCol___redArg___closed__0;
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineCol___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineCol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_DependencyProbe_NCG_Petz_stineConj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Complex_instStarRing___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___closed__0 = (const lean_object*)&lp_DependencyProbe_NCG_Petz_stineConj___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_envTrace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_envTrace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_envTrace___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_DependencyProbe_NCG_Petz_envTrace___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_DependencyProbe_NCG_Petz_envTrace___redArg___closed__0;
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_envTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_envTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineCol___redArg___lam__0(lean_object* v_K_1_, lean_object* v_p_2_, lean_object* v_j_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v___x_6_; 
v_fst_4_ = lean_ctor_get(v_p_2_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v_p_2_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_p_2_);
v___x_6_ = lean_apply_3(v_K_1_, v_fst_4_, v_snd_5_, v_j_3_);
return v___x_6_;
}
}
static lean_object* _init_lp_DependencyProbe_NCG_Petz_stineCol___redArg___closed__0(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineCol___redArg(lean_object* v_K_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; lean_object* v_toFun_12_; lean_object* v___f_13_; lean_object* v___x_14_; 
v___x_11_ = lean_obj_once(&lp_DependencyProbe_NCG_Petz_stineCol___redArg___closed__0, &lp_DependencyProbe_NCG_Petz_stineCol___redArg___closed__0_once, _init_lp_DependencyProbe_NCG_Petz_stineCol___redArg___closed__0);
v_toFun_12_ = lean_ctor_get(v___x_11_, 0);
v___f_13_ = lean_alloc_closure((void*)(lp_DependencyProbe_NCG_Petz_stineCol___redArg___lam__0), 3, 1);
lean_closure_set(v___f_13_, 0, v_K_8_);
lean_inc(v_toFun_12_);
v___x_14_ = lean_apply_3(v_toFun_12_, v___f_13_, v_a_9_, v_a_10_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineCol(lean_object* v_n_15_, lean_object* v_m_16_, lean_object* v_00_u03ba_17_, lean_object* v_K_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_DependencyProbe_NCG_Petz_stineCol___redArg(v_K_18_, v_a_19_, v_a_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__0(lean_object* v_K_22_, lean_object* v_a_23_, lean_object* v_j_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_DependencyProbe_NCG_Petz_stineCol___redArg(v_K_22_, v_a_23_, v_j_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__1(lean_object* v_00_u03c1_26_, lean_object* v_j_27_, lean_object* v_j_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_apply_2(v_00_u03c1_26_, v_j_28_, v_j_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__2(lean_object* v_00_u03c1_30_, lean_object* v_inst_31_, lean_object* v___x_32_, lean_object* v___x_33_, lean_object* v___f_34_, lean_object* v_j_35_){
_start:
{
lean_object* v___f_36_; lean_object* v___x_37_; 
v___f_36_ = lean_alloc_closure((void*)(lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__1), 3, 2);
lean_closure_set(v___f_36_, 0, v_00_u03c1_30_);
lean_closure_set(v___f_36_, 1, v_j_35_);
v___x_37_ = lp_mathlib_dotProduct___redArg(v_inst_31_, v___x_32_, v___x_33_, v___f_34_, v___f_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__2___boxed(lean_object* v_00_u03c1_38_, lean_object* v_inst_39_, lean_object* v___x_40_, lean_object* v___x_41_, lean_object* v___f_42_, lean_object* v_j_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__2(v_00_u03c1_38_, v_inst_39_, v___x_40_, v___x_41_, v___f_42_, v_j_43_);
lean_dec_ref(v___x_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__3(lean_object* v___f_45_, lean_object* v___x_46_, lean_object* v_a_47_, lean_object* v_j_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lp_mathlib_Matrix_conjTranspose___redArg(v___f_45_, v___x_46_, v_j_48_, v_a_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj___redArg(lean_object* v_inst_51_, lean_object* v_K_52_, lean_object* v_00_u03c1_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___f_59_; lean_object* v___f_60_; lean_object* v___x_61_; lean_object* v___f_62_; lean_object* v___x_63_; 
lean_inc_ref(v_K_52_);
v___f_56_ = lean_alloc_closure((void*)(lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__0), 3, 2);
lean_closure_set(v___f_56_, 0, v_K_52_);
lean_closure_set(v___f_56_, 1, v_a_54_);
v___x_57_ = lp_mathlib_Complex_instMul;
v___x_58_ = lp_mathlib_Complex_instAddCommMonoid;
lean_inc(v_inst_51_);
v___f_59_ = lean_alloc_closure((void*)(lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_59_, 0, v_00_u03c1_53_);
lean_closure_set(v___f_59_, 1, v_inst_51_);
lean_closure_set(v___f_59_, 2, v___x_57_);
lean_closure_set(v___f_59_, 3, v___x_58_);
lean_closure_set(v___f_59_, 4, v___f_56_);
v___f_60_ = ((lean_object*)(lp_DependencyProbe_NCG_Petz_stineConj___redArg___closed__0));
v___x_61_ = lean_alloc_closure((void*)(lp_DependencyProbe_NCG_Petz_stineCol), 6, 4);
lean_closure_set(v___x_61_, 0, lean_box(0));
lean_closure_set(v___x_61_, 1, lean_box(0));
lean_closure_set(v___x_61_, 2, lean_box(0));
lean_closure_set(v___x_61_, 3, v_K_52_);
v___f_62_ = lean_alloc_closure((void*)(lp_DependencyProbe_NCG_Petz_stineConj___redArg___lam__3), 4, 3);
lean_closure_set(v___f_62_, 0, v___f_60_);
lean_closure_set(v___f_62_, 1, v___x_61_);
lean_closure_set(v___f_62_, 2, v_a_55_);
v___x_63_ = lp_mathlib_dotProduct___redArg(v_inst_51_, v___x_57_, v___x_58_, v___f_59_, v___f_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_stineConj(lean_object* v_n_64_, lean_object* v_m_65_, lean_object* v_00_u03ba_66_, lean_object* v_inst_67_, lean_object* v_K_68_, lean_object* v_00_u03c1_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lp_DependencyProbe_NCG_Petz_stineConj___redArg(v_inst_67_, v_K_68_, v_00_u03c1_69_, v_a_70_, v_a_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_envTrace___redArg___lam__0(lean_object* v_a_73_, lean_object* v_b_74_, lean_object* v_X_75_, lean_object* v_i_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
lean_inc(v_i_76_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v_i_76_);
lean_ctor_set(v___x_77_, 1, v_a_73_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v_i_76_);
lean_ctor_set(v___x_78_, 1, v_b_74_);
v___x_79_ = lean_apply_2(v_X_75_, v___x_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_envTrace___redArg___lam__1(lean_object* v_X_80_, lean_object* v___x_81_, lean_object* v_inst_82_, lean_object* v_a_83_, lean_object* v_b_84_){
_start:
{
lean_object* v___f_85_; lean_object* v___x_86_; 
v___f_85_ = lean_alloc_closure((void*)(lp_DependencyProbe_NCG_Petz_envTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_85_, 0, v_a_83_);
lean_closure_set(v___f_85_, 1, v_b_84_);
lean_closure_set(v___f_85_, 2, v_X_80_);
v___x_86_ = lp_mathlib_Finset_sum___redArg(v___x_81_, v_inst_82_, v___f_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_envTrace___redArg___lam__1___boxed(lean_object* v_X_87_, lean_object* v___x_88_, lean_object* v_inst_89_, lean_object* v_a_90_, lean_object* v_b_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lp_DependencyProbe_NCG_Petz_envTrace___redArg___lam__1(v_X_87_, v___x_88_, v_inst_89_, v_a_90_, v_b_91_);
lean_dec_ref(v___x_88_);
return v_res_92_;
}
}
static lean_object* _init_lp_DependencyProbe_NCG_Petz_envTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_envTrace___redArg(lean_object* v_inst_94_, lean_object* v_X_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_toFun_100_; lean_object* v___f_101_; lean_object* v___x_102_; 
v___x_98_ = lp_mathlib_Complex_instAddCommMonoid;
v___x_99_ = lean_obj_once(&lp_DependencyProbe_NCG_Petz_envTrace___redArg___closed__0, &lp_DependencyProbe_NCG_Petz_envTrace___redArg___closed__0_once, _init_lp_DependencyProbe_NCG_Petz_envTrace___redArg___closed__0);
v_toFun_100_ = lean_ctor_get(v___x_99_, 0);
v___f_101_ = lean_alloc_closure((void*)(lp_DependencyProbe_NCG_Petz_envTrace___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_101_, 0, v_X_95_);
lean_closure_set(v___f_101_, 1, v___x_98_);
lean_closure_set(v___f_101_, 2, v_inst_94_);
lean_inc(v_toFun_100_);
v___x_102_ = lean_apply_3(v_toFun_100_, v___f_101_, v_a_96_, v_a_97_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_DependencyProbe_NCG_Petz_envTrace(lean_object* v_m_103_, lean_object* v_00_u03ba_104_, lean_object* v_inst_105_, lean_object* v_X_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lp_DependencyProbe_NCG_Petz_envTrace___redArg(v_inst_105_, v_X_106_, v_a_107_, v_a_108_);
return v___x_109_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_DependencyProbe_NCG_Grand_RelEntropyInvarianceExact(uint8_t builtin);
lean_object* initialize_DependencyProbe_NCG_Grand_PetzSufficiencyExact(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_DependencyProbe_NCG_Grand_StinespringDilationExact(uint8_t builtin) {
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
res = initialize_DependencyProbe_NCG_Grand_RelEntropyInvarianceExact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DependencyProbe_NCG_Grand_PetzSufficiencyExact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
