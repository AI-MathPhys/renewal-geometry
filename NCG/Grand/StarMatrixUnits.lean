/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.FiniteStarSubalgebraMutualCommutant

/-!
# Star-compatible matrix units for a finite star subalgebra
  (`thm:commutant-decomposition` star bridge,
  Gran-Tensor manuscript)

The remaining bridge of the commutant-decomposition record:
from a system of (non-self-adjoint) Artin–Wedderburn matrix
units of a star-closed subalgebra `S` of a matrix algebra,
construct the **self-adjoint central projection family and
star-compatible matrix units inside `S`**.

* `kaplansky_projection`: for every idempotent `e ∈ S`
  there is a self-adjoint projection `p ∈ S` with
  `p e = e`, `e p = p`, and `p = e w` for some `w ∈ S` —
  the Kaplansky formula `p = e e* z⁻¹`,
  `z = 1 + (e − e*)(e* − e)`, with `z⁻¹ ∈ S` because a
  finite-dimensional subalgebra absorbs inverses.
* `ordered_orthogonalization`: any finite family of
  pairwise-orthogonal idempotents of `S` summing to `1`
  admits a family of pairwise-orthogonal self-adjoint
  projections of `S` summing to `1`, each equivalent to
  its idempotent (`p e' = e'`, `e' p = p`, `p ∈ e' S` for
  the successively compressed idempotents `e'`).
* `star_matrix_units`: from an Artin–Wedderburn unit
  system (multiplication relations and spanning), `S`
  carries a full star-compatible unit system: self-adjoint
  central block projections summing to `1` and partial
  isometries `f_{αβ} = v_α v_β*` with
  `f_{αβ}* = f_{βα}`, `f_{αβ} f_{γδ} = δ_{βγ} f_{αδ}`,
  and `∑_α f_{αα}` the block projection.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace StarUnits

variable {n : Type} [Fintype n] [DecidableEq n]
variable (S : Subalgebra ℂ (Matrix n n ℂ))

/-- A finite-dimensional subalgebra absorbs inverses: if
`z ∈ S` is invertible in the matrix algebra, its inverse
lies in `S`. -/
theorem inv_mem_of_isUnit {z : Matrix n n ℂ} (hz : z ∈ S)
    (hzu : IsUnit z) :
    ∃ y ∈ S, z * y = 1 ∧ y * z = 1 := by
  classical
  have hL : Function.Injective
      (fun x : S => (⟨z, hz⟩ : S) * x) := by
    intro x x' hxx
    have hval : z * (x : Matrix n n ℂ) = z * (x' : Matrix n n ℂ) := by
      have := congrArg Subtype.val hxx
      exact this
    have := hzu.mul_left_cancel hval
    exact Subtype.ext this
  have hLlin : ∃ L : S →ₗ[ℂ] S,
      ∀ x, L x = (⟨z, hz⟩ : S) * x :=
    ⟨{ toFun := fun x => (⟨z, hz⟩ : S) * x
       map_add' := fun x y => mul_add _ x y
       map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        exact mul_smul_comm c _ x },
      fun x => rfl⟩
  obtain ⟨L, hLdef⟩ := hLlin
  have hLinj : Function.Injective L := by
    intro x x' h
    apply hL
    beta_reduce
    rw [← hLdef, ← hLdef]
    exact h
  have hLsurj : Function.Surjective L :=
    LinearMap.injective_iff_surjective.mp hLinj
  obtain ⟨y, hy⟩ := hLsurj 1
  rw [hLdef] at hy
  have hy1 : z * (y : Matrix n n ℂ) = 1 := by
    have := congrArg Subtype.val hy
    exact this
  refine ⟨y, y.2, hy1, ?_⟩
  have h2 : z * ((y : Matrix n n ℂ) * z - 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hy1,
      Matrix.one_mul, Matrix.mul_one, sub_self]
  have := hzu.mul_left_cancel
    (h2.trans (Matrix.mul_zero z).symm)
  rw [sub_eq_zero] at this
  exact this

/-- **Kaplansky projection formula**: every idempotent of a
star-closed finite-dimensional subalgebra is equivalent to
a self-adjoint projection of the subalgebra, lying in its
principal right ideal. -/
theorem kaplansky_projection
    (hstar : ∀ a ∈ S, aᴴ ∈ S)
    {e : Matrix n n ℂ} (he : e ∈ S) (hidem : e * e = e) :
    ∃ p w : Matrix n n ℂ, p ∈ S ∧ w ∈ S ∧ p = e * w
      ∧ pᴴ = p ∧ p * p = p ∧ p * e = e ∧ e * p = p := by
  classical
  have hidemH : eᴴ * eᴴ = eᴴ := by
    have := congrArg conjTranspose hidem
    rwa [Matrix.conjTranspose_mul] at this
  set a : Matrix n n ℂ := e - eᴴ with ha
  set z : Matrix n n ℂ := 1 + a * aᴴ with hzdef
  have haH : aᴴ = -a := by
    rw [ha, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    abel
  have hzS : z ∈ S := by
    have haS : a ∈ S := S.sub_mem he (hstar e he)
    have haHS : aᴴ ∈ S := hstar a haS
    exact S.add_mem (S.one_mem) (S.mul_mem haS haHS)
  have hzPD : z.PosDef := by
    rw [hzdef]
    exact Matrix.PosDef.add_posSemidef Matrix.PosDef.one
      (Matrix.posSemidef_self_mul_conjTranspose a)
  have hzu : IsUnit z := hzPD.isUnit
  have hzH : zᴴ = z := by
    rw [hzdef, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have ha2 : a * a = e - e * eᴴ - eᴴ * e + eᴴ := by
    rw [ha, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      hidem, hidemH]
    abel
  have hz2 : z = 1 - a * a := by
    rw [hzdef, haH, Matrix.mul_neg]
    abel
  have hez : e * z = e * eᴴ * e := by
    have h1 : e * (e * eᴴ) = e * eᴴ := by
      rw [← Matrix.mul_assoc, hidem]
    have h2 : e * (eᴴ * e) = e * eᴴ * e := by
      rw [Matrix.mul_assoc]
    rw [hz2, Matrix.mul_sub, Matrix.mul_one, ha2,
      Matrix.mul_add, Matrix.mul_sub, Matrix.mul_sub,
      hidem, h1, h2]
    abel
  have hze : z * e = e * eᴴ * e := by
    have h4 : eᴴ * e * e = eᴴ * e := by
      rw [Matrix.mul_assoc, hidem]
    rw [hz2, Matrix.sub_mul, Matrix.one_mul, ha2,
      Matrix.add_mul, Matrix.sub_mul, Matrix.sub_mul,
      hidem, h4]
    abel
  obtain ⟨y, hyS, hzy, hyz⟩ := inv_mem_of_isUnit S hzS hzu
  have hyH : yᴴ = y := by
    have h1 : yᴴ * z = 1 := by
      have := congrArg conjTranspose hzy
      rwa [Matrix.conjTranspose_mul, hzH,
        Matrix.conjTranspose_one] at this
    calc yᴴ = yᴴ * (z * y) := by
          rw [hzy, Matrix.mul_one]
      _ = (yᴴ * z) * y := by rw [Matrix.mul_assoc]
      _ = y := by rw [h1, Matrix.one_mul]
  have hey : e * y = y * e := by
    calc e * y = (y * z) * e * y := by
          rw [hyz, Matrix.one_mul]
      _ = y * (z * e) * y := by
          simp only [Matrix.mul_assoc]
      _ = y * (e * z) * y := by rw [hze, hez]
      _ = y * e * (z * y) := by
          simp only [Matrix.mul_assoc]
      _ = y * e := by rw [hzy, Matrix.mul_one]
  have heHz : eᴴ * z = eᴴ * e * eᴴ := by
    have := congrArg conjTranspose hze
    rwa [Matrix.conjTranspose_mul, hzH,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc] at this
  have hzeH : z * eᴴ = eᴴ * e * eᴴ := by
    have := congrArg conjTranspose hez
    rwa [Matrix.conjTranspose_mul, hzH,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc] at this
  have heHy : eᴴ * y = y * eᴴ := by
    calc eᴴ * y = (y * z) * eᴴ * y := by
          rw [hyz, Matrix.one_mul]
      _ = y * (z * eᴴ) * y := by
          simp only [Matrix.mul_assoc]
      _ = y * (eᴴ * z) * y := by rw [hzeH, heHz]
      _ = y * eᴴ * (z * y) := by
          simp only [Matrix.mul_assoc]
      _ = y * eᴴ := by rw [hzy, Matrix.mul_one]
  have hpH : (e * eᴴ * y)ᴴ = e * eᴴ * y := by
    have h1 : (e * eᴴ * y)ᴴ = y * (e * eᴴ) := by
      rw [Matrix.conjTranspose_mul, hyH,
        Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    rw [h1, ← Matrix.mul_assoc, ← hey, Matrix.mul_assoc,
      ← heHy, ← Matrix.mul_assoc]
  have hpe : (e * eᴴ * y) * e = e := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hey,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hez,
      Matrix.mul_assoc, hzy, Matrix.mul_one]
  have hep : e * (e * eᴴ * y) = e * eᴴ * y := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hidem]
  have hpp : (e * eᴴ * y) * (e * eᴴ * y) = e * eᴴ * y := by
    calc (e * eᴴ * y) * (e * eᴴ * y)
        = ((e * eᴴ * y) * e) * (eᴴ * y) := by
          simp only [Matrix.mul_assoc]
      _ = e * (eᴴ * y) := by rw [hpe]
      _ = e * eᴴ * y := by rw [Matrix.mul_assoc]
  exact ⟨e * eᴴ * y, eᴴ * y,
    S.mul_mem (S.mul_mem he (hstar e he)) hyS,
    S.mul_mem (hstar e he) hyS,
    Matrix.mul_assoc e eᴴ y, hpH, hpp, hpe, hep⟩

section Orthogonalization

variable {N : ℕ} (g : Fin N → Matrix n n ℂ)

/-- The successively compressed idempotent at slot `j`. -/
noncomputable def compIdem (p : Fin N → Matrix n n ℂ)
    (j : Fin N) : Matrix n n ℂ :=
  (1 - ∑ i ∈ Finset.univ.filter (fun i => i < j), p i) * g j

/-- The per-slot data package of the orthogonalization. -/
def SlotData (p : Fin N → Matrix n n ℂ) (j : Fin N) : Prop :=
  p j ∈ S ∧ (p j)ᴴ = p j ∧ p j * p j = p j
    ∧ (∃ w ∈ S, p j = compIdem g p j * w)
    ∧ p j * compIdem g p j = compIdem g p j
    ∧ compIdem g p j * p j = p j

/-- The kill invariant: original idempotents annihilate all
strictly earlier constructed projections on the left. -/
private theorem kill_lemma
    (horth : ∀ j k, j ≠ k → g j * g k = 0)
    (p : Fin N → Matrix n n ℂ) {k : ℕ}
    (hdata : ∀ j : Fin N, j.val < k → SlotData S g p j) :
    ∀ (jv : ℕ) (j : Fin N), j.val = jv → j.val < k →
      ∀ m : Fin N, j < m → g m * p j = 0 := by
  intro jv
  induction jv using Nat.strong_induction_on with
  | _ jv ih =>
    intro j hjv hj m hmj
    obtain ⟨_, _, _, ⟨w, _, hw⟩, _, _⟩ := hdata j hj
    rw [hw, compIdem]
    have hq : g m * (1 - ∑ i ∈ Finset.univ.filter
        (fun i => i < j), p i) = g m := by
      rw [Matrix.mul_sub, Matrix.mul_one, Finset.mul_sum]
      rw [Finset.sum_eq_zero fun i hi => by
        have hij : i < j := (Finset.mem_filter.mp hi).2
        have hijv : i.val < jv := by
          rw [← hjv]
          exact hij
        have hik : i.val < k := Nat.lt_trans hij hj
        exact ih i.val hijv i rfl hik m (lt_trans hij hmj)]
      rw [sub_zero]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hq,
      horth m j (ne_of_gt hmj), Matrix.zero_mul]

/-- **Ordered orthogonalization**: a finite family of
pairwise-orthogonal idempotents of `S` summing to `1`
yields a family of pairwise-orthogonal self-adjoint
projections of `S` summing to `1`, each Kaplansky
equivalent to its successively compressed idempotent. -/
theorem ordered_orthogonalization
    (hstar : ∀ a ∈ S, aᴴ ∈ S)
    (hgS : ∀ j, g j ∈ S) (hgidem : ∀ j, g j * g j = g j)
    (horth : ∀ j k, j ≠ k → g j * g k = 0)
    (hgsum : ∑ j, g j = 1) :
    ∃ p : Fin N → Matrix n n ℂ,
      (∀ j, SlotData S g p j)
      ∧ (∀ j l, j ≠ l → p j * p l = 0)
      ∧ ∑ j, p j = 1 := by
  classical
  have aux : ∀ k : ℕ, k ≤ N →
      ∃ p : Fin N → Matrix n n ℂ,
        (∀ j : Fin N, k ≤ j.val → p j = 0)
        ∧ (∀ j : Fin N, j.val < k → SlotData S g p j)
        ∧ (∀ j l : Fin N, j ≠ l → p j * p l = 0) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ => 0, fun _ _ => rfl,
        fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j l _ => Matrix.zero_mul 0⟩
    | succ k ih =>
      intro hk1
      obtain ⟨p, hzero, hdata, horthp⟩ :=
        ih (Nat.le_of_succ_le hk1)
      have hkN : k < N := hk1
      set jk : Fin N := ⟨k, hkN⟩ with hjk
      have hjkval : jk.val = k := rfl
      have hkill := kill_lemma S g horth p hdata
      have hpq : ∀ j : Fin N, j.val < k →
          p j * (∑ i ∈ Finset.univ.filter
            (fun i => i < jk), p i) = p j := by
        intro j hj
        rw [Finset.mul_sum]
        rw [Finset.sum_eq_single j (fun i hi hij => by
            exact horthp j i (Ne.symm hij))
          (fun hnot => absurd (Finset.mem_filter.mpr
            ⟨Finset.mem_univ j, show j < jk from hj⟩) hnot)]
        exact (hdata j hj).2.2.1
      have hgq : g jk * (∑ i ∈ Finset.univ.filter
          (fun i => i < jk), p i) = 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hij : i < jk := (Finset.mem_filter.mp hi).2
        exact hkill i.val i rfl hij jk hij
      have hqS : (∑ i ∈ Finset.univ.filter
          (fun i => i < jk), p i) ∈ S := by
        refine Subalgebra.sum_mem S fun i hi => ?_
        exact (hdata i ((Finset.mem_filter.mp hi).2)).1
      have he'S : compIdem g p jk ∈ S := by
        unfold compIdem
        exact S.mul_mem (S.sub_mem S.one_mem hqS) (hgS jk)
      have hg1q : g jk * (1 - ∑ i ∈ Finset.univ.filter
          (fun i => i < jk), p i) = g jk := by
        rw [Matrix.mul_sub, Matrix.mul_one, hgq, sub_zero]
      have he'idem : compIdem g p jk * compIdem g p jk
          = compIdem g p jk := by
        unfold compIdem
        calc (1 - ∑ i ∈ Finset.univ.filter
              (fun i => i < jk), p i) * g jk *
            ((1 - ∑ i ∈ Finset.univ.filter
              (fun i => i < jk), p i) * g jk)
            = (1 - ∑ i ∈ Finset.univ.filter
              (fun i => i < jk), p i) *
              ((g jk * (1 - ∑ i ∈ Finset.univ.filter
                (fun i => i < jk), p i)) * g jk) := by
              simp only [Matrix.mul_assoc]
          _ = (1 - ∑ i ∈ Finset.univ.filter
              (fun i => i < jk), p i) * (g jk * g jk) := by
              rw [hg1q]
          _ = _ := by rw [hgidem]
      obtain ⟨pk, w, hpkS, hwS, hpk_fact, hpkH, hpkidem,
        hpke, hepk⟩ :=
        kaplansky_projection S hstar he'S he'idem
      refine ⟨Function.update p jk pk, ?_, ?_, ?_⟩
      · intro j hj
        have hne : j ≠ jk := by
          intro h
          have hval := congrArg Fin.val h
          omega
        rw [Function.update_of_ne hne]
        exact hzero j (by omega)
      · intro j hj
        have hcomp_stable : ∀ j' : Fin N, j'.val ≤ k →
            compIdem g (Function.update p jk pk) j'
              = compIdem g p j' := by
          intro j' hj'
          unfold compIdem
          congr 2
          refine Finset.sum_congr rfl fun i hi => ?_
          have hij : i < j' := (Finset.mem_filter.mp hi).2
          have hine : i ≠ jk := by
            intro h
            have hval := congrArg Fin.val h
            have hijv : i.val < j'.val := hij
            omega
          exact Function.update_of_ne hine _ _
        rcases Nat.lt_or_ge j.val k with hjlt | hjge
        · have hne : j ≠ jk := by
            intro h
            rw [h, hjk] at hjlt
            omega
          have hold := hdata j hjlt
          unfold SlotData
          rw [Function.update_of_ne hne,
            hcomp_stable j hjlt.le]
          exact hold
        · have hjeq : j = jk := by
            apply Fin.ext
            omega
          unfold SlotData
          rw [hjeq, Function.update_self,
            hcomp_stable jk (le_of_eq hjkval)]
          exact ⟨hpkS, hpkH, hpkidem, ⟨w, hwS, hpk_fact⟩,
            hpke, hepk⟩
      · intro j l hjl
        rcases eq_or_ne j jk with hj | hj <;>
          rcases eq_or_ne l jk with hl | hl
        · exact absurd (hj.trans hl.symm) hjl
        · subst hj
          rw [Function.update_self,
            Function.update_of_ne hl]
          rcases Nat.lt_or_ge l.val k with hllt | hlge
          · have hplq := hpq l hllt
            have hple' : p l * compIdem g p jk = 0 := by
              unfold compIdem
              rw [← Matrix.mul_assoc, Matrix.mul_sub,
                Matrix.mul_one, hplq, sub_self,
                Matrix.zero_mul]
            have : p l * pk = 0 := by
              rw [hpk_fact, ← Matrix.mul_assoc, hple',
                Matrix.zero_mul]
            have hlH := (hdata l hllt).2.1
            calc pk * p l = ((p l)ᴴ * pkᴴ)ᴴ := by
                  rw [Matrix.conjTranspose_mul,
                    Matrix.conjTranspose_conjTranspose,
                    Matrix.conjTranspose_conjTranspose]
              _ = (p l * pk)ᴴ := by rw [hlH, hpkH]
              _ = 0 := by rw [this, Matrix.conjTranspose_zero]
          · rw [hzero l hlge, Matrix.mul_zero]
        · subst hl
          rw [Function.update_self,
            Function.update_of_ne hj]
          rcases Nat.lt_or_ge j.val k with hjlt | hjge
          · have hplq := hpq j hjlt
            have hple' : p j * compIdem g p jk = 0 := by
              unfold compIdem
              rw [← Matrix.mul_assoc, Matrix.mul_sub,
                Matrix.mul_one, hplq, sub_self,
                Matrix.zero_mul]
            rw [hpk_fact, ← Matrix.mul_assoc, hple',
              Matrix.zero_mul]
          · rw [hzero j hjge, Matrix.zero_mul]
        · rw [Function.update_of_ne hj,
            Function.update_of_ne hl]
          exact horthp j l hjl
  obtain ⟨p, hzero, hdata, horthp⟩ := aux N le_rfl
  have hdata' : ∀ j, SlotData S g p j :=
    fun j => hdata j j.isLt
  have hsum1 : ∑ j, p j = 1 := by
    have hkillall : ∀ m : Fin N,
        (1 - ∑ j, p j) * g m = 0 := by
      intro m
      have hqm : compIdem g p m
          = (1 - ∑ i ∈ Finset.univ.filter
            (fun i => i < m), p i) * g m := rfl
      have hgm_split : g m = compIdem g p m
          + (∑ i ∈ Finset.univ.filter
            (fun i => i < m), p i) * g m := by
        rw [hqm, Matrix.sub_mul, Matrix.one_mul]
        abel
      have hPp : ∀ l : Fin N, (∑ j, p j) * p l = p l := by
        intro l
        rw [Finset.sum_mul]
        rw [Finset.sum_eq_single l
          (fun i _ hil => horthp i l hil)
          (fun h => absurd (Finset.mem_univ l) h)]
        exact (hdata' l).2.2.1
      have h1 : (1 - ∑ j, p j) * compIdem g p m = 0 := by
        have hpm := (hdata' m).2.2.2.2.1
        rw [← hpm, ← Matrix.mul_assoc, Matrix.sub_mul,
          Matrix.one_mul, hPp, sub_self, Matrix.zero_mul]
      have h2 : (1 - ∑ j, p j) *
          ((∑ i ∈ Finset.univ.filter
            (fun i => i < m), p i) * g m) = 0 := by
        rw [← Matrix.mul_assoc, Matrix.sub_mul,
          Matrix.one_mul]
        rw [show (∑ j, p j) * (∑ i ∈ Finset.univ.filter
            (fun i => i < m), p i)
          = ∑ i ∈ Finset.univ.filter
            (fun i => i < m), p i from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => hPp i]
        rw [sub_self, Matrix.zero_mul]
      rw [hgm_split, Matrix.mul_add, h1, h2, add_zero]
    have hfin : (1 - ∑ j, p j) = 0 := by
      calc (1 - ∑ j, p j)
          = (1 - ∑ j, p j) * (∑ m, g m) := by
            rw [hgsum, Matrix.mul_one]
        _ = ∑ m, (1 - ∑ j, p j) * g m := by
            rw [Finset.mul_sum]
        _ = 0 := Finset.sum_eq_zero fun m _ => hkillall m
    have := sub_eq_zero.mp hfin
    exact this.symm
  exact ⟨p, hdata', horthp, hsum1⟩

/-- Generalized kill: any element annihilating the first
`k` diagonal idempotents on the left annihilates the first
`k` constructed projections on the left. -/
theorem kill_general
    (p : Fin N → Matrix n n ℂ) {k : ℕ}
    (hdata : ∀ j : Fin N, j.val < k → SlotData S g p j)
    (X : Matrix n n ℂ)
    (hX : ∀ i : Fin N, i.val < k → X * g i = 0) :
    ∀ (jv : ℕ) (j : Fin N), j.val = jv → j.val < k →
      X * p j = 0 := by
  intro jv
  induction jv using Nat.strong_induction_on with
  | _ jv ih =>
    intro j hjv hj
    obtain ⟨_, _, _, ⟨w, _, hw⟩, _, _⟩ := hdata j hj
    rw [hw, compIdem]
    have hq : X * (1 - ∑ i ∈ Finset.univ.filter
        (fun i => i < j), p i) = X := by
      rw [Matrix.mul_sub, Matrix.mul_one, Finset.mul_sum]
      rw [Finset.sum_eq_zero fun i hi => by
        have hij : i < j := (Finset.mem_filter.mp hi).2
        have hijv : i.val < jv := by
          rw [← hjv]
          exact hij
        exact ih i.val hijv i rfl (Nat.lt_trans hij hj)]
      rw [sub_zero]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hq,
      hX j hj, Matrix.zero_mul]

end Orthogonalization

section Units

variable {M : ℕ} (blk : Fin M → ℕ)
variable (U : Fin M → Fin M → Matrix n n ℂ)

/-- The AW unit multiplication law. -/
def UnitLaw : Prop :=
  ∀ j k l m', U j k * U l m' =
    if k = l ∧ blk j = blk k ∧ blk l = blk m'
      then U j m' else 0

/-- The block sum `Ê_b = ∑_{blk j = b} U j j` is central. -/
private theorem blockSum_central
    (hUmul : UnitLaw blk U)
    (hspan : ∀ x ∈ S, x ∈ Submodule.span ℂ
      {y | ∃ j k, blk j = blk k ∧ y = U j k}) (b : ℕ) :
    ∀ x ∈ S, (∑ j ∈ Finset.univ.filter
        (fun j => blk j = b), U j j) * x
      = x * ∑ j ∈ Finset.univ.filter
        (fun j => blk j = b), U j j := by
  intro x hx
  have hx' := hspan x hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, m', hlm, rfl⟩ := hy
    rw [Finset.sum_mul, Finset.mul_sum]
    by_cases hb : blk l = b
    · rw [Finset.sum_eq_single_of_mem l
        (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hb⟩)
        (fun j _ hjl => by
          rw [hUmul j j l m', if_neg fun hc => hjl hc.1]),
        Finset.sum_eq_single_of_mem m'
        (Finset.mem_filter.mpr ⟨Finset.mem_univ m', hlm ▸ hb⟩)
        (fun j _ hjm => by
          rw [hUmul l m' j j, if_neg fun hc => hjm hc.1.symm]),
        hUmul l l l m', if_pos ⟨rfl, rfl, hlm⟩,
        hUmul l m' m' m', if_pos ⟨rfl, hlm, rfl⟩]
    · rw [Finset.sum_eq_zero fun j hj => by
          rw [hUmul j j l m', if_neg]
          rintro ⟨rfl, -, -⟩
          exact hb (Finset.mem_filter.mp hj).2,
        Finset.sum_eq_zero fun j hj => by
          rw [hUmul l m' j j, if_neg]
          rintro ⟨rfl, -, -⟩
          exact hb (hlm.trans (Finset.mem_filter.mp hj).2)]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]
  | add y z _ _ ihy ihz =>
    rw [Matrix.mul_add, Matrix.add_mul, ihy, ihz]
  | smul c y _ ihy =>
    rw [mul_smul_comm, smul_mul_assoc, ihy]

/-- **The star bridge**: from an Artin–Wedderburn unit
system of a star-closed subalgebra, construct the
self-adjoint projection family, the connecting partial
isometries, and the central block projections — the
star-compatible matrix units `f_{jk} = v_j v_k*` follow. -/
theorem star_matrix_units
    (hstar : ∀ a ∈ S, aᴴ ∈ S)
    (hUmul : UnitLaw blk U)
    (hUS : ∀ j k, U j k ∈ S)
    (hUsum : ∑ j, U j j = 1)
    (hUne : ∀ j k, blk j = blk k → U j k ≠ 0)
    (hspan : ∀ x ∈ S, x ∈ Submodule.span ℂ
      {y | ∃ j k, blk j = blk k ∧ y = U j k}) :
    ∃ (p v : Fin M → Matrix n n ℂ)
      (base : Fin M → Fin M),
      (∀ j, blk (base j) = blk j)
      ∧ (∀ j k, blk j = blk k → base j = base k)
      ∧ (∀ j, p j ∈ S) ∧ (∀ j, (p j)ᴴ = p j)
      ∧ (∀ j, p j * p j = p j)
      ∧ (∀ j k, j ≠ k → p j * p k = 0)
      ∧ (∑ j, p j = 1)
      ∧ (∀ j, v j ∈ S)
      ∧ (∀ j k, (v j)ᴴ * v k
          = if j = k then p (base j) else 0)
      ∧ (∀ j, v j * (v j)ᴴ = p j)
      ∧ (∀ b : ℕ, ∀ x ∈ S,
          (∑ j ∈ Finset.univ.filter
            (fun j => blk j = b), p j) * x
          = x * ∑ j ∈ Finset.univ.filter
            (fun j => blk j = b), p j) := by
  classical
  -- Step 1: orthogonalize the diagonal idempotents.
  obtain ⟨p, hslot, horthp, hsump⟩ :=
    ordered_orthogonalization S (fun i => U i i) hstar
      (fun i => hUS i i)
      (fun i => by
        show U i i * U i i = U i i
        rw [hUmul i i i i, if_pos ⟨rfl, rfl, rfl⟩])
      (fun i k h => by
        show U i i * U k k = 0
        rw [hUmul i i k k, if_neg fun hc => h hc.1])
      hUsum
  -- Step 2: base point of each block.
  obtain ⟨base, hbase_blk, hbase_le⟩ :
      ∃ base : Fin M → Fin M,
        (∀ j, blk (base j) = blk j)
        ∧ ∀ j i, blk i = blk j → base j ≤ i := by
    have hne : ∀ j : Fin M,
        ((Finset.univ.filter (fun i => blk i = blk j)) :
          Finset (Fin M)).Nonempty :=
      fun j => ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ j, rfl⟩⟩
    refine ⟨fun j => (Finset.univ.filter
        (fun i => blk i = blk j)).min' (hne j),
      fun j => ?_, fun j i hi => ?_⟩
    · exact (Finset.mem_filter.mp
        (Finset.min'_mem _ (hne j))).2
    · exact Finset.min'_le _ i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hbase_eq : ∀ j k, blk j = blk k → base j = base k := by
    intro j k hjk
    refine le_antisymm
      (hbase_le j (base k) ?_) (hbase_le k (base j) ?_)
    · rw [hbase_blk k, ← hjk]
    · rw [hbase_blk j, hjk]
  -- Step 3: reduced multiplication facts.
  have hpr : ∀ j : Fin M, p j * (∑ i ∈ Finset.univ.filter
      (fun i => i < j), p i) = 0 := by
    intro j
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun i hi =>
      horthp j i (Finset.mem_filter.mp hi).2.ne'
  have hUkill : ∀ (X : Matrix n n ℂ) (m : Fin M),
      (∀ i : Fin M, i.val < m.val → X * U i i = 0) →
      X * (∑ i ∈ Finset.univ.filter
        (fun i => i < m), p i) = 0 := by
    intro X m hX
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun i hi =>
      kill_general S (fun i => U i i) p
        (fun i _ => hslot i) X hX i.val i rfl
        ((Finset.mem_filter.mp hi).2)
  have hgr : ∀ j : Fin M, U j j * (∑ i ∈ Finset.univ.filter
      (fun i => i < j), p i) = 0 := by
    intro j
    refine hUkill (U j j) j fun i hi => ?_
    rw [hUmul j j i i, if_neg]
    rintro ⟨rfl, -, -⟩
    exact lt_irrefl _ hi
  have hUbr : ∀ j : Fin M,
      U j (base j) * (∑ i ∈ Finset.univ.filter
        (fun i => i < base j), p i) = 0 := by
    intro j
    refine hUkill (U j (base j)) (base j) fun i hi => ?_
    rw [hUmul j (base j) i i, if_neg]
    rintro ⟨rfl, -, -⟩
    exact lt_irrefl _ hi
  have hcompeq : ∀ j : Fin M,
      compIdem (fun i => U i i) p j
        = U j j - (∑ i ∈ Finset.univ.filter
          (fun i => i < j), p i) * U j j := by
    intro j
    simp only [compIdem]
    rw [Matrix.sub_mul, Matrix.one_mul]
  have hpU : ∀ j : Fin M,
      p j * U j j = compIdem (fun i => U i i) p j := by
    intro j
    have h1 := (hslot j).2.2.2.2.1
    rw [hcompeq j, Matrix.mul_sub, ← Matrix.mul_assoc,
      hpr j, Matrix.zero_mul, sub_zero] at h1
    rw [hcompeq j]
    exact h1
  have hcompne : ∀ j : Fin M,
      compIdem (fun i => U i i) p j ≠ 0 := by
    intro j h0
    rw [hcompeq j, sub_eq_zero] at h0
    have h3 : U j j * U j j
        = U j j * ((∑ i ∈ Finset.univ.filter
          (fun i => i < j), p i) * U j j) := by
      rw [← h0]
    rw [← Matrix.mul_assoc, hgr j, Matrix.zero_mul] at h3
    refine hUne j j rfl ?_
    calc U j j = U j j * U j j := by
          rw [hUmul j j j j, if_pos ⟨rfl, rfl, rfl⟩]
      _ = 0 := h3
  have hpne : ∀ j : Fin M, p j ≠ 0 := by
    intro j hp0
    have h := (hslot j).2.2.2.2.1
    rw [hp0, Matrix.zero_mul] at h
    exact hcompne j h.symm
  -- Step 4: corner minimality.
  have hgcorner : ∀ (j : Fin M), ∀ a ∈ S, ∃ c : ℂ,
      U j j * (a * U j j) = c • U j j := by
    intro j a ha
    have ha' := hspan a ha
    clear ha
    induction ha' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, m', hlm, rfl⟩ := hy
      by_cases hm : m' = j
      · rw [hUmul l m' j j, if_pos ⟨hm, hlm, rfl⟩]
        by_cases hl : j = l
        · refine ⟨1, ?_⟩
          rw [hUmul j j l j,
            if_pos ⟨hl, rfl, (congrArg blk hl).symm⟩,
            one_smul]
        · exact ⟨0, by
            rw [hUmul j j l j, if_neg fun hc => hl hc.1,
              zero_smul]⟩
      · exact ⟨0, by
          rw [hUmul l m' j j, if_neg fun hc => hm hc.1,
            Matrix.mul_zero, zero_smul]⟩
    | zero =>
      exact ⟨0, by
        rw [Matrix.zero_mul, Matrix.mul_zero, zero_smul]⟩
    | add y z _ _ ihy ihz =>
      obtain ⟨c1, h1⟩ := ihy
      obtain ⟨c2, h2⟩ := ihz
      exact ⟨c1 + c2, by
        rw [Matrix.add_mul, Matrix.mul_add, h1, h2,
          add_smul]⟩
    | smul t y _ ihy =>
      obtain ⟨c, hc⟩ := ihy
      exact ⟨t * c, by
        rw [smul_mul_assoc, mul_smul_comm, hc, smul_smul]⟩
  have hecorner : ∀ (j : Fin M), ∀ a ∈ S, ∃ c : ℂ,
      compIdem (fun i => U i i) p j
          * (a * compIdem (fun i => U i i) p j)
        = c • compIdem (fun i => U i i) p j := by
    intro j a ha
    have hrS : (∑ i ∈ Finset.univ.filter
        (fun i => i < j), p i) ∈ S :=
      Subalgebra.sum_mem S fun i _ => (hslot i).1
    obtain ⟨c, hc⟩ := hgcorner j
      (a * (1 - ∑ i ∈ Finset.univ.filter
        (fun i => i < j), p i))
      (S.mul_mem ha (S.sub_mem S.one_mem hrS))
    refine ⟨c, ?_⟩
    have hunfold : compIdem (fun i => U i i) p j
        = (1 - ∑ i ∈ Finset.univ.filter
          (fun i => i < j), p i) * U j j := by
      simp only [compIdem]
    rw [hunfold, Matrix.mul_assoc,
      ← Matrix.mul_assoc a
        (1 - ∑ i ∈ Finset.univ.filter
          (fun i => i < j), p i) (U j j),
      hc, mul_smul_comm]
  have hpcorner : ∀ (j : Fin M), ∀ a ∈ S, ∃ c : ℂ,
      p j * (a * p j) = c • p j := by
    intro j a ha
    have hsS : p j * (a * p j) ∈ S :=
      S.mul_mem (hslot j).1 (S.mul_mem ha (hslot j).1)
    obtain ⟨c, hc⟩ := hecorner j _ hsS
    refine ⟨c, ?_⟩
    have he'p : compIdem (fun i => U i i) p j * p j = p j :=
      (hslot j).2.2.2.2.2
    have hes : compIdem (fun i => U i i) p j
        * (p j * (a * p j)) = p j * (a * p j) := by
      rw [← Matrix.mul_assoc, he'p]
    have hsp : (p j * (a * p j)) * p j = p j * (a * p j) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc,
        (hslot j).2.2.1]
    calc p j * (a * p j)
        = compIdem (fun i => U i i) p j
            * (p j * (a * p j)) := hes.symm
      _ = compIdem (fun i => U i i) p j
            * ((p j * (a * p j)) * p j) := by rw [hsp]
      _ = compIdem (fun i => U i i) p j
            * ((p j * (a * p j))
              * (compIdem (fun i => U i i) p j * p j)) := by
          rw [he'p]
      _ = (compIdem (fun i => U i i) p j
            * ((p j * (a * p j))
              * compIdem (fun i => U i i) p j)) * p j := by
          rw [Matrix.mul_assoc (compIdem (fun i => U i i) p j)
              (p j * (a * p j) * compIdem (fun i => U i i) p j)
              (p j),
            Matrix.mul_assoc (p j * (a * p j))
              (compIdem (fun i => U i i) p j) (p j)]
      _ = (c • compIdem (fun i => U i i) p j) * p j := by
          rw [hc]
      _ = c • p j := by rw [smul_mul_assoc, he'p]
  -- Step 5: connecting elements and their nonvanishing.
  have hUcomp : ∀ j : Fin M,
      U j (base j) * compIdem (fun i => U i i) p (base j)
        = U j (base j) := by
    intro j
    rw [hcompeq (base j), Matrix.mul_sub,
      ← Matrix.mul_assoc, hUbr j, Matrix.zero_mul,
      sub_zero, hUmul j (base j) (base j) (base j),
      if_pos ⟨rfl, (hbase_blk j).symm, rfl⟩]
  have hpx : ∀ j : Fin M,
      p j * (p j * (U j (base j) * p (base j)))
        = p j * (U j (base j) * p (base j)) := by
    intro j
    rw [← Matrix.mul_assoc, (hslot j).2.2.1]
  have hxne : ∀ j : Fin M,
      p j * (U j (base j) * p (base j)) ≠ 0 := by
    intro j hx0
    have hpeb : p (base j)
        * compIdem (fun i => U i i) p (base j)
        = compIdem (fun i => U i i) p (base j) :=
      (hslot (base j)).2.2.2.2.1
    have hu : p j * U j (base j) = 0 := by
      calc p j * U j (base j)
          = p j * (U j (base j)
              * compIdem (fun i => U i i) p (base j)) := by
            rw [hUcomp j]
        _ = p j * (U j (base j)
              * (p (base j)
                * compIdem (fun i => U i i) p (base j))) := by
            rw [hpeb]
        _ = (p j * (U j (base j) * p (base j)))
              * compIdem (fun i => U i i) p (base j) := by
            rw [Matrix.mul_assoc
                (p j) (U j (base j) * p (base j))
                (compIdem (fun i => U i i) p (base j)),
              Matrix.mul_assoc (U j (base j)) (p (base j))
                (compIdem (fun i => U i i) p (base j))]
        _ = 0 := by rw [hx0, Matrix.zero_mul]
    have h2 : (p j * U j (base j)) * U (base j) j
        = compIdem (fun i => U i i) p j := by
      rw [Matrix.mul_assoc, hUmul j (base j) (base j) j,
        if_pos ⟨rfl, (hbase_blk j).symm, hbase_blk j⟩,
        hpU j]
    rw [hu, Matrix.zero_mul] at h2
    exact hcompne j h2.symm
  -- Step 6: normalized partial isometries.
  have hmain : ∀ j : Fin M, ∃ v : Matrix n n ℂ, v ∈ S
      ∧ vᴴ * v = p (base j)
      ∧ v * vᴴ = p j
      ∧ ∃ s : ℂ,
          v = s • (p j * (U j (base j) * p (base j))) := by
    intro j
    set x := p j * (U j (base j) * p (base j)) with hxdef
    have hxS : x ∈ S := S.mul_mem (hslot j).1
      (S.mul_mem (hUS j (base j)) (hslot (base j)).1)
    have hxx : xᴴ * x
        = p (base j) * (((U j (base j))ᴴ
          * (p j * U j (base j))) * p (base j)) := by
      rw [hxdef]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
        (hslot j).2.1, (hslot (base j)).2.1]
      rw [← Matrix.mul_assoc (p j) (p j), (hslot j).2.2.1]
    have haS : ((U j (base j))ᴴ * (p j * U j (base j))) ∈ S :=
      S.mul_mem (hstar _ (hUS j (base j)))
        (S.mul_mem (hslot j).1 (hUS j (base j)))
    obtain ⟨c, hc⟩ := hpcorner (base j) _ haS
    have hxxc : xᴴ * x = c • p (base j) := by
      rw [hxx]; exact hc
    have hcne : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_smul] at hxxc
      have hx0 : x = 0 :=
        Matrix.conjTranspose_mul_self_eq_zero.mp hxxc
      rw [hxdef] at hx0
      exact hxne j hx0
    -- trace bookkeeping: the corner scalar is a positive real
    have ht1 : (0:ℂ) ≤ (xᴴ * x).trace :=
      (Matrix.posSemidef_conjTranspose_mul_self x).trace_nonneg
    have ht2eq : (p (base j)).trace
        = ((p (base j))ᴴ * p (base j)).trace := by
      rw [(hslot (base j)).2.1]
      conv_lhs => rw [← (hslot (base j)).2.2.1]
    have ht2 : (0:ℂ) ≤ (p (base j)).trace := by
      rw [ht2eq]
      exact (Matrix.posSemidef_conjTranspose_mul_self
        (p (base j))).trace_nonneg
    have ht2ne : (p (base j)).trace ≠ 0 := by
      rw [ht2eq]
      intro h0
      exact hpne (base j)
        (Matrix.conjTranspose_mul_self_eq_zero.mp
          ((Matrix.posSemidef_conjTranspose_mul_self
            (p (base j))).trace_eq_zero_iff.mp h0))
    have htr : (xᴴ * x).trace = c * (p (base j)).trace := by
      rw [hxxc, Matrix.trace_smul, smul_eq_mul]
    have ht1ne : (xᴴ * x).trace ≠ 0 := by
      rw [htr]
      exact mul_ne_zero hcne ht2ne
    obtain ⟨h1re, h1im⟩ := Complex.nonneg_iff.mp ht1
    obtain ⟨h2re, h2im⟩ := Complex.nonneg_iff.mp ht2
    have ht1c : (xᴴ * x).trace = ((xᴴ * x).trace.re : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm
        (by rw [Complex.ofReal_im]; exact h1im.symm)
    have ht2c : (p (base j)).trace
        = ((p (base j)).trace.re : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm
        (by rw [Complex.ofReal_im]; exact h2im.symm)
    have ht2repos : 0 < (p (base j)).trace.re := by
      rcases lt_or_eq_of_le h2re with h | h
      · exact h
      · exact absurd
          (by rw [ht2c, ← h, Complex.ofReal_zero]) ht2ne
    have ht1repos : 0 < (xᴴ * x).trace.re := by
      rcases lt_or_eq_of_le h1re with h | h
      · exact h
      · exact absurd
          (by rw [ht1c, ← h, Complex.ofReal_zero]) ht1ne
    have hcval : c = (((xᴴ * x).trace.re
        / (p (base j)).trace.re : ℝ) : ℂ) := by
      rw [Complex.ofReal_div,
        eq_div_iff (Complex.ofReal_ne_zero.mpr
          ht2repos.ne')]
      rw [← ht2c, ← ht1c, htr]
    have hcRpos : 0 < (xᴴ * x).trace.re
        / (p (base j)).trace.re :=
      div_pos ht1repos ht2repos
    set cR : ℝ := (xᴴ * x).trace.re / (p (base j)).trace.re
      with hcRdef
    have hscal : ((((Real.sqrt cR)⁻¹ : ℝ)) : ℂ)
        * ((((Real.sqrt cR)⁻¹ : ℝ)) : ℂ) * c = 1 := by
      rw [hcval, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← mul_inv, Real.mul_self_sqrt hcRpos.le,
        inv_mul_cancel₀ hcRpos.ne', Complex.ofReal_one]
    have hstars : star ((((Real.sqrt cR)⁻¹ : ℝ)) : ℂ)
        = ((((Real.sqrt cR)⁻¹ : ℝ)) : ℂ) := by
      rw [Complex.star_def]
      exact Complex.conj_ofReal _
    -- the reversed product carries the same scalar
    have hxxH : x * xᴴ
        = p j * ((U j (base j)
          * (p (base j) * (U j (base j))ᴴ)) * p j) := by
      rw [hxdef]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
        (hslot j).2.1, (hslot (base j)).2.1]
      rw [← Matrix.mul_assoc (p (base j)) (p (base j)),
        (hslot (base j)).2.2.1]
    have ha'S : (U j (base j)
        * (p (base j) * (U j (base j))ᴴ)) ∈ S :=
      S.mul_mem (hUS j (base j))
        (S.mul_mem (hslot (base j)).1
          (hstar _ (hUS j (base j))))
    obtain ⟨c', hc'⟩ := hpcorner j _ ha'S
    have hxxHc : x * xᴴ = c' • p j := by
      rw [hxxH]; exact hc'
    have hA : (xᴴ * x) * (xᴴ * x)
        = (c * c) • p (base j) := by
      rw [hxxc, smul_mul_assoc, mul_smul_comm, smul_smul,
        (hslot (base j)).2.2.1]
    have hB : (xᴴ * x) * (xᴴ * x)
        = (c' * c) • p (base j) := by
      calc (xᴴ * x) * (xᴴ * x)
          = xᴴ * ((x * xᴴ) * x) := by
            simp only [Matrix.mul_assoc]
        _ = xᴴ * ((c' • p j) * x) := by rw [hxxHc]
        _ = c' • (xᴴ * (p j * x)) := by
            rw [smul_mul_assoc, mul_smul_comm]
        _ = c' • (xᴴ * x) := by rw [hxdef, hpx j]
        _ = (c' * c) • p (base j) := by
            rw [hxxc, smul_smul]
    have hcc : c' = c := by
      by_contra hne
      have h12 : (c * c - c' * c) • p (base j) = 0 := by
        rw [sub_smul, ← hA, ← hB, sub_self]
      have hs0 : c * c - c' * c ≠ 0 := by
        intro h
        exact hne
          (mul_right_cancel₀ hcne (sub_eq_zero.mp h)).symm
      have hp0 : p (base j) = 0 := by
        have h13 := congrArg
          (fun t => (c * c - c' * c)⁻¹ • t) h12
        simpa [smul_smul, inv_mul_cancel₀ hs0] using h13
      exact hpne (base j) hp0
    refine ⟨((((Real.sqrt cR)⁻¹ : ℝ)) : ℂ) • x,
      S.smul_mem hxS _, ?_, ?_, ⟨_, rfl⟩⟩
    · rw [Matrix.conjTranspose_smul, hstars,
        smul_mul_assoc, mul_smul_comm, smul_smul, hxxc,
        smul_smul, hscal, one_smul]
    · rw [Matrix.conjTranspose_smul, hstars,
        smul_mul_assoc, mul_smul_comm, smul_smul, hxxHc,
        hcc, smul_smul, hscal, one_smul]
  choose v hvS hv1 hv2 hvs using hmain
  -- Step 7: cross-orthogonality of the isometries.
  have hxorth : ∀ j k : Fin M, j ≠ k →
      (p j * (U j (base j) * p (base j)))ᴴ
        * (p k * (U k (base k) * p (base k))) = 0 := by
    intro j k hjk
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      (hslot j).2.1, (hslot (base j)).2.1]
    rw [← Matrix.mul_assoc (p j) (p k), horthp j k hjk,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  have hlaw : ∀ j k : Fin M,
      (v j)ᴴ * v k = if j = k then p (base j) else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      exact hv1 j
    · rw [if_neg hjk]
      obtain ⟨sj, hsj⟩ := hvs j
      obtain ⟨sk, hsk⟩ := hvs k
      rw [hsj, hsk, Matrix.conjTranspose_smul,
        smul_mul_assoc, mul_smul_comm, smul_smul,
        hxorth j k hjk, smul_zero]
  -- Step 8: centrality of the block projections.
  have hcent : ∀ b : ℕ, ∀ x ∈ S,
      (∑ j ∈ Finset.univ.filter (fun j => blk j = b), p j)
          * x
        = x * ∑ j ∈ Finset.univ.filter
            (fun j => blk j = b), p j := by
    intro b
    have hUE : ∀ j : Fin M,
        U j j * (∑ k ∈ Finset.univ.filter
          (fun k => blk k = b), U k k)
          = if blk j = b then U j j else 0 := by
      intro j
      rw [Finset.mul_sum]
      by_cases hb : blk j = b
      · rw [Finset.sum_eq_single_of_mem j
          (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hb⟩)
          (fun k _ hkj => by
            rw [hUmul j j k k,
              if_neg fun hc => hkj hc.1.symm]),
          hUmul j j j j, if_pos ⟨rfl, rfl, rfl⟩,
          if_pos hb]
      · rw [Finset.sum_eq_zero fun k hk => by
            rw [hUmul j j k k, if_neg]
            rintro ⟨rfl, -, -⟩
            exact hb (Finset.mem_filter.mp hk).2,
          if_neg hb]
    have hpE : ∀ j : Fin M,
        p j * (∑ k ∈ Finset.univ.filter
          (fun k => blk k = b), U k k)
          = if blk j = b then p j else 0 := by
      intro j
      obtain ⟨w, hwS, hw⟩ := (hslot j).2.2.2.1
      have hcw : (∑ k ∈ Finset.univ.filter
          (fun k => blk k = b), U k k) * w
          = w * ∑ k ∈ Finset.univ.filter
            (fun k => blk k = b), U k k :=
        blockSum_central S blk U hUmul hspan b w hwS
      have hkey : compIdem (fun i => U i i) p j
          * (∑ k ∈ Finset.univ.filter
            (fun k => blk k = b), U k k)
          = if blk j = b
            then compIdem (fun i => U i i) p j else 0 := by
        rw [hcompeq j, Matrix.sub_mul, hUE j,
          Matrix.mul_assoc, hUE j]
        by_cases hb : blk j = b
        · rw [if_pos hb, if_pos hb]
        · rw [if_neg hb, if_neg hb, Matrix.mul_zero,
            sub_zero]
      calc p j * (∑ k ∈ Finset.univ.filter
            (fun k => blk k = b), U k k)
          = (compIdem (fun i => U i i) p j * w)
              * ∑ k ∈ Finset.univ.filter
                (fun k => blk k = b), U k k := by rw [hw]
        _ = compIdem (fun i => U i i) p j
              * ((∑ k ∈ Finset.univ.filter
                (fun k => blk k = b), U k k) * w) := by
            rw [Matrix.mul_assoc, ← hcw]
        _ = (if blk j = b
              then compIdem (fun i => U i i) p j else 0)
              * w := by
            rw [← Matrix.mul_assoc, hkey]
        _ = if blk j = b then p j else 0 := by
            by_cases hb : blk j = b
            · rw [if_pos hb, if_pos hb, ← hw]
            · rw [if_neg hb, if_neg hb, Matrix.zero_mul]
    have hPE : (∑ j ∈ Finset.univ.filter
          (fun j => blk j = b), p j)
        = ∑ j ∈ Finset.univ.filter
          (fun j => blk j = b), U j j := by
      calc (∑ j ∈ Finset.univ.filter
            (fun j => blk j = b), p j)
          = ∑ j, if blk j = b then p j else 0 :=
            Finset.sum_filter _ _
        _ = ∑ j, p j * ∑ k ∈ Finset.univ.filter
              (fun k => blk k = b), U k k :=
            Finset.sum_congr rfl fun j _ => (hpE j).symm
        _ = (∑ j, p j) * ∑ k ∈ Finset.univ.filter
              (fun k => blk k = b), U k k :=
            (Finset.sum_mul _ _ _).symm
        _ = ∑ k ∈ Finset.univ.filter
              (fun k => blk k = b), U k k := by
            rw [hsump, Matrix.one_mul]
    intro x hx
    rw [hPE]
    exact blockSum_central S blk U hUmul hspan b x hx
  exact ⟨p, v, base, hbase_blk, hbase_eq,
    fun j => (hslot j).1, fun j => (hslot j).2.1,
    fun j => (hslot j).2.2.1, horthp, hsump,
    hvS, hlaw, hv2, hcent⟩

end Units

section Assembly

/-- The canonical Artin–Wedderburn unit of a finite product of
matrix algebras, indexed by a pair of block coordinates. -/
private def blockUnit {r : ℕ} (d : Fin r → ℕ)
    (js ks : (i : Fin r) × Fin (d i)) :
    ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  if h : js.1 = ks.1
    then Pi.single js.1
      (Matrix.single js.2 (Fin.cast (congrArg d h.symm) ks.2) 1)
    else 0

private theorem blockUnit_same {r : ℕ} (d : Fin r → ℕ)
    (b : Fin r) (α β : Fin (d b)) :
    blockUnit d ⟨b, α⟩ ⟨b, β⟩
      = Pi.single b (Matrix.single α β 1) := by
  rw [blockUnit, dif_pos rfl]
  rfl

private theorem blockUnit_of_ne {r : ℕ} (d : Fin r → ℕ)
    {js ks : (i : Fin r) × Fin (d i)} (h : js.1 ≠ ks.1) :
    blockUnit d js ks = 0 := by
  rw [blockUnit, dif_neg h]

private theorem pi_single_mul_same {r : ℕ} {d : Fin r → ℕ}
    (b : Fin r) (A B : Matrix (Fin (d b)) (Fin (d b)) ℂ) :
    Pi.single b A * Pi.single b B
      = (Pi.single b (A * B) :
          ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  funext i
  rw [Pi.mul_apply]
  by_cases h : i = b
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same,
      Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h,
      Pi.single_eq_of_ne h, Matrix.zero_mul]

private theorem pi_single_mul_ne {r : ℕ} {d : Fin r → ℕ}
    {b1 b2 : Fin r} (h : b1 ≠ b2)
    (A : Matrix (Fin (d b1)) (Fin (d b1)) ℂ)
    (B : Matrix (Fin (d b2)) (Fin (d b2)) ℂ) :
    (Pi.single b1 A :
        ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
      * Pi.single b2 B = 0 := by
  funext i
  rw [Pi.mul_apply]
  by_cases h1 : i = b1
  · subst h1
    rw [Pi.single_eq_of_ne h, Matrix.mul_zero, Pi.zero_apply]
  · rw [Pi.single_eq_of_ne h1, Matrix.zero_mul, Pi.zero_apply]

private theorem blockUnit_mul {r : ℕ} (d : Fin r → ℕ)
    (js ks ls ms : (i : Fin r) × Fin (d i)) :
    blockUnit d js ks * blockUnit d ls ms
      = if ks = ls ∧ js.1 = ks.1 ∧ ls.1 = ms.1
          then blockUnit d js ms else 0 := by
  obtain ⟨b1, α⟩ := js
  obtain ⟨b2, β⟩ := ks
  obtain ⟨b3, γ⟩ := ls
  obtain ⟨b4, δ⟩ := ms
  by_cases h1 : b1 = b2
  · subst h1
    by_cases h2 : b3 = b4
    · subst h2
      rw [blockUnit_same, blockUnit_same]
      by_cases h3 : b1 = b3
      · subst h3
        rw [pi_single_mul_same]
        by_cases h4 : β = γ
        · subst h4
          rw [Matrix.single_mul_single_same, one_mul,
            if_pos ⟨rfl, rfl, rfl⟩, blockUnit_same]
        · rw [Matrix.single_mul_single_of_ne 1 α β γ h4 1,
            Pi.single_zero, if_neg]
          rintro ⟨hc, -, -⟩
          rw [Sigma.mk.injEq] at hc
          exact h4 (eq_of_heq hc.2)
      · rw [pi_single_mul_ne h3, if_neg]
        rintro ⟨hc, -, -⟩
        rw [Sigma.mk.injEq] at hc
        exact h3 hc.1
    · rw [blockUnit_of_ne d
          (js := ⟨b3, γ⟩) (ks := ⟨b4, δ⟩) h2,
        mul_zero, if_neg]
      rintro ⟨-, -, hc⟩
      exact h2 hc
  · rw [blockUnit_of_ne d
        (js := ⟨b1, α⟩) (ks := ⟨b2, β⟩) h1,
      zero_mul, if_neg]
    rintro ⟨-, hc, -⟩
    exact h1 hc

private theorem sum_single_diag (m : ℕ) :
    ∑ α : Fin m, Matrix.single α α (1:ℂ) = 1 := by
  ext i j
  rw [Matrix.sum_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun α _ hαi => by
        rw [Matrix.single_apply, if_neg fun hc => hαi hc.1])]
    rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, if_pos rfl]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h rfl

private theorem blockUnit_diag_sum {r : ℕ} (d : Fin r → ℕ) :
    ∑ js : (i : Fin r) × Fin (d i), blockUnit d js js = 1 := by
  have h1 : ∀ js : (i : Fin r) × Fin (d i),
      blockUnit d js js
        = Pi.single js.1 (Matrix.single js.2 js.2 1) := by
    rintro ⟨b, α⟩
    exact blockUnit_same d b α α
  rw [Finset.sum_congr rfl fun js _ => h1 js]
  funext b
  rw [Finset.sum_apply, Pi.one_apply,
    ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine (Finset.sum_eq_single_of_mem b (Finset.mem_univ b)
    (fun b' _ hb' => Finset.sum_eq_zero fun α _ =>
      Pi.single_eq_of_ne (Ne.symm hb') _)).trans ?_
  show ∑ α : Fin (d b),
    (Pi.single b (Matrix.single α α (1:ℂ)) :
      ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) b = 1
  exact (Finset.sum_congr rfl fun α _ =>
    Pi.single_eq_same
      (M := fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ)
      b (Matrix.single α α (1:ℂ))).trans
    (sum_single_diag _)

private theorem blockUnit_ne_zero {r : ℕ} (d : Fin r → ℕ)
    {js ks : (i : Fin r) × Fin (d i)} (h : js.1 = ks.1) :
    blockUnit d js ks ≠ 0 := by
  obtain ⟨b1, α⟩ := js
  obtain ⟨b2, β⟩ := ks
  have hb : b1 = b2 := h
  subst hb
  rw [blockUnit_same]
  intro h0
  have h1 := congrArg (fun f => f b1 α β) h0
  simp [Pi.single_eq_same] at h1

/-- **Star unit system**: every star-closed subalgebra of a
finite complex matrix algebra carries a self-adjoint central
unit system inside itself — pairwise-orthogonal self-adjoint
projections `p` summing to `1`, block-constant base points,
partial isometries `v` with `v_j* v_k = δ_{jk} p_{base j}` and
`v_j v_j* = p_j` (so the matrix units are `f_{jk} = v_j v_k*`),
and central block projections `∑_{blk = b} p_j`.  This is the
bridge from the abstract Artin–Wedderburn equivalence
(`matrixBlockDecomposition`) demanded by
`thm:commutant-decomposition`. -/
theorem star_unit_system
    (hstar : ∀ a ∈ S, aᴴ ∈ S) :
    ∃ (M : ℕ) (blk : Fin M → ℕ)
      (p v : Fin M → Matrix n n ℂ) (base : Fin M → Fin M),
      (∀ j, blk (base j) = blk j)
      ∧ (∀ j k, blk j = blk k → base j = base k)
      ∧ (∀ j, p j ∈ S) ∧ (∀ j, (p j)ᴴ = p j)
      ∧ (∀ j, p j * p j = p j)
      ∧ (∀ j k, j ≠ k → p j * p k = 0)
      ∧ (∑ j, p j = 1)
      ∧ (∀ j, v j ∈ S)
      ∧ (∀ j k, (v j)ᴴ * v k
          = if j = k then p (base j) else 0)
      ∧ (∀ j, v j * (v j)ᴴ = p j)
      ∧ (∀ b : ℕ, ∀ x ∈ S,
          (∑ j ∈ Finset.univ.filter
            (fun j => blk j = b), p j) * x
          = x * ∑ j ∈ Finset.univ.filter
            (fun j => blk j = b), p j) := by
  classical
  obtain ⟨r, d, _, ⟨e⟩⟩ :=
    FiniteStarSubalgebraMutualCommutant.matrixBlockDecomposition
      S hstar
  set σ : Fin (Fintype.card ((i : Fin r) × Fin (d i)))
      ≃ (i : Fin r) × Fin (d i) :=
    (Fintype.equivFin ((i : Fin r) × Fin (d i))).symm
    with hσdef
  set blk : Fin (Fintype.card ((i : Fin r) × Fin (d i))) → ℕ :=
    fun j => ((σ j).1 : ℕ) with hblkdef
  set U : Fin (Fintype.card ((i : Fin r) × Fin (d i)))
      → Fin (Fintype.card ((i : Fin r) × Fin (d i)))
      → Matrix n n ℂ :=
    fun j k =>
      ((e.symm (blockUnit d (σ j) (σ k)) : S) : Matrix n n ℂ)
    with hUdef
  have hUmul : UnitLaw blk U := by
    intro j k l m'
    simp only [hUdef]
    rw [← MulMemClass.coe_mul, ← map_mul, blockUnit_mul]
    by_cases hcond : k = l ∧ blk j = blk k ∧ blk l = blk m'
    · obtain ⟨rfl, hc2, hc3⟩ := hcond
      rw [if_pos ⟨rfl, Fin.val_injective hc2,
          Fin.val_injective hc3⟩,
        if_pos ⟨rfl, hc2, hc3⟩]
    · rw [if_neg hcond, if_neg]
      · rw [map_zero, ZeroMemClass.coe_zero]
      · intro hσc
        exact hcond ⟨σ.injective hσc.1,
          congrArg Fin.val hσc.2.1,
          congrArg Fin.val hσc.2.2⟩
  have hUS : ∀ j k, U j k ∈ S := fun j k =>
    SetLike.coe_mem (e.symm (blockUnit d (σ j) (σ k)))
  have hUsum : ∑ j, U j j = 1 := by
    simp only [hUdef]
    rw [← AddSubmonoidClass.coe_finsetSum, ← map_sum]
    have hreindex :
        ∑ j : Fin (Fintype.card ((i : Fin r) × Fin (d i))),
          blockUnit d (σ j) (σ j)
        = ∑ js : (i : Fin r) × Fin (d i), blockUnit d js js :=
      Equiv.sum_comp σ (fun js => blockUnit d js js)
    rw [hreindex, blockUnit_diag_sum, map_one,
      OneMemClass.coe_one]
  have hUne : ∀ j k, blk j = blk k → U j k ≠ 0 := by
    intro j k hjk h0
    simp only [hUdef] at h0
    simp only [hblkdef] at hjk
    have h1 : e.symm (blockUnit d (σ j) (σ k)) = 0 :=
      Subtype.ext
        (h0.trans (ZeroMemClass.coe_zero S).symm)
    have h2 : blockUnit d (σ j) (σ k) = 0 := by
      have h3 := congrArg e h1
      rwa [AlgEquiv.apply_symm_apply, map_zero] at h3
    exact blockUnit_ne_zero d (Fin.val_injective hjk) h2
  have hspan : ∀ x ∈ S, x ∈ Submodule.span ℂ
      {y | ∃ j k, blk j = blk k ∧ y = U j k} := by
    intro x hx
    have hxeq : (⟨x, hx⟩ : S) = e.symm (e ⟨x, hx⟩) :=
      (AlgEquiv.symm_apply_apply e _).symm
    set z := e (⟨x, hx⟩ : S) with hzdef
    have hsingle : ∀ (b : Fin r) (α β : Fin (d b)),
        (z b α β) • blockUnit d ⟨b, α⟩ ⟨b, β⟩
          = Pi.single b (Matrix.single α β (z b α β)) := by
      intro b α β
      rw [blockUnit_same, ← Pi.single_smul,
        Matrix.smul_single, smul_eq_mul, mul_one]
    have hcollapse : ∀ b : Fin r,
        ∑ α : Fin (d b), ∑ β : Fin (d b),
          Pi.single b (Matrix.single α β (z b α β))
        = (Pi.single b (z b) :
            ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
      intro b
      funext i
      by_cases hib : i = b
      · subst hib
        simp only [Finset.sum_apply, Pi.single_eq_same]
        exact (Matrix.matrix_eq_sum_single (z i)).symm
      · simp only [Finset.sum_apply,
          Pi.single_eq_of_ne hib, Finset.sum_const_zero]
    have hzsum : z = ∑ b : Fin r, ∑ α : Fin (d b),
        ∑ β : Fin (d b),
        (z b α β) • blockUnit d ⟨b, α⟩ ⟨b, β⟩ := by
      calc z = ∑ b : Fin r, Pi.single b (z b) :=
            (Finset.univ_sum_single z).symm
        _ = ∑ b : Fin r, ∑ α : Fin (d b), ∑ β : Fin (d b),
              Pi.single b (Matrix.single α β (z b α β)) :=
            Finset.sum_congr rfl fun b _ => (hcollapse b).symm
        _ = ∑ b : Fin r, ∑ α : Fin (d b), ∑ β : Fin (d b),
              (z b α β) • blockUnit d ⟨b, α⟩ ⟨b, β⟩ :=
            Finset.sum_congr rfl fun b _ =>
              Finset.sum_congr rfl fun α _ =>
                Finset.sum_congr rfl fun β _ =>
                  (hsingle b α β).symm
    have hS : (⟨x, hx⟩ : S) = ∑ b : Fin r, ∑ α : Fin (d b),
        ∑ β : Fin (d b),
        (z b α β) • e.symm (blockUnit d ⟨b, α⟩ ⟨b, β⟩) := by
      rw [hxeq]
      conv_lhs => rw [hzsum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [map_smul]
    have hxval : x = ∑ b : Fin r, ∑ α : Fin (d b),
        ∑ β : Fin (d b),
        (z b α β) • ((e.symm (blockUnit d ⟨b, α⟩ ⟨b, β⟩) : S)
          : Matrix n n ℂ) := by
      have h4 := congrArg
        (fun t : S => (t : Matrix n n ℂ)) hS
      simp only [AddSubmonoidClass.coe_finsetSum,
        Subalgebra.coe_smul] at h4
      exact h4
    rw [hxval]
    refine Submodule.sum_mem _ fun b _ =>
      Submodule.sum_mem _ fun α _ =>
        Submodule.sum_mem _ fun β _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨σ.symm ⟨b, α⟩, σ.symm ⟨b, β⟩, ?_, ?_⟩
    · show ((σ (σ.symm ⟨b, α⟩)).1 : ℕ)
        = ((σ (σ.symm ⟨b, β⟩)).1 : ℕ)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · simp only [hUdef]
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  obtain ⟨p, v, base, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11⟩ :=
    star_matrix_units S blk U hstar hUmul hUS hUsum hUne hspan
  exact ⟨_, blk, p, v, base, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11⟩

omit [DecidableEq n] in
/-- The star law of the derived matrix units
`f_{jk} = v_j v_k*`. -/
theorem unit_star {A B : Matrix n n ℂ} :
    (A * Bᴴ)ᴴ = B * Aᴴ := by
  rw [Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

omit [DecidableEq n] in
/-- A partial isometry absorbs its self-adjoint idempotent
initial projection on the right. -/
theorem isometry_absorb {q v : Matrix n n ℂ}
    (hqH : qᴴ = q) (hqidem : q * q = q)
    (hvq : vᴴ * v = q) : v * q = v := by
  have h : (v * q - v)ᴴ * (v * q - v) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      hqH, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have hA : (q * vᴴ) * (v * q) = q := by
      rw [Matrix.mul_assoc q vᴴ (v * q),
        ← Matrix.mul_assoc vᴴ v q, hvq, hqidem, hqidem]
    have hB : (q * vᴴ) * v = q := by
      rw [Matrix.mul_assoc, hvq, hqidem]
    have hC : vᴴ * (v * q) = q := by
      rw [← Matrix.mul_assoc, hvq, hqidem]
    rw [hA, hB, hC, hvq, sub_self]
  have h2 := Matrix.conjTranspose_mul_self_eq_zero.mp h
  exact sub_eq_zero.mp h2

omit [DecidableEq n] in
/-- The multiplication law of the derived matrix units
`f_{jk} = v_j v_k*`: within a block,
`f_{jk} f_{lm} = δ_{kl} f_{jm}`; all cross-block products
vanish through the base-point mismatch. -/
theorem unit_mul {M : ℕ}
    (p v : Fin M → Matrix n n ℂ) (base : Fin M → Fin M)
    (hpH : ∀ j, (p j)ᴴ = p j)
    (hpidem : ∀ j, p j * p j = p j)
    (hporth : ∀ j k, j ≠ k → p j * p k = 0)
    (hlaw : ∀ j k, (v j)ᴴ * v k
      = if j = k then p (base j) else 0)
    (j k l m : Fin M) :
    (v j * (v k)ᴴ) * (v l * (v m)ᴴ)
      = if k = l ∧ base m = base k
          then v j * (v m)ᴴ else 0 := by
  have habs : ∀ i, v i * p (base i) = v i := fun i =>
    isometry_absorb (hpH (base i)) (hpidem (base i))
      (by rw [hlaw i i, if_pos rfl])
  rw [Matrix.mul_assoc (v j) ((v k)ᴴ) (v l * (v m)ᴴ),
    ← Matrix.mul_assoc ((v k)ᴴ) (v l) ((v m)ᴴ), hlaw k l]
  by_cases hkl : k = l
  · rw [if_pos hkl]
    have h5 : v m * p (base k)
        = if base m = base k then v m else 0 := by
      by_cases hb : base m = base k
      · rw [if_pos hb, ← hb, habs m]
      · rw [if_neg hb, ← habs m, Matrix.mul_assoc,
          hporth (base m) (base k) hb, Matrix.mul_zero]
    have h4 : p (base k) * (v m)ᴴ
        = if base m = base k then (v m)ᴴ else 0 := by
      have h6 := congrArg Matrix.conjTranspose h5
      rw [Matrix.conjTranspose_mul, hpH] at h6
      rw [h6]
      by_cases hb : base m = base k
      · rw [if_pos hb, if_pos hb]
      · rw [if_neg hb, if_neg hb, Matrix.conjTranspose_zero]
    rw [h4]
    by_cases hb : base m = base k
    · rw [if_pos hb, if_pos ⟨hkl, hb⟩]
    · rw [if_neg hb, Matrix.mul_zero,
        if_neg fun hc => hb hc.2]
  · rw [if_neg hkl, Matrix.zero_mul, Matrix.mul_zero,
      if_neg fun hc => hkl hc.1]

end Assembly

end StarUnits
end NCG
