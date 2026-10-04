import RenewalGeometry.Analysis.SobolevTorusBridge
open Filter Topology
namespace TT
def ip {N : Type*} [Fintype N] (u v : N → ℂ) : ℝ := (∑ i, star (u i) * v i).re
def mv {N : Type*} [Fintype N] (A : N → N → ℂ) (v : N → ℂ) : N → ℂ := fun i => ∑ j, A i j * v j
theorem continuous_ip_mv {N : Type*} [Fintype N] (v : N → ℂ) :
    Continuous fun p : (N → N → ℂ) × (N → ℂ) => ip (mv p.1 p.2) v := by
  unfold ip mv
  fun_prop
set_option maxHeartbeats 1000000 in
theorem tendsto_ip_mv {N : Type*} [Fintype N] {l : Filter ℝ} {B : ℝ → N → N → ℂ}
    {u : ℝ → N → ℂ} {B0 : N → N → ℂ} {u0 : N → ℂ} (v : N → ℂ) (hB : Tendsto B l (𝓝 B0))
    (hu : Tendsto u l (𝓝 u0)) :
    Tendsto (fun s => ip (mv (B s) (u s)) v) l (𝓝 (ip (mv B0 u0) v)) := by
  have h := (continuous_ip_mv v).tendsto (B0, u0)
  have h2 := hB.prodMk_nhds hu
  have h3 := h.comp h2
  exact h3
end TT
