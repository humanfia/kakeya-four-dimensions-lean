/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeOriginalCaps.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeCoordinates
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeFrameCaps
import Submission.Obl.k4_subcritical_corrected_scalar_charts.OffsetCaps
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

def affineField (L : Fin 4 → ℝ) (z : Fin 3 → ℝ) : ℝ :=
  L 0 + L 1 * z 0 + L 2 * z 1 + L 3 * z 2

theorem affineField_lipschitz (L : Fin 4 → ℝ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hL : ∀ i : Fin 3, |L i.succ| ≤ M)
    {z w : Fin 3 → ℝ} (hdist : ∀ i, |z i - w i| ≤ δ) :
    |affineField L z - affineField L w| ≤ 3 * M * δ := by
  have heq : affineField L z - affineField L w = ∑ i : Fin 3, L i.succ * (z i - w i) := by
    simp [Fin.sum_univ_three, affineField]
    ring
  rw [heq]
  calc
    _ ≤ ∑ i : Fin 3, |L i.succ * (z i - w i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, M * δ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hL i) (hdist i) (abs_nonneg _) hM
    _ = _ := by simp; ring

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original hidden/native joint cap gives a pure base cap on each whole
original fitted witness, using its genuine bounded affine entry. -/
theorem NativeLevel.original_base_cell_cap (h : cfg.Prepared) {k : ℕ} {s δ V : ℝ}
    (a : cfg.NativeLevel k s) (hδ : 0 < δ) (hV : 0 ≤ V)
    (hmesh : 108 * cfg.K k ^ 4 * δ ≤ cfg.N k ^ (-s))
    (hcap : ∀ q n, cfg.μ k {p | baseMesh δ (originalBase (cfg.b k p.1) p.2) = q ∧
      ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / (cfg.N k ^ (-s))⌋ = n} ≤
        ENNReal.ofReal (V * δ ^ 3))
    (i : Fin (cfg.n k s)) (q : Fin 3 → ℤ) :
    cfg.μ k {p | baseMesh δ (originalBase (cfg.b k p.1) p.2) = q ∧
      p ∈ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)} ≤
      ENNReal.ofReal (((4 * cfg.K k + 6) * V) * δ ^ 3) := by
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos (by linarith [h.scale k]) _
  have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  let x := fun p : α × ℝ => originalBase (cfg.b k p.1) p.2
  let X := fun p : α × ℝ => cfg.b k p.1 2 + p.2 * cfg.b k p.1 5
  let o := fun p : α × ℝ => affineField (a.L i) (x p)
  let center := affineField (a.L i) (fun e => δ * (q e : ℝ))
  have hosc (p : α × ℝ) (hp : baseMesh δ (x p) = q) :
      |o p - center| ≤ cfg.N k ^ (-s) := by
    apply (affineField_lipschitz (a.L i) (by positivity : 0 ≤ 36 * cfg.K k ^ 4)
      hδ.le (a.slope i) ?_).trans
      (by convert hmesh using 1 <;> ring)
    intro e
    have he := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hδ (x p e)
    have hcode : ⌊x p e / δ⌋ = q e := congrFun hp e
    simpa only [hcode] using he
  have hb := offset_band_cell_cap (cfg.μ k) (fun p => baseMesh δ (x p)) X o
    (fun _ => True) q ha hK (ENNReal.ofReal (V * δ ^ 3))
    (by intro n; simpa only [and_true] using hcap q n)
    (by intro p hp _; exact hosc p hp)
  have hsub : {p | baseMesh δ (x p) = q ∧
      p ∈ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)} ⊆
      {p | baseMesh δ (x p) = q ∧ |X p - o p| ≤ cfg.K k * cfg.N k ^ (-s) ∧ True} := by
    intro p hp
    exact ⟨hp.1, a.fit i p.1 hp.2.1 p.2 hp.2.2, trivial⟩
  refine (measure_mono hsub).trans (hb.trans_eq ?_)
  rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ 4 * cfg.K k + 6)]
  congr 1
  ring

/-- The preceding original cap transports to normalized native cells with the
matching h⁴ factor in the density and in the stored witness floor. -/
theorem NativeLevel.normalized_cell_cap (h : cfg.Prepared) {k : ℕ} {s δ σ V : ℝ}
    (a : cfg.NativeLevel k s) (hδ : 0 < δ) (hσ : 0 < σ) (hV : 0 ≤ V)
    (hmesh : 108 * cfg.K k ^ 4 * δ ≤ cfg.N k ^ (-s))
    (hcap : ∀ q n, cfg.μ k {p | baseMesh δ (originalBase (cfg.b k p.1) p.2) = q ∧
      ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / (cfg.N k ^ (-s))⌋ = n} ≤
        ENNReal.ofReal (V * δ ^ 3))
    (i : Fin (cfg.n k s))
    (hresolve : ∀ e, (∑ j, |nativeFrameMatrix (cfg.timeLength k s)
      (cfg.c k s i 1) (-cfg.c k s i 3 - cfg.c k s i 4 * cfg.c k s i 1)
      (cfg.c k s i 4) e j| * δ) ≤ σ)
    (q : Fin 3 → ℤ) :
    ((cfg.μ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)))
      {p | baseMesh σ (atlasFrame (cfg.timeLength k s) (cfg.nativeMidpoint k s i)
        (cfg.c k s i) (originalBase (cfg.b k p.1) p.2)) = q} ≤
      ENNReal.ofReal (27 * ((4 * cfg.K k + 6) * V) * cfg.timeLength k s ^ 4 * σ ^ 3) := by
  have hb := (h.basic k).1
  have hx : Measurable (fun p : α × ℝ => originalBase (cfg.b k p.1) p.2) := by
    unfold originalBase
    fun_prop
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  exact native_frame_restrict_cell_cap (cfg.μ k)
    (fun p => originalBase (cfg.b k p.1) p.2) hx
    (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))
    hq hδ hσ (by have hK := h.subpower.1 k; positivity)
    (cfg.nativeMidpoint k s i) (cfg.c k s i 0)
    (cfg.c k s i 2 + cfg.c k s i 4 * cfg.c k s i 0) (cfg.c k s i 1)
    (-cfg.c k s i 3 - cfg.c k s i 4 * cfg.c k s i 1) (cfg.c k s i 4)
    hresolve (a.original_base_cell_cap h hδ hV hmesh hcap i) q

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
