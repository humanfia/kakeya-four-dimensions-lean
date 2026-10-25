import Submission.Obl.k4_raw_native_atlas_normalization.Interface
import Submission.Obl.k4_raw_native_atlas_normalization.Kernel.NormalizeProblem
import Submission.Obl.k4_raw_native_atlas_normalization.Pruning
import Submission.Obl.k4_finite_width_output_exclusion.Interfaces
import Submission.Obl.k4_finite_width_output_exclusion.ChartTransport
import Submission.Obl.k4_quadratic_atlas_normalization.Thickness

namespace Submission.Obl.k4_raw_native_atlas_normalization

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

def kernelAtlas {p : Data} {k : ℕ} (a : Atlas p k) : Kernel.ChartSystem (p.W k) a.T where
  count := a.C
  world := a.γ
  block := a.j
  center := a.c
  speed := a.u
  frame := a.Q
  test := a.R
  assignment := a.A
  event := a.F

lemma samples_of_valid {p : Data} (hp : Valid p) :
    ∃ M D : ℕ, ∀ k, Kernel.SampleProblem (p.N k) (p.K k) M D (p.W k)
      (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k) := by
  obtain ⟨M, D, hf⟩ := hp.2.2.2.2.2.2.2.2.1
  refine ⟨M, D, fun k => ?_⟩
  obtain ⟨hW, hω, hωs, hw, hm⟩ := hf k
  refine ⟨hW, hω, hωs, fun b => (hw b).1, fun b => (hw b).2.1,
    fun b => (hw b).2.2.1, fun b => (hw b).2.2.2.1,
    fun b => (hw b).2.2.2.2.1, fun b => (hw b).2.2.2.2.2.1,
    fun b => (hw b).2.2.2.2.2.2.1,
    fun b => (hw b).2.2.2.2.2.2.2.1,
    fun b => (hw b).2.2.2.2.2.2.2.2.1,
    fun b => (hw b).2.2.2.2.2.2.2.2.2.1,
    fun b => (hw b).2.2.2.2.2.2.2.2.2.2.1,
    fun b => (hw b).2.2.2.2.2.2.2.2.2.2.2.1,
    fun b => (hw b).2.2.2.2.2.2.2.2.2.2.2.2, ?_⟩
  simpa only [Measure.restrict_apply_univ] using hm

lemma raw_of_samples {p : Data} (hN : ∀ k, 2 ≤ p.N k) (hNt : Tendsto p.N atTop atTop)
    (hK : (∀ k, 1 ≤ p.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε)
    (hL : 0 < p.L) (hd : 0 < p.d) (hd1 : p.d < 1) (hS : 0 < p.S) (hη : 0 < p.η)
    {M D : ℕ} (hs : ∀ k, Kernel.SampleProblem (p.N k) (p.K k) M D (p.W k)
      (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k)) : Raw p := by
  refine ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, M, D, fun k => ?_⟩
  have s := hs k
  refine ⟨s.card, s.weight_nonneg, s.weight_sum, fun b =>
    ⟨s.prob b, s.scale_pos b, s.scale_le b, s.scale_inv_le b, s.deg b, s.coeff b,
      s.prior b, s.event_meas b, s.event_time b, s.event_bdd b, s.event_fmt b,
      s.native b, s.lower b⟩, ?_⟩
  simpa only [Measure.restrict_apply_univ] using s.mass

lemma known_mono {p : Data} {k M M' D D' : ℕ} {κ κ' r : ℝ} {a : Atlas p k}
    (ha : a.KnownAt M D κ r) (hN : 1 ≤ p.N k) (hM : M ≤ M') (hD : D ≤ D')
    (hκ : 0 < κ) (hκ' : κ ≤ κ') (hB : ∀ b, 0 ≤ p.B k b) :
    a.KnownAt M' D' κ' r := by
  refine ⟨⟨ha.1.1.trans (pow_le_pow_right₀ hN hM), ha.1.2.1, fun b => ?_,
    (ENNReal.ofReal_le_ofReal (inv_anti₀ hκ hκ')).trans ha.1.2.2.2⟩,
    fun γ o => (ha.2 γ o).trans hκ'⟩
  exact Submission.Obl.k4_quadratic_atlas_normalization.chart_mono hN hM hD hκ hκ'
    (hB _) (ha.1.2.2.1 b) id

lemma known_geometry {p : Data} {k M D : ℕ} {κ r : ℝ} {a : Atlas p k}
    (ha : a.KnownAt M D κ r) : (kernelAtlas a).Geometry (p.N k) κ M D := by
  refine ⟨ha.1.1, ha.1.2.1, fun b => ?_⟩
  obtain ⟨hdet, hcu, hQ, hsize, _, _, hA, _, hfmt, hwhole, _⟩ := ha.1.2.2.1 b
  exact ⟨hdet, hcu, hQ, hsize, hA, fun i => (hfmt i).1,
    fun l hl => ⟨(hwhole l hl).1, (hwhole l hl).2.1⟩⟩

/-- The affine trajectory equivalence used by the certificate. -/
def trajectoryEquiv {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C)
    (hdet : (a.Q b).det ≠ 0) : Trajectory ≃ᵐ Trajectory :=
  (MeasurableEquiv.refl ℕ).prodCongr
    (((kernelAtlas a).frameOf b).normHomeomorph ((kernelAtlas a).frameOf_q_pos b).ne'
      (isUnit_iff_ne_zero.mpr hdet)).toMeasurableEquiv

lemma trajectoryEquiv_planar {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C)
    (hdet : (a.Q b).det ≠ 0) (l : Trajectory) (t : ℝ) :
    y (trajectoryEquiv a b hdet l) t = Matrix.toEuclideanLin (a.Q b)⁻¹
      (y l ((a.j b : ℝ) / (2 : ℝ) ^ a.T + t / (2 : ℝ) ^ a.T) - a.c b -
        ((a.j b : ℝ) / (2 : ℝ) ^ a.T + t / (2 : ℝ) ^ a.T) • a.u b) := by
  have hq : ((kernelAtlas a).frameOf b).q ≠ 0 := ((kernelAtlas a).frameOf_q_pos b).ne'
  have ht : ((((a.j b : ℝ) / (2 : ℝ) ^ a.T + t / (2 : ℝ) ^ a.T) -
      ((kernelAtlas a).frameOf b).t₀) / ((kernelAtlas a).frameOf b).q) = t := by
    dsimp [Kernel.ChartSystem.frameOf, kernelAtlas]
    field_simp
    ring
  have h := ((kernelAtlas a).frameOf b).planarPoint_normTraj hq l
    ((a.j b : ℝ) / (2 : ℝ) ^ a.T + t / (2 : ℝ) ^ a.T)
  rw [ht] at h
  exact h

lemma trajectoryEquiv_hidden {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C)
    (hdet : (a.Q b).det ≠ 0) (l : Trajectory) (t : ℝ) :
    x (trajectoryEquiv a b hdet l) t 3 =
      x l ((a.j b : ℝ) / (2 : ℝ) ^ a.T + t / (2 : ℝ) ^ a.T) 3 := by
  change (l.2 2 + ((a.j b : ℝ) / (2 : ℝ) ^ a.T) * l.2 5) +
      t * ((1 / (2 : ℝ) ^ a.T) * l.2 5) =
    l.2 2 + ((a.j b : ℝ) / (2 : ℝ) ^ a.T + t / (2 : ℝ) ^ a.T) * l.2 5
  ring

lemma normalized_test_identity {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (b : Fin a.C) (z : Fin 4 → ℝ) :
    MvPolynomial.eval z ((kernelAtlas a).normNative (δ (p.N k) r) b) =
      MvPolynomial.eval
        ![(a.j b : ℝ) / (2 : ℝ) ^ a.T + z 0 / (2 : ℝ) ^ a.T,
          (a.c b) 0 + ((a.j b : ℝ) / (2 : ℝ) ^ a.T + z 0 / (2 : ℝ) ^ a.T) * (a.u b) 0 +
            (a.Q b) 0 0 * z 1 + (a.Q b) 0 1 * z 2,
          (a.c b) 1 + ((a.j b : ℝ) / (2 : ℝ) ^ a.T + z 0 / (2 : ℝ) ^ a.T) * (a.u b) 1 +
            (a.Q b) 1 0 * z 1 + (a.Q b) 1 1 * z 2, z 3] (a.R b) / δ (p.N k) r := by
  have he : (fun i => MvPolynomial.eval z (((kernelAtlas a).frameOf b).unsubst i)) =
      ![(a.j b : ℝ) / (2 : ℝ) ^ a.T + z 0 / (2 : ℝ) ^ a.T,
        (a.c b) 0 + ((a.j b : ℝ) / (2 : ℝ) ^ a.T + z 0 / (2 : ℝ) ^ a.T) * (a.u b) 0 +
          (a.Q b) 0 0 * z 1 + (a.Q b) 0 1 * z 2,
        (a.c b) 1 + ((a.j b : ℝ) / (2 : ℝ) ^ a.T + z 0 / (2 : ℝ) ^ a.T) * (a.u b) 1 +
          (a.Q b) 1 0 * z 1 + (a.Q b) 1 1 * z 2, z 3] := by
    funext i
    fin_cases i <;>
      simp [Kernel.Frame.unsubst, kernelAtlas, Kernel.ChartSystem.frameOf] <;> ring <;> simp
  simp only [Kernel.ChartSystem.normNative, Kernel.Frame.normTest, MvPolynomial.smul_eval,
    Kernel.eval_bind₁', he]
  simp only [div_eq_mul_inv]
  exact mul_comm _ _

end
end Submission.Obl.k4_raw_native_atlas_normalization
