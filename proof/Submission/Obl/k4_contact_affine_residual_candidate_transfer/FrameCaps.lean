import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameLaw
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.NormalizedCaps

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory Filter MvPolynomial Matrix
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4AffineMeshCaps (baseMesh)
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

namespace Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable (f : Frame D k s₀ U')

def baseCode (r : ℝ) (p : α × ℝ) : Fin 3 → ℤ :=
  baseMesh (D.N k ^ (-r)) (point (f.coeff p.1) p.2 ∘ Fin.castSucc)

def hiddenCode (s : ℝ) (p : α × ℝ) : ℤ :=
  ⌊point (f.coeff p.1) p.2 3 / D.N k ^ (-s)⌋

def velocityCode (v : ℝ) (p : α × ℝ) : ℤ :=
  ⌊f.coeff p.1 3 / D.N k ^ (-v)⌋

theorem baseCode_toChart (r : ℝ) (p : α × ℝ) :
    f.baseCode r (f.toChart p) =
      baseMesh (D.N k ^ (-r))
        (Submission.Lib.K4AffineMeshCaps.affineBase
          (contactFrameMatrix f.t₀ f.q₀ f.Z₀) (contactFrameOffset f.t₀ f.q₀ f.Z₀ f.Y₀)
          (D.x k p.1 p.2 ∘ Fin.castSucc)) := by
  unfold baseCode
  change baseMesh _ (point (f.coeff p.1) ((p.2 - f.t₀) / f.q₀) ∘ Fin.castSucc) = _
  rw [f.point_coeff_base, contactBaseFrame_eq_affine]
  rfl

theorem hiddenCode_toChart (hN : 0 < D.N k) (s : ℝ) (p : α × ℝ) :
    f.hiddenCode s (f.toChart p) =
      ⌊((D.x k p.1 p.2) 3 - eval (D.x k p.1 p.2) (affineBase (f.pal 0 f.i₀ f.u₀))) /
        D.N k ^ (-(s₀ + s))⌋ := by
  unfold hiddenCode
  change ⌊point (f.coeff p.1) ((p.2 - f.t₀) / f.q₀) 3 / D.N k ^ (-s)⌋ = _
  rw [f.point_coeff_hidden, div_div]
  have hden : f.a₀ * D.N k ^ (-s) = D.N k ^ (-(s₀ + s)) := by
    rw [a₀, f.depth_zero, ← Real.rpow_add hN]
    congr 1
    ring
  rw [hden]

theorem velocityCode_toChart (v : ℝ) (p : α × ℝ) :
    f.velocityCode v (f.toChart p) = ⌊D.b k p.1 3 / D.N k ^ (-v)⌋ := rfl

/-- Original mesh caps recode exactly through the frame. No mass or palette
factor is changed by the deterministic time-coordinate bookkeeping. -/
theorem resμ_code_cap (hN : 0 < D.N k) (hb : Measurable (D.b k))
    (angular : Bool) (r s v : ℝ) (q : Fin 3 → ℤ) (j v₀ : ℤ) (C : ENNReal)
    (hcap : (f.scale⁻¹ • (D.μ k).restrict f.core) {p |
      baseMesh (D.N k ^ (-r))
        (Submission.Lib.K4AffineMeshCaps.affineBase
          (contactFrameMatrix f.t₀ f.q₀ f.Z₀) (contactFrameOffset f.t₀ f.q₀ f.Z₀ f.Y₀)
          (D.x k p.1 p.2 ∘ Fin.castSucc)) = q ∧
      ⌊((D.x k p.1 p.2) 3 - eval (D.x k p.1 p.2) (affineBase (f.pal 0 f.i₀ f.u₀))) /
        D.N k ^ (-(s₀ + s))⌋ = j ∧
      (if angular then ⌊D.b k p.1 3 / D.N k ^ (-v)⌋ = v₀ else True)} ≤ C) :
    f.resμ {p | f.baseCode r p = q ∧ f.hiddenCode s p = j ∧
      (if angular then f.velocityCode v p = v₀ else True)} ≤ C := by
  have hbc := f.measurable_coeff hb
  have hcode : Measurable (f.baseCode r) := by
    unfold baseCode baseMesh Submission.Lib.K4MovingMeshBoxes.baseMesh point
    fun_prop
  have hhidden : Measurable (f.hiddenCode s) := by
    unfold hiddenCode point
    fun_prop
  have hvelocity : Measurable (f.velocityCode v) := by
    unfold velocityCode
    fun_prop
  have hang : MeasurableSet {p : α × ℝ | if angular then f.velocityCode v p = v₀ else True} := by
    cases angular
    · simp
    · exact measurableSet_eq_fun hvelocity measurable_const
  have hE : MeasurableSet {p | f.baseCode r p = q ∧ f.hiddenCode s p = j ∧
      (if angular then f.velocityCode v p = v₀ else True)} :=
    (measurableSet_eq_fun hcode measurable_const).inter
      ((measurableSet_eq_fun hhidden measurable_const).inter hang)
  rw [resμ, Measure.smul_apply, smul_eq_mul, Measure.map_apply f.measurable_toChart hE]
  have heq : f.toChart ⁻¹' {p | f.baseCode r p = q ∧ f.hiddenCode s p = j ∧
      (if angular then f.velocityCode v p = v₀ else True)} =
      {p | baseMesh (D.N k ^ (-r))
        (Submission.Lib.K4AffineMeshCaps.affineBase
          (contactFrameMatrix f.t₀ f.q₀ f.Z₀) (contactFrameOffset f.t₀ f.q₀ f.Z₀ f.Y₀)
          (D.x k p.1 p.2 ∘ Fin.castSucc)) = q ∧
        ⌊((D.x k p.1 p.2) 3 - eval (D.x k p.1 p.2) (affineBase (f.pal 0 f.i₀ f.u₀))) /
          D.N k ^ (-(s₀ + s))⌋ = j ∧
        (if angular then ⌊D.b k p.1 3 / D.N k ^ (-v)⌋ = v₀ else True)} := by
    ext p
    simp only [mem_preimage, mem_setOf_eq, f.baseCode_toChart,
      f.hiddenCode_toChart hN, f.velocityCode_toChart]
  rw [heq]
  simpa only [Measure.smul_apply, smul_eq_mul] using hcap

end Frame

/-- All normalized frame caps hold on one eventual sample set, uniformly
over every prepared frame satisfying the original-source mass and reference
comparisons. -/
theorem eventual_frame_caps {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) (h1 : D.Basic) (h2 : D.Caps)
    {B A R s₀ U' : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hR : 1 < R) (hs₀ : 0 ≤ s₀) :
    ∀ᶠ k in atTop, ∀ f : Frame D k s₀ U', D.ν k f.parentSet ≠ 0 →
      ENNReal.ofReal (D.N k ^ (-B)) ≤ ((D.μ k).restrict f.core) univ →
      (∀ᵐ x ∂(D.μ k).restrict f.core,
        |eval (D.x k x.1 x.2) (affineBase (f.pal 0 f.i₀ f.u₀)) - (D.x k x.1 x.2) 3| ≤ 1 / 4) →
      (∀ i, ∑ j, |contactFrameMatrix f.t₀ f.q₀ f.Z₀ i j| ≤ D.N k ^ A) →
      ∀ J : ℝ, 0 ≤ J →
        |(contactFrameMatrix f.t₀ f.q₀ f.Z₀).det|⁻¹ * D.N k ^ (-D.d * s₀) ≤
          J * (f.q₀ * (D.ν k).real f.parentSet) →
      ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
      let C := 27 * (6 * D.K k + 5) * D.K k * J * D.N k ^ (-3 * r - D.d * s)
      (∀ (q : Fin 3 → ℤ) (j : ℤ),
        f.resμ {x | f.baseCode r x = q ∧ f.hiddenCode s x = j} ≤ ENNReal.ofReal C) ∧
      (∀ (q : Fin 3 → ℤ) (j v₀ : ℤ),
        f.resμ {x | f.baseCode r x = q ∧ f.hiddenCode s x = j ∧ f.velocityCode v x = v₀} ≤
          ENNReal.ofReal C * D.π k {w : ℝ | ⌊w / D.N k ^ (-v)⌋ = v₀}) := by
  filter_upwards [normalized_affine_residual_mesh_caps D p h1 h2 hB hA hR hs₀] with k hk
  intro f hparent hmass hfit hsize J hJ href r s v hrl hru hs hsu hvl hvu
  dsimp only
  letI : IsProbabilityMeasure (D.ν k) := (h1 k).2.1
  have hN : 0 < D.N k := by linarith [p.scale k]
  let W := f.q₀ * (D.ν k).real f.parentSet
  have hW : 0 < W := mul_pos f.q₀_pos
    (ENNReal.toReal_pos hparent (measure_ne_top (D.ν k) f.parentSet))
  have hscale : f.scale⁻¹ = ENNReal.ofReal W⁻¹ := by
    rw [f.scale_eq_ofReal, ENNReal.ofReal_inv_of_pos hW]
  have hcap := hk ((D.μ k).restrict f.core) Measure.restrict_le_self hmass
    (f.pal 0 f.i₀ f.u₀) hfit (contactFrameMatrix f.t₀ f.q₀ f.Z₀)
    (contactFrameOffset f.t₀ f.q₀ f.Z₀ f.Y₀)
    (det_contactFrameMatrix_ne_zero _ _ f.q₀_pos.ne') hsize W J hW hJ href
    r s v hrl hru hs hsu hvl hvu
  constructor
  · intro q j
    have hh := f.resμ_code_cap hN (h1 k).1 false r s v q j 0 _
      (by simpa only [hscale, Bool.false_eq_true, ite_false, and_true] using hcap.1 q j)
    simpa using hh
  · intro q j v₀
    have hh := f.resμ_code_cap hN (h1 k).1 true r s v q j v₀ _
      (by simpa only [hscale, ite_true] using hcap.2 q j v₀)
    simpa using hh

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
