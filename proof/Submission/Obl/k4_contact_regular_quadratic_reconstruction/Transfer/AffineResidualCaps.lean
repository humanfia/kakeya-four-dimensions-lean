/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c872eb1b,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/AffineResidualCaps.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the o238 one (k4_critical_switching_state_preparation). -/
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.ResidualBins
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.AffinePaletteCaps

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

open Set MeasureTheory Filter MvPolynomial Matrix
open Submission.Lib.K4ContactNormalization (affineBase)
open Submission.Lib.K4AffineMeshCaps (baseMesh)
open Submission.Obl.k4_critical_switching_state_preparation

/-- All prescribed affine base meshes and residual scalar bins inherit the
original native caps, uniformly over fixed-power-small sources and affine
base frames of fixed-power size. The original palette is unchanged. -/
theorem affine_residual_mesh_caps {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) (h1 : D.Basic) (h2 : D.Caps)
    {B A R : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ (τ : Measure (α × ℝ)), τ ≤ D.μ k →
      ENNReal.ofReal (D.N k ^ (-B)) ≤ τ univ → ∀ L : Fin 4 → ℝ,
      (∀ᵐ x ∂τ, |eval (D.x k x.1 x.2) (affineBase L) - (D.x k x.1 x.2) 3| ≤ 1 / 4) →
      ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ), M.det ≠ 0 →
      (∀ i, ∑ j, |M i j| ≤ D.N k ^ A) →
      ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
      let Z := fun x : α × ℝ => D.x k x.1 x.2 ∘ Fin.castSucc
      let code := fun x => baseMesh (D.N k ^ (-r))
        (Submission.Lib.K4AffineMeshCaps.affineBase M b (Z x))
      let scalar := fun x => ((D.x k x.1 x.2) 3 - eval (D.x k x.1 x.2) (affineBase L)) /
        D.N k ^ (-s)
      let C := 27 * (6 * D.K k + 5) * D.K k * |M.det|⁻¹ * D.N k ^ (-3 * r - D.d * s)
      (∀ (q : Fin 3 → ℤ) (j : ℤ), τ {x | code x = q ∧ ⌊scalar x⌋ = j} ≤ ENNReal.ofReal C) ∧
      (∀ (q : Fin 3 → ℤ) (j v₀ : ℤ),
        τ {x | code x = q ∧ ⌊scalar x⌋ = j ∧ ⌊D.b k x.1 3 / D.N k ^ (-v)⌋ = v₀} ≤
          ENNReal.ofReal C * D.π k {w : ℝ | ⌊w / D.N k ^ (-v)⌋ = v₀}) := by
  let rf : ℝ := R + (6 * B + 2) + A + 1
  let R' : ℝ := rf + R + 2
  have hrf : 1 ≤ rf := by dsimp [rf]; linarith
  have hR' : 1 < R' := by dsimp [R']; linarith
  have hRR' : R ≤ R' := by dsimp [R']; linarith
  have hRinv : R'⁻¹ ≤ R⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0 < R) hRR'
  have hR'inv : R'⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR'.le
  filter_upwards [fine_original_residual_bin_transfer D p h1 h2 hB, h2 R' hR'] with k htransfer hcapk
  intro τ hτ hmass L hparent M b hM hsize r s v hrl hru hs hsu hvl hvu
  dsimp only
  have hN : 0 < D.N k := lt_of_lt_of_le (by norm_num) (p.scale k)
  have hN₁ : 1 ≤ D.N k := le_trans (by norm_num) (p.scale k)
  have hK : 1 ≤ D.K k := p.subpower.1 k
  let δ : ℝ := D.N k ^ (-rf)
  let σ : ℝ := D.N k ^ (-r)
  let Z := fun x : α × ℝ => D.x k x.1 x.2 ∘ Fin.castSucc
  let C₀ : ℝ := (6 * D.K k + 5) * D.K k * D.N k ^ (-D.d * s)
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN _
  have hσ : 0 < σ := Real.rpow_pos_of_pos hN _
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hresolve (i : Fin 3) : (∑ j, |M i j| * δ) ≤ σ := by
    rw [← Finset.sum_mul]
    calc
      _ ≤ D.N k ^ A * δ := mul_le_mul_of_nonneg_right (hsize i) hδ.le
      _ = D.N k ^ (A - rf) := by dsimp [δ]; rw [← Real.rpow_add hN]; rfl
      _ ≤ σ := Real.rpow_le_rpow_of_exponent_le hN₁ (by dsimp [rf]; linarith)
  have hnow := hcapk rf s v (hR'inv.trans hrf) (by dsimp [R']; linarith) hs
    (hsu.trans hRR') (hRinv.trans hvl) (hvu.trans hRR')
  have he (u : ℝ) : (D.N k ^ (-u)) ^ (3 : ℕ) * D.N k ^ (-D.d * s) =
      D.N k ^ (-3 * u - D.d * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1
    ring
  have hcase (angular : Bool) (q : Fin 3 → ℤ) (j v₀ : ℤ) :
      τ {x | baseMesh σ (Submission.Lib.K4AffineMeshCaps.affineBase M b (Z x)) = q ∧
        ⌊((D.x k x.1 x.2) 3 - eval (D.x k x.1 x.2) (affineBase L)) / D.N k ^ (-s)⌋ = j ∧
        (if angular then ⌊D.b k x.1 3 / D.N k ^ (-v)⌋ = v₀ else True)} ≤
      ENNReal.ofReal (27 * (6 * D.K k + 5) * D.K k * |M.det|⁻¹ *
        D.N k ^ (-3 * r - D.d * s)) *
        (if angular then D.π k {w : ℝ | ⌊w / D.N k ^ (-v)⌋ = v₀} else 1) := by
    let G : Set (α × ℝ) := {x | if angular then
      ⌊D.b k x.1 3 / D.N k ^ (-v)⌋ = v₀ else True}
    let Γ : ENNReal := if angular then D.π k {w : ℝ | ⌊w / D.N k ^ (-v)⌋ = v₀} else 1
    let condition := fun x : α × ℝ =>
      ⌊((D.x k x.1 x.2) 3 - eval (D.x k x.1 x.2) (affineBase L)) / D.N k ^ (-s)⌋ = j ∧ x ∈ G
    letI : IsProbabilityMeasure (D.π k) := (h1 k).2.2.1
    have hΓ : Γ ≠ ⊤ := by dsimp [Γ]; split_ifs <;> finiteness
    have hfine (qf : Fin 3 → ℤ) :
        τ {x | baseMesh δ (Z x) = qf ∧ condition x} ≤ ENNReal.ofReal (C₀ * δ ^ 3) * Γ := by
      have hnat (a : ℤ) : D.μ k {x | x ∈ G ∧ D.z k (D.N k) rf x = qf ∧
          ⌊eval (D.x k x.1 x.2) (D.P k) / D.N k ^ (-s)⌋ = a} ≤
          ENNReal.ofReal (D.K k * D.N k ^ (-3 * rf - D.d * s)) * Γ := by
        cases angular
        · simpa only [G, Γ, mem_setOf_eq, Bool.false_eq_true, ite_false,
            true_and, mul_one, eq_self_iff_true, ite_true] using hnow.2.1 true qf a
        · have hsub : {x | x ∈ G ∧ D.z k (D.N k) rf x = qf ∧
              ⌊eval (D.x k x.1 x.2) (D.P k) / D.N k ^ (-s)⌋ = a} ⊆
              {x | D.z k (D.N k) rf x = qf ∧
                ⌊eval (D.x k x.1 x.2) (D.P k) / D.N k ^ (-s)⌋ = a ∧
                ⌊D.b k x.1 3 / D.N k ^ (-v)⌋ = v₀} := by
            intro x hx
            exact ⟨hx.2.1, hx.2.2, by
              simpa only [G, mem_setOf_eq, eq_self_iff_true, ite_true] using hx.1⟩
          have hh := (measure_mono hsub).trans (hnow.2.2 true qf a v₀)
          simpa only [Γ, eq_self_iff_true, ite_true] using hh
      have ht := htransfer τ hτ hmass L hparent rf s hs
        (by dsimp [rf]; linarith) G qf
        (ENNReal.ofReal (D.K k * D.N k ^ (-3 * rf - D.d * s)) * Γ) hnat j
      have hscalar : ENNReal.ofReal (6 * D.K k + 5) *
          (ENNReal.ofReal (D.K k * D.N k ^ (-3 * rf - D.d * s)) * Γ) =
          ENNReal.ofReal (C₀ * δ ^ 3) * Γ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 6 * D.K k + 5)]
        congr 2
        dsimp [C₀, δ]
        rw [← he]
        ring
      rw [hscalar] at ht
      have hsub : {x | baseMesh δ (Z x) = qf ∧ condition x} ⊆
          {x | x ∈ G ∧ D.z k (D.N k) rf x = qf ∧
            ⌊((D.x k x.1 x.2) 3 - eval (D.x k x.1 x.2) (affineBase L)) /
              D.N k ^ (-s)⌋ = j} := by
        intro x hx
        refine ⟨hx.2.2, ?_, hx.2.1⟩
        rw [data_z_eq_cell]
        exact hx.1
      exact (measure_mono hsub).trans ht
    have hbound := affine_mesh_cell_cap_with_palette τ Z condition M b hM
      hδ hσ hC₀ Γ hΓ hresolve hfine q
    have hfactor : 27 * C₀ * |M.det|⁻¹ * σ ^ 3 =
        27 * (6 * D.K k + 5) * D.K k * |M.det|⁻¹ * D.N k ^ (-3 * r - D.d * s) := by
      dsimp [C₀, σ]
      rw [← he]
      ring
    rw [hfactor] at hbound
    exact hbound
  constructor
  · intro q j
    simpa using hcase false q j 0
  · intro q j v₀
    simpa using hcase true q j v₀

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
