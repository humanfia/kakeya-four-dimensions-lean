-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceParts
import Submission.Obl.k4_finite_affine_parent_sources.OriginalLabelGeometry
import Submission.Obl.k4_finite_affine_parent_sources.MajorAxisFullness

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Obl.k4_compatible_pair_frame_preparation.Construction

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

/-- The geometric budgets left after the original deficient-axis deletion
and the numerical calibration. They concern full old assignments. -/
structure TrackingGeometry (n : ℕ) (ℓ unit Nk L H : ℝ) : Prop where
  one_le : 1 ≤ H
  slack : 18 * p.κ ≤ H
  model_budget : 16 * H ^ 4 ≤ D.K
  parent_full : D.q₀ / H ≤ r₁ (p.frame D.parent)
  parent_area : |(p.frame D.parent).det| ≤ D.q₀ ^ 2 / (2 * H ^ 3)
  child_full : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
    ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
      (((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹) / H ≤ r₁ (p.frame (D.old s i))
  det_upper : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
    ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
      |(relativeVelocityFrame D.q₀ (((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹)
        D.D₀ (p.frame (D.old s i))).det| ≤ H * (Nk ^ (unit * L)) ^ (-ℓ * s)

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The parent chart supplies the four native coefficient bounds needed
by both the no-strip argument and the representative-centered shear. -/
theorem parent_native_coefficients
    (hD : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (l : Trajectory) (hl : l ∈ p.assigned D.parent) :
    |(D.frame Nk B).eb l 0| + |(D.frame Nk B).eb l 1| +
      |(D.frame Nk B).eb l 3| + |(D.frame Nk B).eb l 4| ≤ 18 * p.κ := by
  calc
    _ ≤ 6 * (3 * p.κ) := (D.frame Nk B).eb_coeff_bound D.q₀_pos l (3 * p.κ)
      (fun t ht => (D.parent_tube hp hD l hl t ht).1)
    _ = _ := by ring

/-- One active full old assignment has the exact tracking rows of the
source model. Its original-prior floor is used before normalization. -/
theorem track_at_of_geometric_budgets
    (hNk : 0 < Nk) (Mc : ℕ) (d₁ ρ gain ε unit τ h H : ℝ)
    (Hres : Fin W → Set Incidence)
    (hno : ¬MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world
      p.bin p.velocity p.frame p.assigned Hres)
    (hD : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hSres : D.S ⊆ Hres D.w₀)
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hτ : 0 < τ) (hτbudget : Nk ^ (-ρ * h * L - ε) ≤ τ)
    (hgain : gain ≤ h) (hupper : h ≤ 1 / 8)
    (hbias : 2 * p.κ ≤ Nk ^ Mc)
    (hrow : 36 * p.κ / (Nk ^ (ρ * h * L + ε) * Nk ^ (-h * L)) ≤ H)
    (n : ℕ) (hg : D.TrackingGeometry n ℓ unit Nk L H)
    (s : ℝ) (hslo : (n : ℝ)⁻¹ ≤ s) (hshi : s ≤ 1)
    (hdepth : D.i₀ ≤ D.depth s)
    (hroom : p.r (D.depth s) + 2 * h * L ≤ L)
    (i : Fin (p.activeCount D.Hm (D.depth s)))
    (hfloor : ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old s i)) ≤
      ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old s i))) :
    ∃ c : Fin 5 → ℝ, (∀ e, |c e| ≤ D.K) ∧
      ∀ l ∈ p.assigned (D.old s i), ∀ t ∈ IS (D.relT s) (D.relBin s i),
        |(exS (D.stage Nk L unit ν B).b l t) 1 - c 0 - t * c 1| ≤
          D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) ∧
        |(exS (D.stage Nk L unit ν B).b l t) 2 - c 2 - t * c 3 -
            c 4 * (exS (D.stage Nk L unit ν B).b l t) 1| ≤
          D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) * (Nk ^ (unit * L)) ^ (-ℓ * s) ∧
        |(D.stage Nk L unit ν B).b l 4 - c 3 - c 4 * (D.stage Nk L unit ν B).b l 3| ≤
          D.K * (Nk ^ (unit * L)) ^ (-ℓ * s) := by
  let b := D.old s i
  let Φ := D.frame Nk B
  have hw : p.world b = D.w₀ := (D.old_world s i).1
  have hκ : 0 ≤ p.κ := zero_le_one.trans hp.one_le_slack
  have hκH : p.κ ≤ H := by linarith [hg.slack]
  have hcoef18 (l : Trajectory) (hl : l ∈ p.assigned D.parent) :
      |Φ.eb l 0| ≤ 18 * p.κ ∧ |Φ.eb l 1| ≤ 18 * p.κ ∧
        |Φ.eb l 3| ≤ 18 * p.κ ∧ |Φ.eb l 4| ≤ 18 * p.κ := by
    have hc := D.parent_native_coefficients hp hD l hl
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith [abs_nonneg (Φ.eb l 0), abs_nonneg (Φ.eb l 1),
        abs_nonneg (Φ.eb l 3), abs_nonneg (Φ.eb l 4)]
  have hsub : p.assigned b ⊆ p.assigned D.parent :=
    D.old_assigned_subset hp hSo s hdepth i
  let V : Set Incidence := {z | z ∈ Hres (p.world b) ∧ z.1 ∈ p.assigned b ∧
    z.2 ∈ Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
      (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b))}
  obtain ⟨z₀, hzS, hzF⟩ := (D.old_world s i).2
  have hzA : z₀.1 ∈ p.assigned b := (hp.counted_support b z₀ hzF).2.1
  have hzV : z₀ ∈ V :=
    ⟨by simpa only [hw] using hSres hzS, hzA, (hp.counted_support b z₀ hzF).2.2.1⟩
  have hfloorV : ENNReal.ofReal
      (Nk ^ (-ρ * h * L - ε) / (2 : ℝ) ^ p.T (p.lev b)) *
      ν (p.world b) (p.assigned b) ≤ (ν (p.world b)).prod volume V := by
    have hf := D.residual_floor hp hτ (le_refl τ⁻¹) Hres hSres b hfloor
    have hwidth : Nk ^ (-ρ * h * L - ε) / (2 : ℝ) ^ p.T (p.lev b) ≤
        (((2 : ℝ) ^ p.T (p.lev b))⁻¹) / τ⁻¹ := by
      simpa only [div_eq_mul_inv, inv_inv, mul_comm] using
        mul_le_mul_of_nonneg_left hτbudget (by positivity : 0 ≤ ((2 : ℝ) ^ p.T (p.lev b))⁻¹)
    have hf' := (mul_le_mul' (ENNReal.ofReal_le_ofReal hwidth)
      (le_refl (ν D.w₀ (p.assigned b)))).trans hf
    simpa only [V, hw] using hf'
  have hparent : ∀ z ∈ V, ∀ e : Fin 2,
      |(WithLp.toLp 2 ![Φ.eb z.1 3, Φ.eb z.1 4]) e| ≤ 18 * p.κ := by
    intro z hz e
    have hc := hcoef18 z.1 (hsub hz.2.1)
    fin_cases e
    · simpa using hc.2.2.1
    · simpa using hc.2.2.2
  have hblockLength : ((2 : ℝ) ^ D.relT s)⁻¹ =
      (((2 : ℝ) ^ p.T (p.lev b))⁻¹) / Φ.F.q := by
    have hT := (D.old_bin_div hp hSo s hdepth i).1
    change ((2 : ℝ) ^ D.relT s)⁻¹ = (((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹) / D.q₀
    simp only [D.old_level s i, relT, q₀]
    rw [pow_sub₀ (2 : ℝ) two_ne_zero hT]
    field_simp
  have hblock : ∀ t ∈ IS (D.relT s) (D.relBin s i), Φ.F.t₀ + Φ.F.q * t ∈
      Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
        (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) := by
    intro t ht
    apply (D.old_relBin_mem hp hSo s hdepth i (D.t₀ + D.q₀ * t)).mpr
    have heq : (D.t₀ + D.q₀ * t - D.t₀) / D.q₀ = t :=
      Φ.tnorm_denorm D.q₀_pos.ne' t
    simpa only [heq] using ht
  have hupperParent : r₁ (p.frame D.parent) ≤ H * Φ.F.q := by
    exact hp.major_upper D.parent H hκH
  have hc := hcoef18 z₀.1 (hsub hzA)
  have hgeom := PFrame.original_label_geometric_rows hp hNk Mc d₁ ρ gain ε Hres hno
    D.parent b h hgain hupper (by show p.r (p.lev (D.old s i)) + 2 * h * L ≤ L; rw [D.old_level s i]; exact hroom)
    (prior_pos_of_valid hp hNk b) hbias V ⟨z₀, hzV⟩ (fun z hz => hz) hfloorV
    Φ (18 * p.κ) H ((Nk ^ (unit * L)) ^ (-ℓ * s)) (by positivity) hg.one_le hκH
    (by positivity) D.q₀_pos hD hparent (by convert hrow using 1 <;> ring)
    hg.parent_full hupperParent hg.parent_area (hg.child_full s hslo hshi i)
    (hg.det_upper s hslo hshi i) (D.relT s) (D.relBin s i) hblockLength hblock
    z₀.1 hzA ⟨hc.1.trans hg.slack, hc.2.1.trans hg.slack,
      hc.2.2.1.trans hg.slack, hc.2.2.2.trans hg.slack⟩
  exact tilted_label_with_model_slack Φ.eb (p.assigned b) (D.relT s) (D.relBin s i)
    (16 * H ^ 4) D.K ((Nk ^ (unit * L)) ^ (-ℓ * s)) hg.model_budget (by positivity) hgeom

/-- Choose all tracking coefficients at once, including harmless values
outside the model range. This is precisely the `SourceParts.models` tracking field. -/
theorem tracks_of_geometric_budgets
    (hNk : 0 < Nk) (Mc : ℕ) (d₁ ρ gain ε unit τ h H : ℝ)
    (Hres : Fin W → Set Incidence)
    (hno : ¬MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world
      p.bin p.velocity p.frame p.assigned Hres)
    (hD : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hSres : D.S ⊆ Hres D.w₀)
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hτ : 0 < τ) (hτbudget : Nk ^ (-ρ * h * L - ε) ≤ τ)
    (hgain : gain ≤ h) (hupper : h ≤ 1 / 8)
    (hbias : 2 * p.κ ≤ Nk ^ Mc)
    (hrow : 36 * p.κ / (Nk ^ (ρ * h * L + ε) * Nk ^ (-h * L)) ≤ H)
    (n : ℕ) (hg : D.TrackingGeometry n ℓ unit Nk L H)
    (hdepth : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → D.i₀ ≤ D.depth s)
    (hroom : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → p.r (D.depth s) + 2 * h * L ≤ L)
    (hfloor : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
      ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
        ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old s i)) ≤
          ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old s i))) :
    ∃ c, D.Tracks n ℓ unit Nk L ν B c := by
  classical
  let P := fun (s : ℝ) (i : Fin (p.activeCount D.Hm (D.depth s))) (c : Fin 5 → ℝ) =>
    (∀ e, |c e| ≤ D.K) ∧
      ∀ l ∈ p.assigned (D.old s i), ∀ t ∈ IS (D.relT s) (D.relBin s i),
        |(exS (D.stage Nk L unit ν B).b l t) 1 - c 0 - t * c 1| ≤
          D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) ∧
        |(exS (D.stage Nk L unit ν B).b l t) 2 - c 2 - t * c 3 -
            c 4 * (exS (D.stage Nk L unit ν B).b l t) 1| ≤
          D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) * (Nk ^ (unit * L)) ^ (-ℓ * s) ∧
        |(D.stage Nk L unit ν B).b l 4 - c 3 - c 4 * (D.stage Nk L unit ν B).b l 3| ≤
          D.K * (Nk ^ (unit * L)) ^ (-ℓ * s)
  have hex : ∀ s i, ∃ c, ((n : ℝ)⁻¹ ≤ s ∧ s ≤ 1) → P s i c := by
    intro s i
    by_cases hs : (n : ℝ)⁻¹ ≤ s ∧ s ≤ 1
    · obtain ⟨c, hc⟩ := D.track_at_of_geometric_budgets hp hNk Mc d₁ ρ gain ε unit τ h H
        Hres hno hD hSres hSo hτ hτbudget hgain hupper hbias hrow n hg s hs.1 hs.2
        (hdepth s hs.1 hs.2) (hroom s hs.1 hs.2) i (hfloor s hs.1 hs.2 i)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => False.elim (hs h)⟩
  let c := fun s i => Classical.choose (hex s i)
  refine ⟨c, fun s hslo hshi i => ?_⟩
  exact Classical.choose_spec (hex s i) ⟨hslo, hshi⟩

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
