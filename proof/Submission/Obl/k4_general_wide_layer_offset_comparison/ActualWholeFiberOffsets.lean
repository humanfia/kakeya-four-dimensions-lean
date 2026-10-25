import Submission.Obl.k4_general_wide_layer_offset_comparison.WideOffsetNumerics
import Submission.Obl.k4_critical_intercept_concentration.CriticalScales

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ActualWholeFiberOffsets.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set Filter MvPolynomial

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Uniform quantitative return of the long projected comparison to one
constant on each WHOLE original true fiber. All mesh and short-domain
inequalities follow from the actual true atlas and the fixed scale gaps. -/
theorem eventually_wholeFiber_offsets (hp : p.Valid)
    {r u m C : ℝ} (hr : 0 < r) (hu : 0 < u) (hC : 0 ≤ C)
    (hm : (p.κ + p.ℓ) * r < m) (hgap : (C + 1 + p.ℓ) * u < p.κ * r)
    (H : ℕ → ℝ) (hH : ∀ k, 2 ≤ H k) (hKH : ∀ k, p.K k ≤ H k)
    (hHs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε) :
    ∀ᶠ k in atTop, ∀ R : ℝ, p.AtDepth k r R →
      ∀ h g b : ℝ, 0 < h → 0 < g → 0 < b → h * g = b →
      p.N k ^ (-p.ℓ * (r + u)) / H k ≤ b → g ≤ H k * p.N k ^ (-p.ℓ * r) →
      ∀ (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) (ω : α × ℝ),
        ω.1 ∈ p.B k r Q → ω.2 ∈ block (p.T k r) (p.j k r Q) →
        ⌊p.b k ω.1 0 / p.N k ^ (-m)⌋ = tag 1 →
        ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = tag 0 →
      ∀ G₀ G₁ : MvPolynomial (Fin 2) ℝ, G₀.totalDegree ≤ 2 → G₁.totalDegree ≤ 2 →
      (∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
        let D := p.domainCode k h g b ω
        |eval (fun i => y i)
          (projectedChartPolynomial G₁ (domainTime h D) (32 * h)
            (domainIntercept h g b D) (domainVelocity g D) (32 * b) -
          projectedChartPolynomial G₀ (domainTime h D) (32 * h)
            (domainIntercept h g b D) (domainVelocity g D) (32 * b))| ≤
          4 * H k * p.N k ^ (-r) * p.N k ^ (C * u)) →
      ∀ t₀ ∈ block (p.T k r) (p.j k r Q),
        let z₀ := p.trueFiberPoint k r m Q tag t₀
        let offset := eval ![z₀ 0, z₀ 2] G₁ - eval ![z₀ 0, z₀ 2] G₀
        ∀ z ∈ p.trueFiberBox k r m (H k) Q tag,
          |eval ![z 0, z 2] G₁ - eval ![z 0, z 2] G₀ - offset| ≤ p.N k ^ (-r - u) := by
  have hH1 : ∀ k, 1 ≤ H k := fun k => by linarith [hH k]
  have hK0 : ∀ k, 0 ≤ p.K k := fun k => zero_le_one.trans (hp.subpower.1 k)
  have hsmall := eventually_wide_fiber_small hp.scale hp.scale_limit hH1 hK0 hKH hHs
    (show p.ℓ * u < p.κ * r by nlinarith)
  have herror := eventually_wide_offset_error hp.scale hp.scale_limit hH1 hK0 hKH hHs hgap
  have hmesh := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [hp.scale k] : ∀ k, 1 ≤ p.N k) hp.scale_limit
    hp.subpower.1 hp.subpower.2 1
    (show -m < -(p.κ + p.ℓ) * r by linarith) (by norm_num : (0 : ℝ) ≤ 1)
  filter_upwards [hsmall, herror, hmesh] with k hsmallk herrork hmeshk
  intro R hat h g b hh hg hb hmove hblo hghi Q tag ω hl ht hz hv G₀ G₁ hG₀ hG₁ hbound t₀ ht₀
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hHp : 0 < H k := zero_lt_one.trans_le (hH1 k)
  have hK : 0 < p.K k := zero_lt_one.trans_le (hp.subpower.1 k)
  let q := (2 : ℝ) ^ (-(p.T k r : ℤ))
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hlength := Submission.Obl.k4_critical_intercept_concentration.time_length_comparison
    hN hK hat.1 hat.2.1
  have hqlo : p.N k ^ (-p.κ * r) ≤ p.K k * q := by
    simpa only [q, zpow_neg, zpow_natCast] using hlength.2
  have hqhi : q ≤ p.K k * p.N k ^ (-p.κ * r) := by
    have hh := (div_le_iff₀ hK).mp hlength.1
    simpa only [q, zpow_neg, zpow_natCast, mul_comm] using hh
  have hpowers : p.N k ^ (-(p.κ + p.ℓ) * r) =
      p.N k ^ (-p.κ * r) * p.N k ^ (-p.ℓ * r) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hχwidth : p.N k ^ (-m) ≤ q * p.N k ^ (-p.ℓ * r) := by
    apply (mul_le_mul_iff_right₀ hK).mp
    calc
      _ ≤ p.N k ^ (-(p.κ + p.ℓ) * r) := by simpa only [pow_one, one_mul] using hmeshk.le
      _ = p.N k ^ (-p.κ * r) * p.N k ^ (-p.ℓ * r) := hpowers
      _ ≤ (p.K k * q) * p.N k ^ (-p.ℓ * r) :=
        mul_le_mul_of_nonneg_right hqlo (by positivity)
      _ = _ := by ring
  have hχg : p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * r) :=
    hχwidth.trans (mul_le_of_le_one_left (by positivity) hq1)
  have hsm := hsmallk q b g hq.le hqhi hblo hghi
  have hfit := AtDepth.trueFiber_offset_bound p hat hN (hH k) (hK0 k) (hKH k)
    hh hg hb hmove hχwidth hχg Q tag hl ht hz hv hsm G₀ G₁ hG₀ hG₁
    (by positivity : 0 ≤ 4 * H k * p.N k ^ (-r) * p.N k ^ (C * u)) hbound ht₀
  dsimp only
  intro z hz
  exact (hfit z hz).trans (herrork q b g hq.le hqhi hblo hghi)

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
