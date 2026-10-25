-- Adapted from this LOT tree, o080/x0272 commit 4d767e4, Submission/Obl/k4_matching_geometric_path_cover/CoarseJetNeighbors.lean.
-- Adapted within this LOT tree from o040, session x0115, commit 561995983838,
-- Submission/Obl/k4_matching_refinement_exponent/CoarseJetNeighbors.lean. Existing provenance comments below are preserved.
import Submission.Obl.k4_matching_switching_target_certificate.CoarseProfiles
import Submission.Obl.k4_matching_switching_target_certificate.Neighbors
import Submission.Obl.k4_matching_homogeneous_records.Offsets

/-!
The analytic input is x0118's `Neighbors.arm_gap_at_level`, merged from the
same-obligation branch at eb3dbe4. The integer cutoff and its growth bound are
imported from accepted o055; they are not reproved here.
-/

open Set

namespace Submission.Obl.k4_matching_switching_target_certificate

open Submission.Obl.k4_matching_homogeneous_records
  (dyadicCenter offsetCutoff offsetCutoff_bound floor_sub_bound)

/-- The frozen gap assumptions imply a uniform integer-bin gap at any
recorded dyadic center, including a center at an arbitrarily chosen depth. -/
theorem center_jet_floor_gap {J : ℕ} (hJ : 1 ≤ J) {β : ℕ → ℝ}
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hk₀J : k₀ ≤ J) (hβ : β k₀ = 0)
    {N ε : ℝ} (hN : 1 ≤ N)
    {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ (J + 1 : ℕ) f (Ioo (-1 : ℝ) 2))
    (hg : ContDiffOn ℝ (J + 1 : ℕ) g (Ioo (-1 : ℝ) 2))
    (hfB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) f t| ≤ N ^ ε)
    (hgB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) g t| ≤ N ^ ε)
    {t a : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1)
    (h₀ : |f t - g t| ≤ N ^ (-1 + ε))
    (hgap : ∀ j : ℕ, 1 ≤ j → j ≤ J →
      |iteratedDeriv j f t - iteratedDeriv j g t| ≤ N ^ (-β j + ε))
    (h : ℕ) (hh : N ^ jetRadius J β a ≤ (2 : ℝ) ^ h)
    (j : ℕ) (hj : j ≤ J) :
    |Int.floor (N ^ jetAccuracy (jetRadius J β) j a *
        iteratedDeriv j f (dyadicCenter h t)) -
      Int.floor (N ^ jetAccuracy (jetRadius J β) j a *
        iteratedDeriv j g (dyadicCenter h t))| ≤ (offsetCutoff J N ε : ℤ) := by
  have hN0 : 0 < N := by linarith
  have hcenter := Submission.Obl.k4_matching_homogeneous_records.dyadicCenter_mem (h := h) ht
  have hdist : |dyadicCenter h t - t| ≤ N ^ (-jetRadius J β a) := by
    calc
      |dyadicCenter h t - t| ≤ ((2 : ℝ) ^ h)⁻¹ :=
        Submission.Obl.k4_matching_homogeneous_records.dyadicCenter_dist h t
      _ ≤ (N ^ jetRadius J β a)⁻¹ := inv_anti₀ (by positivity) hh
      _ = _ := (Real.rpow_neg hN0.le _).symm
  have hjet := arm_gap_at_level hJ hk₀ hk₀J hβ hN hf hg hfB hgB
    (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩) hcenter h₀ hgap ha.1 ha.2 hdist hj
  let w := N ^ jetAccuracy (jetRadius J β) j a
  have hw : 0 < w := by dsimp [w]; positivity
  have hcancel : w * N ^ (-jetAccuracy (jetRadius J β) j a) = 1 := by
    dsimp [w]
    rw [← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero]
  have hscaled : |w * iteratedDeriv j f (dyadicCenter h t) -
      w * iteratedDeriv j g (dyadicCenter h t)| ≤ 5 * N ^ ε := by
    rw [← mul_sub, abs_mul, abs_of_pos hw]
    calc
      w * |iteratedDeriv j f (dyadicCenter h t) - iteratedDeriv j g (dyadicCenter h t)| ≤
          w * (5 * N ^ ε * N ^ (-jetAccuracy (jetRadius J β) j a)) := by gcongr
      _ = 5 * N ^ ε * (w * N ^ (-jetAccuracy (jetRadius J β) j a)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  have hfloor := (floor_sub_bound (w * iteratedDeriv j f (dyadicCenter h t))
    (w * iteratedDeriv j g (dyadicCenter h t))).trans (add_le_add hscaled le_rfl)
  have hcut : 5 * N ^ ε + 1 ≤ (offsetCutoff J N ε : ℝ) := by
    calc
      5 * N ^ ε + 1 ≤ ((2 * (J + 2) : ℕ) : ℝ) * N ^ ε + 1 := by
        have hcoef : (5 : ℝ) ≤ ((2 * (J + 2) : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ 2 * (J + 2))
        gcongr
      _ ≤ _ := Nat.le_ceil _
  exact_mod_cast hfloor.trans hcut

/-- The exact scale of the recorded bins. -/
noncomputable def coarseJetScale (J : ℕ) (β : ℕ → ℝ) (N : ℝ) (q : ℕ) : ℕ → ℕ → ℝ :=
  fun v j => N ^ jetAccuracy (jetRadius J β) j ((v : ℝ) / (q : ℝ))

/-- The two colors of each retained event are neighbors in every coordinate
of its full coarse history. -/
theorem event_coarse_bin_gap {n₁ n₂ J k q : ℕ} (hJ : 1 ≤ J) (hq : 1 ≤ q) (hkq : k ≤ q)
    {β : ℕ → ℝ} {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hk₀J : k₀ ≤ J) (hβ : β k₀ = 0)
    {N ε : ℝ} (hN : 1 ≤ N)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (hf₁ : ∀ i, ContDiffOn ℝ (J + 1 : ℕ) (f₁ i) (Ioo (-1 : ℝ) 2))
    (hf₂ : ∀ i, ContDiffOn ℝ (J + 1 : ℕ) (f₂ i) (Ioo (-1 : ℝ) 2))
    (hB₁ : ∀ i t, t ∈ Icc (0 : ℝ) 1 → |iteratedDeriv (J + 1) (f₁ i) t| ≤ N ^ ε)
    (hB₂ : ∀ i t, t ∈ Icc (0 : ℝ) 1 → |iteratedDeriv (J + 1) (f₂ i) t| ≤ N ^ ε)
    (h : ℕ → ℕ)
    (hh : ∀ v, v ≤ k → N ^ jetRadius J β ((v : ℝ) / (q : ℝ)) ≤ (2 : ℝ) ^ h v)
    (x : (Fin n₁ × Fin n₂) × ℝ) (ht : x.2 ∈ Ico (0 : ℝ) 1)
    (h₀ : |f₁ x.1.1 x.2 - f₂ x.1.2 x.2| ≤ N ^ (-1 + ε))
    (hgap : ∀ j : ℕ, 1 ≤ j → j ≤ J →
      |iteratedDeriv j (f₁ x.1.1) x.2 - iteratedDeriv j (f₂ x.1.2) x.2| ≤ N ^ (-β j + ε)) :
    ∀ i, |coarseBinProfile f₁ f₂ h (coarseJetScale J β N q) k J x 0 i -
      coarseBinProfile f₁ f₂ h (coarseJetScale J β N q) k J x 1 i| ≤
        (offsetCutoff J N ε : ℤ) := by
  intro i
  have hv : (i.1 : ℕ) ≤ k := Nat.le_of_lt_succ i.1.isLt
  have ha : (i.1 : ℝ) / (q : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast (by omega : 0 < q))).mpr
      exact_mod_cast hv.trans hkq
  simpa only [coarseBinProfile, coarseJetScale, Fin.isValue, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false] using
    center_jet_floor_gap hJ hk₀ hk₀J hβ hN (hf₁ x.1.1) (hf₂ x.1.2)
      (hB₁ x.1.1) (hB₂ x.1.2) ht ha h₀ hgap (h i.1) (hh i.1 hv)
      i.2 (Nat.le_of_lt_succ i.2.isLt)

end Submission.Obl.k4_matching_switching_target_certificate
