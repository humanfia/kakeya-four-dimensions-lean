-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyAlternative.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.InsertionBudget
import Submission.WZ.Obl.wz_multiscale_finite_tower.ReferenceGain

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (coverScale coverScale_pos)

def PhysicalAlternatives (σ ω ζ h α κ η c : ℝ) : Prop :=
  ∀ d r s : ℝ, 0 < d → d ≤ 1 → 0 < r → 0 < s → d * r ≤ s →
    s ≤ c * r → r ≤ 1 → s / r ≤ d ^ h → ∀ y w : Space, ‖w‖ = 1 → ∀ n x v Y,
    PhysicalFrame d r s η y w n x v Y →
    ENNReal.ofReal (κ * r ^ 2 * volumeFactor σ ω (s / r) n * (s / r) ^ (-α)) ≤
      volume (⋃ i, Y i) ∨ PhysicalCover d r s ζ coverScale ω y w n x v Y

theorem HierarchyAnalysis.cover_alternative {σ ω ζ h α κ η c d θ g gap ρ : ℝ}
    {J k q : ℕ} {T : TubeHierarchy J} {E : Set Space}
    (H : HierarchyControl d θ g gap T) (A : HierarchyAnalysis T E d θ ρ)
    (HP : PhysicalAlternatives σ ω ζ h α κ η c)
    (hd : 0 < d) (hd1 : d < 1) (hζ : 0 < ζ) (hθ : θ ≤ η) (hk : k < J)
    (hlarge : (T.layer (k + 1)).radius / (T.layer k).radius ≤ d ^ h)
    (hsmall : d ^ h ≤ c) (hq : 0 < q)
    (hn : ((T.layer J).card : ℝ) < (d ^ (-ζ)) ^ q) (hbudget : 56 * (q : ℝ) * d ^ ζ ≤ 1) :
    FibreVolumeBound A σ ω k (κ * ((T.layer (k + 1)).radius / (T.layer k).radius) ^ (-α)) ∨
      Nonempty (IndexedCovers T k d θ ζ coverScale ω (d ^ (θ + 2 * ζ)) (d ^ (-ζ)) (A.shading (k + 1))) := by
  classical
  by_cases hv : FibreVolumeBound A σ ω k (κ * ((T.layer (k + 1)).radius / (T.layer k).radius) ^ (-α))
  · exact Or.inl hv
  right
  have hframes (t : Fin (T.layer k).card) := H.physical_fibre hd hk (A.shading (k + 1))
    (A.measurable (k + 1) (by omega)) (A.containment (k + 1) (by omega))
    (A.mass (k + 1) (by omega)) t
  choose N e hN he hrange hframe using hframes
  have hep (t) (i) : T.parent k (e t i) = t := by
    have hi : e t i ∈ Set.range (e t) := ⟨i, rfl⟩
    simpa only [hrange, Set.mem_setOf_eq] using hi
  have hcovers (t) : PhysicalCover d (T.layer k).radius (T.layer (k + 1)).radius ζ coverScale ω
      ((T.layer k).position t) ((T.layer k).direction t) (N t)
      ((T.layer (k + 1)).position ∘ e t) ((T.layer (k + 1)).direction ∘ e t) (A.shading (k + 1) ∘ e t) := by
    have hh := HP d (T.layer k).radius (T.layer (k + 1)).radius hd hd1.le
      (H.positive k hk.le) (H.positive (k + 1) (by omega))
      ((le_div_iff₀ (H.positive k hk.le)).mp (H.ratio_bounds hd.le hk).1)
      ((div_le_iff₀ (H.positive k hk.le)).mp (hlarge.trans hsmall)) (H.radius_bounds hk.le).2 hlarge
      _ _ ((T.layer k).unit t) (N t) _ _ _ ((hframe t).mono hd hd1.le hθ)
    rcases hh with hV | hP
    · apply False.elim
      apply hv
      refine ⟨t, N t, e t, (hframe t).1, hep t, hN t, ?_⟩
      simpa only [Function.comp_apply, mul_assoc, mul_left_comm, mul_comm] using hV
    · exact hP
  have hbalbudget : d ^ (θ + 2 * ζ) * q ≤ d ^ (θ + ζ) / 56 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 56)).mpr
    calc
      _ = d ^ (θ + ζ) * (56 * (q : ℝ) * d ^ ζ) := by
        rw [show θ + 2 * ζ = (θ + ζ) + ζ by ring, Real.rpow_add hd]
        ring
      _ ≤ d ^ (θ + ζ) * 1 := mul_le_mul_of_nonneg_left hbudget (Real.rpow_nonneg hd.le _)
      _ = _ := mul_one _
  have hR : 1 < d ^ (-ζ) := by
    rw [Real.rpow_neg hd.le]
    exact (one_lt_inv₀ (Real.rpow_pos_of_pos hd ζ)).mpr (Real.rpow_lt_one hd.le hd1 hζ)
  have hbalanced (t) : Nonempty (BalancedPhysicalCover d (T.layer k).radius (T.layer (k + 1)).radius
      ζ coverScale ω (d ^ (θ + 2 * ζ)) (d ^ (-ζ)) (N t)
      ((T.layer (k + 1)).position ∘ e t) ((T.layer (k + 1)).direction ∘ e t)) := by
    apply balance_physical_cover (hframe t) (hcovers t) hd (H.positive k hk.le)
      (H.positive (k + 1) (by omega)) (H.radius_bounds (by omega : k + 1 ≤ J)).2 coverScale_pos
      (Real.rpow_pos_of_pos hd _) hR q hq _ hbalbudget
    have hm : N t ≤ (T.layer (k + 1)).card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (e t) (he t)
    exact (Nat.cast_le.mpr (hm.trans (T.card_le_bottom (by omega : k + 1 ≤ J)))).trans_lt hn
  exact ⟨⟨N, e, he, hrange, hframe, fun t => Classical.choice (hbalanced t)⟩⟩

end WangZahlLot.Obl.wz_multiscale_finite_tower
