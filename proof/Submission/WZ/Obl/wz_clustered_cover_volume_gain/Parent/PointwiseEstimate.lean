-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.PointwiseEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.KatzSeparation

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces

open Finset MeasureTheory

noncomputable section

/-- For uniformly dense shadings, the convex count pays for removing the
essential-distinctness hypothesis from E. It costs one additional factor of `m`. -/
theorem pointwise_dense_estimate {σ ω : ℝ} (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
    0 < n → (∀ i, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ I ∧
      MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) →
    (∀ i, o (δ ^ η * δ ^ 2) ≤ μ (Y i)) → K δ m n x v → F δ l n x v →
    o (a * δ ^ (ω + ε) * (m⁻¹) ^ 2 * (n * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ μ (⋃ i, Y i) := by
  classical
  intro ε hε
  obtain ⟨a, ha, η, hη, hbound⟩ := hE ε hε
  let C := conflictCountConstant + 1
  have hC : 0 < C := by dsimp [C, conflictCountConstant]; positivity
  refine ⟨a / C, div_pos ha hC, η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl n x v Y hn hfib hdense hK hF
  have hδ1 : δ ≤ 1 := by linarith
  have hm0 : 0 < m := by linarith
  obtain ⟨S, hsep, hmass⟩ := weighted_distinct_of_katz hδ hδ1 hm0.le
    (fun i => (hfib i).1) hK (fun _ => 1)
  have hcard : (n : ℝ) ≤ (⌈conflictCountConstant * m⌉₊ : ℝ) * S.card := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hmass
    exact_mod_cast hmass
  have hceil : (⌈conflictCountConstant * m⌉₊ : ℝ) ≤ C * m := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ conflictCountConstant * m by
      dsimp [conflictCountConstant]; positivity)
    dsimp only [C]
    nlinarith
  have hnk : (n : ℝ) ≤ C * m * S.card :=
    hcard.trans (mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg _))
  have hS : 0 < S.card := by
    by_contra hh
    have hz : S.card = 0 := by omega
    rw [hz, Nat.cast_zero, mul_zero] at hnk
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    linarith
  let ii : Fin S.card → Fin n := fun i => (S.equivFin.symm i).1
  have hiS (i : Fin S.card) : ii i ∈ S := (S.equivFin.symm i).2
  have hinj : Function.Injective ii := Subtype.val_injective.comp S.equivFin.symm.injective
  have hkn : (S.card : ℝ) ≤ n := by exact_mod_cast (show S.card ≤ n by simpa using S.card_le_univ)
  have hk0 : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS
  have hl' : 1 ≤ l * n / S.card := by
    apply (le_div_iff₀ hk0).mpr
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hd : o (δ ^ η * S.card * δ ^ 2) ≤ ∑ i : Fin S.card, μ (Y (ii i)) := by
    calc
      _ = ∑ _i : Fin S.card, o (δ ^ η * δ ^ 2) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, o]
        rw [← ENNReal.ofReal_natCast S.card, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring
      _ ≤ _ := sum_le_sum fun i _ => hdense (ii i)
  have hA : A δ η m (l * n / S.card) S.card (x ∘ ii) (v ∘ ii) (Y ∘ ii) := by
    refine ⟨hS, fun i => hfib (ii i), ?_, hd, ?_, ?_⟩
    · intro i j hij
      exact hsep (ii i) (hiS i) (ii j) (hiS j) (fun he => hij (hinj he))
    · exact (show Katz δ m x v from hK).comp_injective hinj
    · exact (show Frostman δ l x v from hF).comp_injective hS hinj
  have hh := hbound δ hδ hδ100 m (l * n / S.card) hm hl' S.card (x ∘ ii) (v ∘ ii) (Y ∘ ii) hA
  have hbase : m ^ (-(3 / 2 : ℝ)) * (l * n / S.card) * (S.card * δ) =
      m ^ (-(3 / 2 : ℝ)) * l * (n * δ) := by
    field_simp
  rw [hbase] at hh
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hh.trans (measure_mono ?_))
  · calc
      _ ≤ (a / C) * δ ^ (ω + ε) * (m⁻¹) ^ 2 * ((C * m * S.card) * δ ^ 2) *
          (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ) := by gcongr
      _ = a * δ ^ (ω + ε) * m⁻¹ * (S.card * δ ^ 2) *
          (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ) := by
        field_simp
  · apply Set.iUnion_subset
    intro i
    exact Set.subset_iUnion Y (ii i)

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces
