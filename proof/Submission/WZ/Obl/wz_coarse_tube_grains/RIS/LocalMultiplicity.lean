-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Multiplicity
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleEstimate

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set

/-- A lower multiplicity bound on the union gives a lower bound for shading mass. -/
theorem multiplicity_mul_volume_le_mass {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) {M : ENNReal}
    (hM : ∀ p ∈ ⋃ i, Y i, M ≤ multiplicity Y p) :
    M * volume (⋃ i, Y i) ≤ ∑ i, volume (Y i) := by
  classical
  calc
    _ = ∫⁻ p, (⋃ i, Y i).indicator (fun _ => M) p :=
      (lintegral_indicator_const (MeasurableSet.iUnion hY) M).symm
    _ ≤ ∫⁻ p, multiplicity Y p := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ ⋃ i, Y i
      · simpa only [Set.indicator_of_mem hp] using hM p hp
      · simp only [Set.indicator_of_notMem hp]
        exact bot_le
    _ = _ := by
      unfold multiplicity
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_indicator_const (hY i), one_mul]
      · intro i _
        exact measurable_const.indicator (hY i)

/-- A union-volume estimate gives an upper bound on every uniform multiplicity
level, using only the absolute upper bound on one unit tube's volume. -/
theorem multiplicity_bound_of_union_lower {δ c M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : 0 < c) (hM : 0 ≤ M) {n : ℕ} (hn : 0 < n)
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hsub : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hmult : ∀ p ∈ ⋃ i, Y i, ENNReal.ofReal M ≤ multiplicity Y p)
    (hvol : ENNReal.ofReal (c * (n * δ ^ 2)) ≤ volume (⋃ i, Y i)) :
    M ≤ 384 / c := by
  have hmass : (∑ i, volume (Y i)) ≤ ENNReal.ofReal (384 * (n * δ ^ 2)) := by
    calc
      _ ≤ ∑ i : Fin n, ENNReal.ofReal (384 * δ ^ 2) :=
        Finset.sum_le_sum fun i _ => (measure_mono (hsub i)).trans
          (tube_volume_upper hδ hδ1 (x i) (v i) (hv i))
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hbound : ENNReal.ofReal (M * (c * (n * δ ^ 2))) ≤
      ENNReal.ofReal (384 * (n * δ ^ 2)) := by
    rw [ENNReal.ofReal_mul hM]
    exact (mul_le_mul_right hvol _).trans
      ((multiplicity_mul_volume_le_mass hY hmult).trans hmass)
  have hr : M * (c * (n * δ ^ 2)) ≤ 384 * (n * δ ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
  have hnδ : 0 < (n : ℝ) * δ ^ 2 := by positivity
  apply (le_div_iff₀ hc).mpr
  apply (mul_le_mul_iff_left₀ hnδ).mp
  simpa only [mul_assoc] using hr

namespace Interfaces

/-- Section 9's fine-scale multiplicity estimate, with the full Katz--Tao and
Frostman errors retained. It follows directly from the local rescaling theorem. -/
theorem multiplicity_of_local_rescaling {σ ω : ℝ} (hR : R σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 →
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (y w : V),
    0 < n → ‖w‖ = 1 →
    (∀ i, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ T ρ y w ∧
      MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) →
    X δ n x v → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → K δ m n x v →
    B δ ρ l n 1 x v Finset.univ (fun _ => y) (fun _ => w) (fun _ => 0) →
    ∀ M : ℝ, 0 ≤ M →
    (∀ p ∈ ⋃ i, Y i, o M ≤ multiplicity Y p) →
    M ≤ C * δ ^ (-ε) * (δ / ρ) ^ (-ω) * m *
      (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ σ := by
  intro ε hε
  obtain ⟨κ, hκ, η, hη, hRκ⟩ := hR ε hε
  refine ⟨384 / κ, by positivity, η, hη, ?_⟩
  intro δ ρ hδ hδ100 hδρ hρ1 m l hm hl n x v Y y w hn hw hdata hX hdense hK hB M hM hmult
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hm0 : 0 < m := by linarith
  have hl0 : 0 < l := by linarith
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let D := m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)
  have hD : 0 < D := by dsimp [D]; positivity
  let c := κ * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * D ^ (-σ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hvolume := hRκ δ ρ hδ hδ100 hδρ hρ1 m l hm hl n x v Y y w
    hn hw hdata hX hdense hK hB
  have hbound := multiplicity_bound_of_union_lower hδ (by linarith) hc hM hn
    (fun i => (hdata i).1) (fun i => (hdata i).2.2.1) (fun i => (hdata i).2.2.2)
    hmult (by simpa only [c, D, o, μ, mul_assoc, mul_left_comm, mul_comm] using hvolume)
  apply hbound.trans_eq
  dsimp only [c]
  rw [div_eq_mul_inv, mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev,
    inv_inv, ← Real.rpow_neg hD.le, ← Real.rpow_neg (div_pos hδ hρ).le,
    ← Real.rpow_neg hδ.le]
  simp only [neg_neg]
  ring

end Interfaces
end WangZahlLot.Obl.wz_coarse_tube_grains.RIS

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- A lower multiplicity on the union bounds its volume by total shading mass. -/
theorem lower_multiplicity_mul_volume_le_mass {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) {M : ENNReal}
    (hM : ∀ p ∈ ⋃ i, Y i, M ≤ multiplicity Y p) :
    M * volume (⋃ i, Y i) ≤ ∑ i, volume (Y i) := by
  classical
  calc
    M * volume (⋃ i, Y i) = ∫⁻ p, (⋃ i, Y i).indicator (fun _ => M) p :=
      (lintegral_indicator_const (MeasurableSet.iUnion hY) M).symm
    _ ≤ ∫⁻ p, multiplicity Y p := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ ⋃ i, Y i
      · simpa only [Set.indicator_of_mem hp] using hM p hp
      · simp only [Set.indicator_of_notMem hp, zero_le]
    _ = ∑ i, volume (Y i) := by
      unfold multiplicity
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_indicator_const (hY i), one_mul]
      · intro i _
        exact measurable_const.indicator (hY i)

/-- Converting the local volume lower bound to a uniform-multiplicity upper bound. -/
theorem multiplicity_bound_of_local_volume {δ ρ κ ε ω σ m l M : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hκ : 0 < κ)
    (hm : 0 < m) (hl : 0 < l) (hM : 0 ≤ M) (hn : 0 < n)
    (hfib : ∀ i, ‖v i‖ = 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ Tube δ (x i) (v i))
    (hmult : ∀ p ∈ ⋃ i, Y i, M ≤ ({i : Fin n | p ∈ Y i}.ncard : ℝ))
    (hvol : ENNReal.ofReal (κ * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ (-σ)) ≤ volume (⋃ i, Y i)) :
    M ≤ (384 / κ) * δ ^ (-ε) * (δ / ρ) ^ (-ω) * m *
      (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ σ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let b := m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)
  have hb : 0 < b := by dsimp [b]; positivity
  let A := κ * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) * b ^ (-σ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hmass := lower_multiplicity_mul_volume_le_mass (fun i => (hfib i).2.1)
    (M := ENNReal.ofReal M) (fun p hp => by
      rw [multiplicity_eq_ncard, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (hmult p hp))
  have hupper : ∑ i, volume (Y i) ≤ ENNReal.ofReal (384 * n * δ ^ 2) := by
    calc
      ∑ i, volume (Y i) ≤ ∑ _i : Fin n, ENNReal.ofReal (384 * δ ^ 2) :=
        Finset.sum_le_sum fun i _ => (measure_mono (hfib i).2.2).trans
          (tube_volume_upper hδ hδ1 (x i) (v i) (hfib i).1)
      _ = ENNReal.ofReal (384 * n * δ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
        congr 1
        ring
  have hMA : M * A ≤ 384 * n * δ ^ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [ENNReal.ofReal_mul hM]
    exact ((mul_le_mul_right hvol _).trans hmass).trans hupper
  have hcancel : ((384 / κ) * δ ^ (-ε) * (δ / ρ) ^ (-ω) * m * b ^ σ) * A =
      384 * n * δ ^ 2 := by
    dsimp [A]
    rw [Real.rpow_neg hδ.le, Real.rpow_neg (div_pos hδ hρ).le, Real.rpow_neg hb.le]
    have hδε : δ ^ ε ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
    have hδω : (δ / ρ) ^ ω ≠ 0 := (Real.rpow_pos_of_pos (div_pos hδ hρ) _).ne'
    have hbσ : b ^ σ ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
    field_simp
  apply (mul_le_mul_iff_left₀ hA).mp
  rw [hcancel]
  exact hMA

namespace Interfaces

/-- Uniform fine multiplicity in a carrier is bounded by the rescaled estimate. -/
theorem local_multiplicity_of_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1 / 2)
    (hω : 0 ≤ ω) (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 →
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (x v : Fin n → V)
      (Y : Fin n → Set V) (y w : V), 0 < n → ‖w‖ = 1 →
    (∀ i, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ T ρ y w ∧
      MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) →
    X δ n x v → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → K δ m n x v →
    B δ ρ l n 1 x v Finset.univ (fun _ => y) (fun _ => w) (fun _ => 0) →
    ∀ M : ℝ, 0 ≤ M → (∀ p ∈ ⋃ i, Y i, M ≤ q {i | p ∈ Y i}) →
    M ≤ C * δ ^ (-ε) * (δ / ρ) ^ (-ω) * m *
      (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ σ := by
  intro ε hε
  obtain ⟨κ, hκ, η, hη, hbound⟩ := local_rescaling_of_estimate hσ hσ2 hω hE ε hε
  refine ⟨384 / κ, by positivity, η, hη, ?_⟩
  intro δ ρ hδ hδ100 hδρ hρ1 m l hm hl n x v Y y w hn hw hfib hX hdense hK hB M hM hmult
  exact multiplicity_bound_of_local_volume hδ (by linarith) (hδ.trans_le hδρ) hκ
    (by linarith) (by linarith) hM hn (fun i => ⟨(hfib i).1, (hfib i).2.2⟩) hmult
    (hbound δ ρ hδ hδ100 hδρ hρ1 m l hm hl n x v Y y w hn hw hfib hX hdense hK hB)

end Interfaces

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
