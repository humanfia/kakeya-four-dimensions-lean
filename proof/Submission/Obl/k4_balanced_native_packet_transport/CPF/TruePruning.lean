/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/TruePruning.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/TruePruning.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.HalfMassPruning
import Submission.Obl.k4_balanced_native_packet_transport.CPF.PrunedAtlas

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open scoped Classical ENNReal

noncomputable section

theorem floor_of_retained_half {n J q κ κ' : ℝ} {mass retained : ENNReal}
    (hn : 0 ≤ n) (hJ : 0 ≤ J) (hq : 0 < q) (hκ : 0 < κ) (hκ' : 2 * κ ≤ κ')
    (hfloor : ENNReal.ofReal (n * J / (q * κ)) ≤ mass)
    (hhalf : mass ≤ 2 * retained) :
    ENNReal.ofReal (n * J / (q * κ')) ≤ retained := by
  have hreal : 2 * (n * J / (q * κ')) ≤ n * J / (q * κ) := by
    calc
      _ ≤ 2 * (n * J / (q * (2 * κ))) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (mul_nonneg hn hJ) (by positivity)
          (mul_le_mul_of_nonneg_left hκ' hq.le)) (by norm_num)
      _ = _ := by field_simp
  apply (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)).mp
  calc
    _ = ENNReal.ofReal (2 * (n * J / (q * κ'))) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (n * J / (q * κ)) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ 2 * retained := hfloor.trans hhalf

theorem Atlas.selected_mass_le_one {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} (a : Atlas p k) (ha : a.TrueAt M D r) (b : Fin a.C) :
    ((p.ν k (a.γ b)).prod volume) (a.F b) ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, ⟨Mb, Db, hb⟩, _⟩ := hp
  letI := ((hb k).2.2.2.1 (a.γ b)).1
  have hE := ((hb k).2.2.2.1 (a.γ b)).2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩ := ha.2.2.1 b
  calc
    _ ≤ ((p.ν k (a.γ b)).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := by
      apply measure_mono
      intro z hz
      exact hE (hsel z hz).1
    _ = 1 := by rw [Measure.prod_prod]; simp

def Atlas.deletedMass {p : Data} {k : ℕ} (a : Atlas p k) (s : Finset (Fin a.C)) : ENNReal :=
  ∑ b ∈ Finset.univ \ s, ENNReal.ofReal (p.ω k (a.γ b)) *
    ((p.ν k (a.γ b)).prod volume) (a.F b)

theorem Atlas.halfMass_prune_cover {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r H : ℝ} (a : Atlas p k) (ha : a.TrueAt M D r)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (hH : 0 ≤ H) (κ' : ℝ)
    (eligible : Finset (Fin a.C)) :
    a.mass ≤
      ((a.pruneCrossings r bins m H κ').subatlas
        (a.halfMassLabels (a.pruneCrossings r bins m H κ').F eligible)).mass +
          (2 * a.crossingLostMass r bins m H + a.deletedMass eligible) := by
  let a0 := a.pruneCrossings r bins m H κ'
  have h := weighted_keep_half_mass
    (fun b => ENNReal.ofReal (p.ω k (a.γ b)))
    (fun b => ((p.ν k (a.γ b)).prod volume) (a.F b))
    (fun b => ((p.ν k (a.γ b)).prod volume) (a0.F b))
    (fun b => ((p.ν k (a.γ b)).prod volume) (a.F b \ a.crossingKeep r bins m H b)) eligible
    (fun b => (measure_inter_add_sdiff (a.F b)
      (a.measurableSet_crossingKeep r bins m hH b)).symm) (fun b => ?_)
  · convert h.trans_eq (add_assoc _ _ _) using 1
    · rfl
    · simpa only [a0, Atlas.pruneCrossings, Atlas.halfMassLabels, Atlas.crossingLostMass,
        Atlas.deletedMass] using
        congrArg (fun x => x + (2 * a.crossingLostMass r bins m H + a.deletedMass eligible))
          (a0.subatlas_mass (a.halfMassLabels a0.F eligible))
  · apply ne_of_lt
    exact ((measure_mono inter_subset_left).trans (a.selected_mass_le_one hp ha b)).trans_lt
      (by simp)

/-- Discard whole charts which lose over half their own mass. Every surviving
chart retains a true floor as well as its list witness. -/
theorem true_atlas_of_crossing_loss {p : Data} (hp : p.Valid)
    {k M D M' D' : ℕ} {r H κ' : ℝ}
    (a : Atlas p k) (ha : a.TrueAt M D r)
    (hM : M ≤ M') (hD : D ≤ D') (h4 : 4 ≤ D') (hκ : 1 ≤ a.κ)
    (hκ' : 2 * a.κ ≤ κ')
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (hmesh : 4 * a.κ ^ 2 ≤ (m : ℝ))
    (hH : 0 ≤ H) (hHκ : H ≤ κ')
    (hfmt : ∀ b, p.N k ^ M + (a.C : ℝ) * ((bins (a.γ b)).card * (5 + 4 * m)) ≤ p.N k ^ M')
    (hbin : ∀ b q, q ∈ a.F b →
      (obs (p.B k (a.γ b)) (δ (p.N k) r) q).2 ∈ bins (a.γ b))
    (eligible : Finset (Fin a.C))
    (hlost : 2 * a.crossingLostMass r bins m H + a.deletedMass eligible ≤
      ENNReal.ofReal (2 * a.κ)⁻¹) :
    ∃ (a' : Atlas p k) (lst : Fin (p.W k) → Observation → Finset (Fin a'.C)),
      a'.T = a.T ∧ a'.κ = κ' ∧ a'.TrueAt M' D' r ∧
      (∀ γ o, ((lst γ o).card : ℝ) ≤ κ') ∧
      (∀ b q, q ∈ a'.F b →
        b ∈ lst (a'.γ b) (obs (p.B k (a'.γ b)) (δ (p.N k) r) q)) ∧
      (∀ b, ∃ b₀ ∈ eligible, a'.γ b = a.γ b₀ ∧ a'.A b = a.A b₀ ∧ a'.Q b = a.Q b₀) ∧
      (∀ γ b, MeasurableSet {o | b ∈ lst γ o}) := by
  let a0 := a.pruneCrossings r bins m H κ'
  let s := a.halfMassLabels a0.F eligible
  let a' := a0.subatlas s
  let lst := fun γ o => a0.restrictList s (a.shortCrossingList r bins m H γ o)
  have hN : 1 ≤ p.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1 k)
  have hκ0 : 0 < a.κ := lt_of_lt_of_le zero_lt_one hκ
  have hκκ' : a.κ ≤ κ' := (by linarith : a.κ ≤ 2 * a.κ).trans hκ'
  have hch := a.pruneCrossings_charts ha hN hM hD h4 hκ hκκ'
    (hp.B_pos k) bins m hmesh hH hfmt hbin
  have hhalf (b : Fin s.card) :
      ((p.ν k (a.γ (a0.labelEmbedding s b))).prod volume) (a.F (a0.labelEmbedding s b)) ≤
        2 * ((p.ν k (a.γ (a0.labelEmbedding s b))).prod volume) (a0.F (a0.labelEmbedding s b)) :=
    (Finset.mem_filter.mp (a0.labelEmbedding_mem s b)).2
  have hcharts (b : Fin a'.C) : Chart (p.N k) M' D' κ' a'.T (a'.j b : ℝ) r
      (p.B k (a'.γ b)) (p.E k (a'.γ b)) (a'.c b) (a'.u b) (a'.Q b) (a'.R b)
      (a'.A b) (a'.F b)
      (ENNReal.ofReal (p.N k ^ (-p.f r) * |Matrix.det (a'.Q b)| /
        ((2 : ℝ) ^ a'.T * κ')) ≤ ((p.ν k (a'.γ b)).prod volume) (a'.F b)) := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩ :=
      hch (a0.labelEmbedding s b)
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
    exact floor_of_retained_half (Real.rpow_nonneg (zero_le_one.trans hN) _) (abs_nonneg _) (by positivity)
      hκ0 hκ' (ha.2.2.1 (a0.labelEmbedding s b)).2.2.2.2.2.2.2.2.2.2.2 (hhalf b)
  have hmass : ENNReal.ofReal κ'⁻¹ ≤ a'.mass := by
    have hret := Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
      a.mass a'.mass _ a.κ⁻¹ (inv_nonneg.mpr hκ0.le) ha.2.2.2
      (a.halfMass_prune_cover hp ha bins m hH κ' eligible) (by
        simpa only [show a.κ⁻¹ / 2 = (2 * a.κ)⁻¹ by field_simp] using hlost)
    apply (ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) hκ')).trans
    simpa only [show a.κ⁻¹ / 2 = (2 * a.κ)⁻¹ by field_simp] using hret
  refine ⟨a', lst, rfl, rfl, ⟨?_, ?_, hcharts, hmass⟩, ?_, ?_, ?_, ?_⟩
  · have hcount : (a'.C : ℝ) ≤ (a.C : ℝ) := by exact_mod_cast a0.subatlas_card_le s
    exact hcount.trans (ha.1.trans (pow_le_pow_right₀ hN hM))
  · exact a0.subatlas_separated s ha.2.1
  · intro γ o
    have hcard : ((lst γ o).card : ℝ) ≤ ((a.shortCrossingList r bins m H γ o).card : ℝ) := by
      exact_mod_cast a0.restrictList_card_le s (a.shortCrossingList r bins m H γ o)
    exact hcard.trans ((a.shortCrossingList_card r bins m hH γ o).trans hHκ)
  · intro b q hq
    apply (a0.mem_restrictList s _ b).mpr
    exact (hch (a0.labelEmbedding s b)).2.2.2.2.2.2.2.2.2.2.2 q hq
  · intro b
    refine ⟨a0.labelEmbedding s b, (Finset.mem_filter.mp (a0.labelEmbedding_mem s b)).1,
      rfl, rfl, rfl⟩
  · intro γ b
    change MeasurableSet {o | (b : Fin s.card) ∈ lst γ o}
    have heq : {o | b ∈ lst γ o} =
        {o | a0.labelEmbedding s b ∈ a.shortCrossingList r bins m H γ o} := by
      ext o
      exact a0.mem_restrictList s _ b
    rw [heq]
    exact a.measurableSet_shortCrossingList r bins m H γ (a0.labelEmbedding s b)

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
