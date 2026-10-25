import Submission.Obl.k4_scalar_guarded_tangent_preparation.KeptPiece
import Submission.Obl.k4_scalar_guarded_tangent_preparation.CompletionAux
import Submission.Obl.k4_scalar_guarded_tangent_preparation.Construction
import Submission.Obl.k4_scalar_guarded_tangent_preparation.Guard

/-!
# Full-prior layer completion

`FullPriorLayerCompletion` (x0612's split interface): the raw guarded geometry with its
reference law `σ`, together with a half-mass submeasure `ρ ≤ σ` with rectangular pure and
joint caps and fixed palettes, gives the literal `GuardedPrepared`.

At every stage, one simultaneous duration-core pruning (`PruneInput`) keeps in each layer
exactly the pieces whose current rectangle mass reaches `ν(A) / (H² 2^T)`. The pruned laws
keep weighted mass at least `1 / H` and live on the kept witnesses; the pruned layers keep
their true chart data. For the kept pieces, the true floor and the width floor give the
full-prior lower bound, the nodal pure ceiling gives the full-prior upper bound and the
whole-block graph bound (`PieceFacts`), and the profile and node-rounding bounds turn
original depths into tangent depths. The tangent slack is a fixed polynomial
`4665600 * 8^7 * B^7 * H^35 * K`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

/-- A fixed polynomial in subpower factors is subpower. -/
theorem subpower_poly {N B H K : ℕ → ℝ} (hN : Tendsto N atTop atTop) (hN1 : ∀ k, 1 ≤ N k)
    (hB : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, B k ≤ N k ^ ε)
    (hK : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hHB : ∀ k, H k ≤ B k) (hH1 : ∀ k, 1 ≤ H k) (hK1 : ∀ k, 1 ≤ K k) (c : ℝ) (hc : 0 < c) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, c * B k ^ 7 * H k ^ 35 * K k ≤ N k ^ ε := by
  intro ε hε
  have hNc : ∀ᶠ k in atTop, c ≤ N k ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity)).comp hN).eventually_ge_atTop c
  filter_upwards [hB (ε / 100) (by positivity), hK (ε / 100) (by positivity), hNc]
    with k hBk hKk hck
  have hN0 : 0 < N k := by linarith [hN1 k]
  have hH0 : 0 ≤ H k := by linarith [hH1 k]
  have hHk : H k ≤ N k ^ (ε / 100) := (hHB k).trans hBk
  have hB0 : 0 ≤ B k := by linarith [hH1 k, hHB k]
  have hK0 : 0 ≤ K k := by linarith [hK1 k]
  calc c * B k ^ 7 * H k ^ 35 * K k
      ≤ N k ^ (ε / 2) * (N k ^ (ε / 100)) ^ 7 * (N k ^ (ε / 100)) ^ 35 * N k ^ (ε / 100) := by
        gcongr
    _ = N k ^ (ε / 2 + 43 * (ε / 100)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
          ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0, ← Real.rpow_add hN0,
          ← Real.rpow_add hN0]
        congr 1; push_cast; ring
    _ ≤ N k ^ ε := Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)

/-- The full-prior layer completion. -/
theorem fullPriorLayerCompletion : FullPriorLayerCompletion := by
  classical
  intro p sample scale H buffer B M count node depth time layers σ d κ S hRG K ρ π hρσ
    hρmass hcaps
  obtain ⟨hexact, hbud, hsc, hbf, hact, hlen, hN2, hNt, hB1, hBsub, hd0, hd1, hκ0, hκ1,
    hS0, hσmu, hσmass, hlay, hnode, hguard⟩ := hRG
  obtain ⟨hK1, hKsub, hπ, hcap⟩ := hcaps
  -- elementary stage facts
  have hN₀gt : ∀ k, 1 < (p k).N (sample k) := fun k => exact_N_gt_one (hexact k) (sample k)
  have hN₀pos : ∀ k, 0 < (p k).N (sample k) := fun k => by linarith [hN₀gt k]
  have hH2 : ∀ k, 2 ≤ H k := fun k => (hbud k).2.2.1
  have hHpos : ∀ k, 0 < H k := fun k => by linarith [hH2 k]
  have hHB : ∀ k, H k ≤ B k := fun k => (hbud k).2.2.2.2.2.2.2.2.2.2.2
  have hcountH : ∀ k, (count k : ℝ) ≤ H k := fun k => (hbud k).2.2.2.2.2.2.2.2.2.1
  have hscpos : ∀ k, 0 < scale k := fun k => (hbud k).1
  have hNge1 : ∀ k, 1 ≤ (p k).N (sample k) ^ scale k := fun k => by linarith [hN2 k]
  have hεH : ∀ k, (p k).N (sample k) ^ (Real.log (H k) / Real.log ((p k).N (sample k))) =
      H k := fun k => rpow_log_div_log (hN₀gt k) (hHpos k)
  have hmeas : ∀ k (ℓ : Fin (count k)) (i : Fin (layers k ℓ).n),
      MeasurableSet ((layers k ℓ).assignment i) := by
    intro k ℓ i
    obtain ⟨_, _, hCD, _⟩ := hlay k ℓ
    exact (hCD.2.2.1 i).1
  have hdisj : ∀ k (ℓ : Fin (count k)) (i i' : Fin (layers k ℓ).n), i ≠ i' →
      (layers k ℓ).world i = (layers k ℓ).world i' →
      (layers k ℓ).block i = (layers k ℓ).block i' →
      Disjoint ((layers k ℓ).assignment i) ((layers k ℓ).assignment i') := by
    intro k ℓ
    obtain ⟨_, _, hCD, _⟩ := hlay k ℓ
    exact hCD.2.2.2.1
  -- the pruning at each stage
  let PI : ℕ → PruneInput := fun k =>
    { W := (p k).1 (sample k), count := count k, layers := layers k,
      ν := (p k).prior (sample k), ρ := ρ k, K₁ := H k ^ 2 }
  let ρ' : (k : ℕ) → Fin ((p k).1 (sample k)) → Measure Incidence :=
    fun k g => PruneInput.pruned (I := PI k) (hmeas k) g
  let keep : (k : ℕ) → (ℓ : Fin (count k)) → Fin (layers k ℓ).n → Prop :=
    fun k ℓ i => PruneInput.keep (I := PI k) (hmeas k) ℓ i
  let layers' : (k : ℕ) → Fin (count k) → Layer ((p k).1 (sample k)) :=
    fun k ℓ => (layers k ℓ).prune (keep k ℓ)
  let K' : ℕ → ℝ := fun k => 4665600 * 8 ^ 7 * B k ^ 7 * H k ^ 35 * K k
  have hρ'ρ : ∀ k g, ρ' k g ≤ ρ k g := fun k g => PruneInput.pruned_le (I := PI k) (hmeas k) g
  have hρ'σ : ∀ k g, ρ' k g ≤ σ k g := fun k g => (hρ'ρ k g).trans (hρσ k g)
  have hρ'mu : ∀ k g, ρ' k g ≤ Split.mu (p k) (sample k) g :=
    fun k g => (hρ'σ k g).trans (hσmu k g)
  -- the retained weighted mass
  have hmass' : ∀ k, ENNReal.ofReal (H k)⁻¹ ≤
      ∑ g, ENNReal.ofReal ((p k).weight (sample k) g) * ρ' k g Set.univ := by
    intro k
    have hw := (hexact k).2.1 (sample k)
    refine PruneInput.pruned_mass (I := PI k) (hmeas k) ((p k).weight (sample k))
      hw.2.1 hw.2.2.1 (fun g => (hw.2.2.2.1 g).1) (pow_pos (hHpos k) 2) (hdisj k)
      (inv_nonneg.mpr (hHpos k).le) ?_ ?_
    · show (count k : ℝ) / H k ^ 2 ≤ (H k)⁻¹
      rw [div_le_iff₀ (pow_pos (hHpos k) 2)]
      calc (count k : ℝ) ≤ H k := hcountH k
        _ = (H k)⁻¹ * H k ^ 2 := by field_simp [(hHpos k).ne']
    · simpa [mul_inv] using hρmass k
  -- the slack
  have hK'ge : ∀ k, 1 ≤ K' k ∧ K k ≤ K' k ∧ B k ^ 2 * H k ^ 2 ≤ K' k ∧
      8 * B k ^ 3 * H k ^ 5 ≤ K' k ∧ 4665600 * (8 * B k * H k ^ 5) ^ 7 ≤ K' k ∧
      H k * B k ≤ K' k ∧ H k ^ 2 ≤ K' k ∧ H k ≤ K' k ∧ B k ^ 2 ≤ K' k := by
    intro k
    have hB : 1 ≤ B k := hB1 k
    have hH : 1 ≤ H k := by linarith [hH2 k]
    have hK : 1 ≤ K k := hK1 k
    set X : ℝ := B k ^ 7 * H k ^ 35 with hX
    have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB) (one_le_pow₀ hH)
    have hK'eq : K' k = (4665600 * 8 ^ 7) * X * K k := by
      show 4665600 * 8 ^ 7 * B k ^ 7 * H k ^ 35 * K k = _
      rw [hX]; ring
    have hcX : X ≤ (4665600 * 8 ^ 7) * X := by
      have : (1 : ℝ) ≤ 4665600 * 8 ^ 7 := by norm_num
      nlinarith
    have hXK' : X ≤ K' k := by
      rw [hK'eq]
      calc X ≤ (4665600 * 8 ^ 7) * X := hcX
        _ = (4665600 * 8 ^ 7) * X * 1 := (mul_one _).symm
        _ ≤ (4665600 * 8 ^ 7) * X * K k := by gcongr
    have hpow : ∀ (a b : ℕ), a ≤ 7 → b ≤ 35 → B k ^ a * H k ^ b ≤ X := by
      intro a b ha hb
      exact mul_le_mul (pow_le_pow_right₀ hB ha) (pow_le_pow_right₀ hH hb)
        (by positivity) (by positivity)
    have hmono : ∀ (a b : ℕ), a ≤ 7 → b ≤ 35 → B k ^ a * H k ^ b ≤ K' k :=
      fun a b ha hb => (hpow a b ha hb).trans hXK'
    have hbase : 4665600 * (8 * B k * H k ^ 5) ^ 7 ≤ K' k := by
      rw [hK'eq]
      have : 4665600 * (8 * B k * H k ^ 5) ^ 7 = (4665600 * 8 ^ 7) * X := by
        rw [hX]; ring
      rw [this]
      calc (4665600 * 8 ^ 7) * X = (4665600 * 8 ^ 7) * X * 1 := (mul_one _).symm
        _ ≤ (4665600 * 8 ^ 7) * X * K k := by gcongr
    refine ⟨le_trans hX1 hXK', ?_, hmono 2 2 (by norm_num) (by norm_num), ?_, hbase, ?_,
      ?_, ?_, ?_⟩
    · rw [hK'eq]
      have : (1 : ℝ) ≤ (4665600 * 8 ^ 7) * X := le_trans hX1 hcX
      calc K k = 1 * K k := (one_mul _).symm
        _ ≤ (4665600 * 8 ^ 7) * X * K k := by gcongr
    · have h8 : 8 * B k ^ 3 * H k ^ 5 ≤ 8 * X := by
        have := hpow 3 5 (by norm_num) (by norm_num)
        nlinarith
      refine h8.trans ?_
      rw [hK'eq]
      calc 8 * X ≤ (4665600 * 8 ^ 7) * X := by gcongr; norm_num
        _ = (4665600 * 8 ^ 7) * X * 1 := (mul_one _).symm
        _ ≤ (4665600 * 8 ^ 7) * X * K k := by gcongr
    · have := hmono 1 1 (by norm_num) (by norm_num)
      simpa [mul_comm] using this
    · simpa using hmono 0 2 (by norm_num) (by norm_num)
    · simpa using hmono 0 1 (by norm_num) (by norm_num)
    · simpa using hmono 2 0 (by norm_num) (by norm_num)
  -- the witnesses of the prepared package
  refine ⟨p, sample, scale, H, buffer, K', M, count, node, depth, time, layers', ρ', π,
    d, κ, S, ?_⟩
  intro N₀ N actual loss guard
  -- the kept pieces of a layer
  have hkept_support : ∀ k (ℓ : Fin (count k)) (g : Fin ((p k).1 (sample k))),
      ρ' k g {z | ∃ i, (layers' k ℓ).world i = g ∧ z ∈ (layers' k ℓ).witness i}ᶜ = 0 := by
    intro k ℓ g
    obtain ⟨_, _, hCD, _, hσsupp, _⟩ := hlay k ℓ
    have hsupp := PruneInput.pruned_support (I := PI k) (hmeas k) (σ k) (hρσ k) ℓ g
      (fun i => fun z hz => (hCD.2.2.2.2.1 i hz).2) (hσsupp g)
    refine le_antisymm (le_trans (measure_mono ?_) hsupp.le) bot_le
    intro z hz hz'
    apply hz
    obtain ⟨i, hig, hik, hzi⟩ := hz'
    obtain ⟨i', hi'⟩ := (layers k ℓ).exists_keptEmb (keep k ℓ) hik
    refine ⟨i', ?_, ?_⟩
    · show (layers k ℓ).world ((layers k ℓ).keptEmb (keep k ℓ) i') = g
      rw [hi']; exact hig
    · show z ∈ (layers k ℓ).witness ((layers k ℓ).keptEmb (keep k ℓ) i')
      rw [hi']; exact hzi
  refine ⟨hexact, fun k => ?_, hsc, hbf, hact, hlen, hρ'mu, hmass', ?_, ?_, hguard⟩
  · -- budgets
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩ := hbud k
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · -- the pruned layers
    intro k ℓ
    obtain ⟨hdp0, hdpL, hCD, hJ, hσsupp, _⟩ := hlay k ℓ
    refine ⟨hdp0, hdpL, ?_, fun i => hJ _, hkept_support k ℓ⟩
    refine chartData_subfamily hCD ((layers k ℓ).keptEmb (keep k ℓ))
      ((layers k ℓ).keptEmb_injective (keep k ℓ)) ?_
    -- coverage by the kept witnesses
    have hcovval : ENNReal.ofReal ((p k).N (sample k) ^
        (-(Real.log (H k) / Real.log ((p k).N (sample k))))) = ENNReal.ofReal (H k)⁻¹ := by
      rw [Real.rpow_neg (hN₀pos k).le, hεH k]
    refine le_trans (le_of_eq hcovval) ((hmass' k).trans ?_)
    have hle : ∀ g, ρ' k g Set.univ ≤ Split.mu (p k) (sample k) g
        {z | ∃ i, (layers' k ℓ).world i = g ∧ z ∈ (layers' k ℓ).witness i} := by
      intro g
      have hms : MeasurableSet
          {z | ∃ i, (layers' k ℓ).world i = g ∧ z ∈ (layers' k ℓ).witness i} := by
        have : {z | ∃ i, (layers' k ℓ).world i = g ∧ z ∈ (layers' k ℓ).witness i} =
            ⋃ i, {z | (layers' k ℓ).world i = g ∧ z ∈ (layers' k ℓ).witness i} := by
          ext z; simp
        rw [this]
        refine MeasurableSet.iUnion fun i => ?_
        by_cases h : (layers' k ℓ).world i = g
        · simp only [h, true_and, Set.setOf_mem_eq]
          exact (hCD.2.2.1 _).2
        · simp only [h, false_and, Set.setOf_false]
          exact MeasurableSet.empty
      calc ρ' k g Set.univ
          = ρ' k g {z | ∃ i, (layers' k ℓ).world i = g ∧ z ∈ (layers' k ℓ).witness i} +
            ρ' k g {z | ∃ i, (layers' k ℓ).world i = g ∧ z ∈ (layers' k ℓ).witness i}ᶜ :=
            (measure_add_measure_compl hms).symm
        _ = ρ' k g {z | ∃ i, (layers' k ℓ).world i = g ∧ z ∈ (layers' k ℓ).witness i} := by
            rw [hkept_support k ℓ g, add_zero]
        _ ≤ _ := hρ'mu k g _
    exact Finset.sum_le_sum (fun g _ => mul_le_mul_right (hle g) _)
  · -- the tangent input
    refine ⟨hN2, hNt, ⟨fun k => (hK'ge k).1, ?_⟩, hd0, hd1, hκ0, hκ1, hS0, fun k => ?_, ?_, ?_⟩
    · exact subpower_poly hNt hNge1 hBsub hKsub hHB (fun k => by linarith [hH2 k]) hK1
        (4665600 * 8 ^ 7) (by norm_num)
    · -- the global clause
      obtain ⟨_, hω0, hω1, hγ, _⟩ := (hexact k).2.1 (sample k)
      refine ⟨hω0, hω1, fun g => ?_, ?_⟩
      · obtain ⟨hprob, _, hae, hEmeas, hEsub, _⟩ := hγ g
        refine ⟨hprob, hπ k g, ?_, ?_, ?_⟩
        · filter_upwards [hae] with l hl e
          exact (hl e).trans ((hbud k).2.2.2.2.2.2.2.2.1.trans (hK'ge k).2.2.2.2.2.2.2.1)
        · refine (hρ'mu k g).trans (Measure.restrict_le_self.trans ?_)
          intro t
          rw [Measure.smul_apply, smul_eq_mul]
          exact le_mul_of_one_le_left (by positivity)
            (ENNReal.one_le_ofReal.mpr (hK'ge k).1)
        · apply le_antisymm _ bot_le
          calc ρ' k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ
              ≤ Split.mu (p k) (sample k) g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ := hρ'mu k g _
            _ ≤ Split.mu (p k) (sample k) g (Split.E (p k) (sample k) g)ᶜ :=
                measure_mono (Set.compl_subset_compl.mpr hEsub)
            _ = 0 := by
                show (((p k).prior (sample k) g).prod volume).restrict
                  (Split.E (p k) (sample k) g) (Split.E (p k) (sample k) g)ᶜ = 0
                rw [Measure.restrict_apply hEmeas.compl, Set.compl_inter_self, measure_empty]
      · exact le_trans (ENNReal.ofReal_le_ofReal
          (inv_anti₀ (hHpos k) (hK'ge k).2.2.2.2.2.2.2.1)) (hmass' k)
    · -- the caps
      intro R hR
      filter_upwards [hcap R hR] with k hk g r s b hr1 hr2 hs1 hs2 hb1 hb2
      obtain ⟨h1, h2, h3⟩ := hk g r s b hr1 hr2 hs1 hs2 hb1 hb2
      have hKK : K k ≤ K' k := (hK'ge k).2.1
      have hNnn : ∀ x : ℝ, 0 ≤ ((p k).N (sample k) ^ scale k) ^ x :=
        fun x => Real.rpow_nonneg (by linarith [hN2 k]) _
      refine ⟨fun c => (h1 c).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hKK (hNnn _))), fun q c => ?_, fun q c e => ?_⟩
      · exact ((hρ'ρ k g) _).trans ((h2 q c).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hKK (hNnn _))))
      · refine ((hρ'ρ k g) _).trans ((h3 q c e).trans ?_)
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hKK (hNnn _))) (by positivity)
    · -- the charts
      intro R hR
      filter_upwards [hnode R hR] with k hk s hs1 hs2
      have hround := hk s hs1 hs2
      obtain ⟨hdp0, hdpL, hCD, hJ, hσsupp, hprof, hT1, hT2, hceil⟩ := hlay k (node k s)
      have hT := tangent_time (hNge1 k) hκ0.le hκ1 hround hT1 hT2 (hB1 k)
        (hK'ge k).2.2.2.2.2.2.2.2
      have texp := tangent_exponents (hN₀gt k) (hscpos k) rfl hd0 hd1.le hprof hround
      refine ⟨hT.1, hT.2, fun i => (hCD.2.2.1 _).1, ?_, fun i => ?_, fun g => ?_⟩
      · intro i i' hii' hw hb
        exact hCD.2.2.2.1 _ _ (((layers k (node k s)).keptEmb_injective
          (keep k (node k s))).ne hii') hw hb
      · -- one kept piece
        have hkeep := (layers k (node k s)).keptEmb_keep (keep k (node k s)) i
        have hcost := PruneInput.cost_le_of_keep (I := PI k) (hmeas k) hkeep
        have hKb : SlackBounds (B k) (H k) (K' k) :=
          ⟨(hK'ge k).1, (hK'ge k).2.2.1, (hK'ge k).2.2.2.1, (hK'ge k).2.2.2.2.1,
            (hK'ge k).2.2.2.2.2.1, (hK'ge k).2.2.2.2.2.2.1, (hK'ge k).2.2.2.2.2.2.2.1⟩
        exact kept_piece_tangent (σ := σ k) (ρ := ρ' k) hCD (hN₀gt k) (hscpos k) hdp0 (hH2 k)
          (hB1 k) hd0 hd1.le hJ hceil (hρ'σ k) hprof hround hKb _ hcost
      · -- support on the kept rectangles
        have hsupp := hkept_support k (node k s) g
        refine le_antisymm (le_trans (measure_mono ?_) hsupp.le) bot_le
        intro z hz hz'
        apply hz
        obtain ⟨i, hig, hzi⟩ := hz'
        exact ⟨i, hig, (hCD.2.2.2.2.1 _ hzi).2⟩

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation

