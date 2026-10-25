import Submission.Obl.k4_raw_localized_native_systems.C.Q2TotalBad

/-
Adapted from this LOT tree, o178, session x0596, `FixedTimeBad.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Transverse incidences at a fixed first time

The paper's count of first labels is made at a fixed time `t₀`: the incidences
`(l, t)` of the good path whose line is also on the good path at `t₀`, with
transverse tags at the two times, are covered by the bad sets of the labels whose
block contains `t₀`.  Hence their mass is at most the sum of the label bounds over
those labels only, for every `t₀` (no averaging in `t₀`).
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

open Classical in
/-- **Bad incidences at a fixed first time, one world.** -/
theorem world_bad_fixed_le {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    {u τ κ' : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L) (hκ' : 1 ≤ κ')
    {n : ℕ} (normal : Fin n → Plane) (speed : Fin n → ℝ) (c u₀ : Fin n → Plane)
    (Q' : Fin n → Matrix (Fin 2) (Fin 2) ℝ) (hQ' : ∀ i, (Q' i).det ≠ 0)
    (blk : Fin n → Set ℝ)
    (lst : Observation → Finset (Fin n)) (κ : ℕ) (hlst_card : ∀ o, (lst o).card ≤ κ)
    (hlst_meas : ∀ j, MeasurableSet {o | j ∈ lst o})
    (E : Set Point) (tag : Point → Fin n)
    {g H ρ : ℝ} (hg : 0 < g) (hH : 0 < H)
    (hnormal : ∀ i, ‖normal i‖ = 1)
    (hE_good : ∀ q ∈ E, AngGood p k γ u τ q ∧ Typ0 p k γ τ q ∧ NativeOK p k γ κ' q ∧
      q ∈ p.E k γ ∧ q.2 ∈ Set.Icc (0 : ℝ) 1)
    (htag : ∀ q ∈ E, q.2 ∈ blk (tag q) ∧ tag q ∈ lst (obs (p.B k γ) (δ (p.N k) p.L) q))
    (hspeed : ∀ q ∈ E, |inner ℝ (normal (tag q)) (v q.1) - speed (tag q)| ≤ ρ)
    (hext : ∀ q ∈ E, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin (Q' (tag q))⁻¹ (y q.1 t - c (tag q) - t • u₀ (tag q))‖ ≤ κ')
    (hpin : 8 * ρ / (g * H) ≤ δ (p.N k) u) (t₀ : ℝ) :
    ((p.ν k γ).prod volume)
        {q | (q.1, t₀) ∈ E ∧ q ∈ E ∧
          g * H < min ‖normal (tag (q.1, t₀)) - normal (tag q)‖
            ‖normal (tag (q.1, t₀)) + normal (tag q)‖} ≤
      ∑ i ∈ Finset.univ.filter (fun i => t₀ ∈ blk i),
        ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κ : ℕ) : ENNReal) *
          (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
            ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(Q' i).det|)) := by
  classical
  have hθ : 0 < g * H := mul_pos hg hH
  have hδu : 0 < δ (p.N k) u := by unfold δ; positivity
  set bins : Fin n → Observation → Finset (Fin 2 → ℤ) :=
    fun i => pinBins normal speed (g * H) (δ (p.N k) u) lst i with hbins
  have hPdeg : (p.P k γ).totalDegree ≤ 2 := by
    obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
    exact ((hfmt k).2.2.2.1 γ).2.2.2.2.1
  have hB := hp.B_pos k γ
  have hEm : MeasurableSet (p.E k γ) := by
    obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
    exact ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.1
  -- cover by the bad sets of the labels whose block contains `t₀`
  have hcover : {q : Point | (q.1, t₀) ∈ E ∧ q ∈ E ∧
          g * H < min ‖normal (tag (q.1, t₀)) - normal (tag q)‖
            ‖normal (tag (q.1, t₀)) + normal (tag q)‖} ⊆
      ⋃ i ∈ Finset.univ.filter (fun i => t₀ ∈ blk i),
        labelBad p k γ u τ κ' (c i) (u₀ i) (Q' i) (bins i) ∩ p.E k γ := by
    intro q hq
    obtain ⟨h1, h2, hsep⟩ := hq
    set i := tag (q.1, t₀) with hi
    set j := tag q with hj
    obtain ⟨hblk1, -⟩ := htag _ h1
    obtain ⟨-, hlst2⟩ := htag _ h2
    obtain ⟨hgood, htyp, hnat, hEprob, ht2⟩ := hE_good _ h2
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
    refine ⟨i, hblk1, ⟨hgood, htyp, ?_, ?_⟩, hEprob⟩
    · have hcross := Submission.Obl.k4_coarsened_outer_horizon_composition.obs_mem_crossing
        (κ := κ') (t₀ := 0) (t₁ := 1) (a := δ (p.N k) 0) (B := p.B k γ)
        (by linarith) (by rw [delta_zero]; norm_num) hB (c i) (u₀ i) (Q' i) (p.P k γ) hPdeg
        q ht2 (hext _ h1 q.2 ht2)
        (by rw [delta_zero, mul_one]; exact hnat.1)
        hnat.2.1
        (by rw [delta_zero, div_one]; exact hnat.2.2.1)
        hnat.2.2.2
      have hδ0 : δ (p.N k) 0 / p.B k γ = 1 / p.B k γ := by rw [delta_zero]
      unfold nativeCrossing
      rw [← hδ0]
      exact hcross
    · have hpinned := norm_sub_cramer_le (hnormal i) (hnormal j) hθ hsep
        (hspeed _ h1) (hspeed _ h2)
      have hclose : ‖v q.1 - cramer (normal i) (normal j) (speed i) (speed j)‖ ≤
          δ (p.N k) u := by
        refine hpinned.trans ?_
        calc 4 * (ρ + ρ) / (g * H) = 8 * ρ / (g * H) := by ring
          _ ≤ δ (p.N k) u := hpin
      have hbin := binOf_mem_nbhd hδu hclose
      simp only [hbins, pinBins, Finset.mem_biUnion]
      refine ⟨j, hlst2, ?_⟩
      rw [if_pos hsep]
      exact hbin
  refine (measure_mono hcover).trans ((measure_biUnion_finset_le _ _).trans ?_)
  refine Finset.sum_le_sum fun i _ => ?_
  have hle := label_bad_mass_le hp k γ (τ := τ) hu huη hκ' (c i) (u₀ i) (Q' i) (hQ' i) (bins i)
    (9 * κ) (fun w => measurableSet_pinBins normal speed (g * H) (δ (p.N k) u) lst hlst_meas i w)
    (fun o => card_pinBins_le normal speed (g * H) (δ (p.N k) u) lst i o (hlst_card o))
  refine le_trans (le_of_eq ?_) hle
  unfold selected
  rw [Measure.restrict_apply' hEm]
  rfl

variable {p : Data} {k : ℕ}

/-- The times whose block index is that of the chart `b` of world `γ`. -/
def q2tblk (a : Atlas p k) (γ : Fin (p.W k)) (b : Fin a.C) : Set ℝ :=
  {t | a.γ b = γ ∧ blockIdx a.T t = ((a.j b : ℕ) : ℤ)}

open Classical in
/-- **Transverse incidences at a fixed first time, for a later chart system.** -/
theorem q2_world_bad_fixed_le (hp : Valid p) (a : Atlas p k) (γ : Fin (p.W k))
    {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
    (κL : ℕ) (hcard : ∀ o, (a.lst γ o).card ≤ κL)
    (hmeas : ∀ b, MeasurableSet {o | b ∈ a.lst γ o})
    (hC : 0 < a.C) {u τ κ' lam ρ Kc g H : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (hκ' : 1 ≤ κ') (hκκ' : κ ≤ κ')
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ)
    (hKc : κ' + ρ ≤ Kc)
    (hg : 0 < g) (hH : 0 < H) (hpin : 8 * ρ / (g * H) ≤ δ (p.N k) u) (t₀ : ℝ) :
    ((p.ν k γ).prod volume)
        {q | (q.1, t₀) ∈ goodPath a γ u τ κ' lam ∧ q ∈ goodPath a γ u τ κ' lam ∧
          g * H < min ‖q2normal a (tagOf a γ hC (q.1, t₀)) - q2normal a (tagOf a γ hC q)‖
            ‖q2normal a (tagOf a γ hC (q.1, t₀)) + q2normal a (tagOf a γ hC q)‖} ≤
      ∑ b ∈ Finset.univ.filter (fun b => t₀ ∈ q2tblk a γ b),
        ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
          (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
            ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det|)) := by
  classical
  have hEsub : ∀ z ∈ p.E k γ, z.2 ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
    intro z hz
    exact (Set.mem_prod.1 (((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.1 hz)).2
  refine world_bad_fixed_le hp k γ (τ := τ) hu huη hκ' (q2normal a) (q2speed a Kc) a.c a.u
    (fun b => stripScale a.T • a.Q b) ?_ (q2tblk a γ) (a.lst γ) κL hcard hmeas
    (goodPath a γ u τ κ' lam) (tagOf a γ hC) hg hH
    (fun b => norm_minorNormal (hc.det_ne b)) ?_ ?_ ?_ ?_ hpin t₀
  · intro b
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (stripScale_pos a.T).ne') (hc.det_ne b)
  · intro q hq
    obtain ⟨htag, hF, hlong⟩ := goodPath_tag a γ hc hdisj hC hq
    have hsel := hc.selected _ hF
    rw [htag.1] at hsel
    exact ⟨hq.2.1, hq.2.2.1, hq.2.2.2.1, hsel.1, hEsub q hsel.1⟩
  · intro q hq
    obtain ⟨htag, hF, hlong⟩ := goodPath_tag a γ hc hdisj hC hq
    have hsel := hc.selected _ hF
    refine ⟨⟨htag.1, htag.2.2⟩, ?_⟩
    have := hknown _ q hF
    rwa [htag.1] at this
  · intro q hq
    exact goodPath_speed hc hdisj hC hρ hKc hq
  · intro q hq t ht
    obtain ⟨htag, hF, hlong⟩ := goodPath_tag a γ hc hdisj hC hq
    exact (hc.extend _ htag.2.1 ht).trans hκκ'

end

end Submission.Obl.k4_raw_localized_native_systems.C
