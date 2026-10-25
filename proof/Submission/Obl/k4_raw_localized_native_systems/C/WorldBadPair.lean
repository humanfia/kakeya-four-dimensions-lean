import Submission.Obl.k4_raw_localized_native_systems.C.LabelBadMass
import Submission.Obl.k4_raw_localized_native_systems.C.PinningBins
import Submission.Obl.k4_raw_localized_native_systems.C.PairBound

/-
Adapted from this LOT tree, o178, session x0596, `WorldBadPair.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The bad-pair mass of one world, for paired full-time binning

Fix a valid problem, a sample `k` and a world `γ`.  Suppose a finite family of
labels (later: the charts of a narrow true system) is given with unit normals,
normal speeds, extrapolated frames and blocks, and a path `E` of incidences, each
tagged by a label whose block contains its time, whose assignment contains its
line, and which the terminal observation lists.  If all incidences of `E` are
good (angular cap, terminal and depth-zero typicality, native bounds), then the
paired mass of pairs on one trajectory whose two labels have normals separated
by more than `g H` (modulo sign) is bounded by a sum over first labels of
`|block| · N^(-S u + 2τ) · 9κ · N^(-f 0 + τ) · 256 κ'^4 |det Q'|`.

This is the hypothesis of paired full-time binning (o175) in the proof of the
paper's full-time localization (Section 10, Proposition 10.2).
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The native bounds at an incidence, with slack `κ`. -/
def NativeOK (p : Data) (k : ℕ) (γ : Fin (p.W k)) (κ : ℝ) (q : Point) : Prop :=
  |MvPolynomial.eval (x q.1 q.2) (p.P k γ)| ≤ κ ∧
  |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv 3 (p.P k γ))| ≤ κ * p.B k γ ∧
  |MvPolynomial.eval (x q.1 q.2)
      (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (p.P k γ)))| ≤ κ * p.B k γ ^ 2 ∧
  p.B k γ / κ ≤ |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv 3 (p.P k γ))|

/-- Bins pinned by a first label `i` and the listed second labels. -/
def pinBins {n : ℕ} (normal : Fin n → Plane) (speed : Fin n → ℝ) (θ w : ℝ)
    (lst : Observation → Finset (Fin n)) (i : Fin n) (o : Observation) :
    Finset (Fin 2 → ℤ) := by
  classical
  exact (lst o).biUnion fun j =>
    if θ < min ‖normal i - normal j‖ ‖normal i + normal j‖ then
      nbhd (binOf w (cramer (normal i) (normal j) (speed i) (speed j)))
    else ∅

theorem card_pinBins_le {n : ℕ} (normal : Fin n → Plane) (speed : Fin n → ℝ) (θ w : ℝ)
    (lst : Observation → Finset (Fin n)) (i : Fin n) (o : Observation) {m : ℕ}
    (hm : (lst o).card ≤ m) : (pinBins normal speed θ w lst i o).card ≤ 9 * m := by
  classical
  unfold pinBins
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ j ∈ lst o, (if θ < min ‖normal i - normal j‖ ‖normal i + normal j‖ then
          nbhd (binOf w (cramer (normal i) (normal j) (speed i) (speed j))) else ∅).card
      ≤ ∑ _j ∈ lst o, 9 := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · exact card_nbhd_le _
        · simp
    _ = 9 * (lst o).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 9 * m := by gcongr

theorem measurableSet_pinBins {n : ℕ} (normal : Fin n → Plane) (speed : Fin n → ℝ) (θ w : ℝ)
    (lst : Observation → Finset (Fin n)) (hlst : ∀ j, MeasurableSet {o | j ∈ lst o})
    (i : Fin n) (z : Fin 2 → ℤ) :
    MeasurableSet {o | z ∈ pinBins normal speed θ w lst i o} := by
  classical
  set Pz : Fin n → Prop := fun j => z ∈ (if θ < min ‖normal i - normal j‖ ‖normal i + normal j‖
      then nbhd (binOf w (cramer (normal i) (normal j) (speed i) (speed j))) else ∅) with hPz
  have : {o | z ∈ pinBins normal speed θ w lst i o} =
      ⋃ j : Fin n, {o | Pz j ∧ j ∈ lst o} := by
    ext o
    simp only [pinBins, Finset.mem_biUnion, Set.mem_setOf_eq, Set.mem_iUnion, hPz]
    constructor
    · rintro ⟨j, hj, hz⟩
      exact ⟨j, hz, hj⟩
    · rintro ⟨j, hz, hj⟩
      exact ⟨j, hj, hz⟩
  rw [this]
  refine MeasurableSet.iUnion fun j => ?_
  by_cases h : Pz j
  · have : {o | Pz j ∧ j ∈ lst o} = {o | j ∈ lst o} := by
      ext o; simp [h]
    rw [this]; exact hlst j
  · have : {o | Pz j ∧ j ∈ lst o} = ∅ := by
      ext o; simp [h]
    rw [this]; exact MeasurableSet.empty

/-- A label's bad set: good incidences, crossing the extrapolated native
parallelogram of the label, with velocity bin pinned by a listed transverse label. -/
def labelBad (p : Data) (k : ℕ) (γ : Fin (p.W k)) (u τ κ' : ℝ) (c u₀ : Plane)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (bins : Observation → Finset (Fin 2 → ℤ)) : Set Point :=
  {q | AngGood p k γ u τ q ∧ Typ0 p k γ τ q ∧
    obs (p.B k γ) (δ (p.N k) 0) q ∈ nativeCrossing p k γ κ' c u₀ Q ∧
    velBin (p.N k) u q ∈ bins (obs (p.B k γ) (δ (p.N k) p.L) q)}

theorem measurableSet_labelBad {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    {u τ κ' : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L) (c u₀ : Plane)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (bins : Observation → Finset (Fin 2 → ℤ))
    (hbins : ∀ w, MeasurableSet {o | w ∈ bins o}) :
    MeasurableSet (labelBad p k γ u τ κ' c u₀ Q bins) := by
  have hL : 0 ≤ p.L := hp.length_pos.le
  obtain ⟨hGm, -⟩ := valid_G_spec hp k γ hu huη
  obtain ⟨hgm, -⟩ := valid_g_spec hp k γ hL le_rfl
  obtain ⟨hg0m, -⟩ := valid_g_spec hp k γ le_rfl hL
  have hobsL := measurable_obs' (p.B k γ) (δ (p.N k) p.L)
  have hobs0 := measurable_obs' (p.B k γ) (δ (p.N k) 0)
  have hjoint : Measurable (jointObs (p.B k γ) (p.N k) p.L u) := by
    rw [jointObs_eq]; exact hobsL.prodMk (measurable_velBin _ _)
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · exact (measurableSet_le (hGm.comp hjoint) measurable_const).inter
      (measurableSet_le measurable_const (hgm.comp hobsL))
  · exact measurableSet_le (hg0m.comp hobs0) measurable_const
  · exact hobs0 (measurableSet_nativeCrossing p k γ κ' c u₀ Q)
  · exact (hobsL.prodMk (measurable_velBin _ _)) (measurableSet_listed bins hbins)

theorem delta_zero (N : ℝ) : δ N 0 = 1 := by
  simp [δ]

/-- **Bad-pair mass of one world.** -/
theorem world_bad_pair_le {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
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
    (hpin : 8 * ρ / (g * H) ≤ δ (p.N k) u) :
    ((p.ν k γ).prod (volume.prod volume))
        {z | (z.1, z.2.1) ∈ E ∧ (z.1, z.2.2) ∈ E ∧
          g * H < min ‖normal (tag (z.1, z.2.1)) - normal (tag (z.1, z.2.2))‖
            ‖normal (tag (z.1, z.2.1)) + normal (tag (z.1, z.2.2))‖} ≤
      ∑ i, volume (blk i) * (ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κ : ℕ) : ENNReal) *
        (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
          ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(Q' i).det|))) := by
  classical
  have hθ : 0 < g * H := mul_pos hg hH
  have hδu : 0 < δ (p.N k) u := by unfold δ; positivity
  set bins : Fin n → Observation → Finset (Fin 2 → ℤ) :=
    fun i => pinBins normal speed (g * H) (δ (p.N k) u) lst i with hbins
  have hEm : MeasurableSet (p.E k γ) := by
    obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
    exact ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.1
  have hPdeg : (p.P k γ).totalDegree ≤ 2 := by
    obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
    exact ((hfmt k).2.2.2.1 γ).2.2.2.2.1
  have hB := hp.B_pos k γ
  haveI : IsProbabilityMeasure (p.ν k γ) := by
    obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
    exact ((hfmt k).2.2.2.1 γ).1
  have hZm : ∀ i, MeasurableSet (labelBad p k γ u τ κ' (c i) (u₀ i) (Q' i) (bins i)) :=
    fun i => measurableSet_labelBad hp k γ hu huη (c i) (u₀ i) (Q' i) (bins i)
      (fun w => measurableSet_pinBins normal speed (g * H) (δ (p.N k) u) lst hlst_meas i w)
  have hmain := pair_bad_le_sum (p.ν k γ) (p.E k γ)
    {z : Line × (ℝ × ℝ) | (z.1, z.2.1) ∈ E ∧ (z.1, z.2.2) ∈ E ∧
          g * H < min ‖normal (tag (z.1, z.2.1)) - normal (tag (z.1, z.2.2))‖
            ‖normal (tag (z.1, z.2.1)) + normal (tag (z.1, z.2.2))‖} blk
    (fun i => labelBad p k γ u τ κ' (c i) (u₀ i) (Q' i) (bins i)) hZm hEm ?cover
  · refine hmain.trans ?_
    gcongr with i
    have hle := label_bad_mass_le hp k γ (τ := τ) hu huη hκ' (c i) (u₀ i) (Q' i) (hQ' i) (bins i)
      (9 * κ) (fun w => measurableSet_pinBins normal speed (g * H) (δ (p.N k) u) lst hlst_meas i w)
      (fun o => card_pinBins_le normal speed (g * H) (δ (p.N k) u) lst i o (hlst_card o))
    exact hle
  · intro z hz
    obtain ⟨h1, h2, hsep⟩ := hz
    set i := tag (z.1, z.2.1) with hi
    set j := tag (z.1, z.2.2) with hj
    obtain ⟨hblk1, -⟩ := htag _ h1
    obtain ⟨-, hlst2⟩ := htag _ h2
    obtain ⟨hgood, htyp, hnat, hEprob, ht2⟩ := hE_good _ h2
    refine ⟨i, hblk1, ⟨hgood, htyp, ?_, ?_⟩, hEprob⟩
    · -- the depth-zero observation crosses the extrapolated native parallelogram
      have hcross := Submission.Obl.k4_coarsened_outer_horizon_composition.obs_mem_crossing
        (κ := κ') (t₀ := 0) (t₁ := 1) (a := δ (p.N k) 0) (B := p.B k γ)
        (by linarith) (by rw [delta_zero]; norm_num) hB (c i) (u₀ i) (Q' i) (p.P k γ) hPdeg
        (z.1, z.2.2) ht2 (hext _ h1 z.2.2 ht2)
        (by rw [delta_zero, mul_one]; exact hnat.1)
        hnat.2.1
        (by rw [delta_zero, div_one]; exact hnat.2.2.1)
        hnat.2.2.2
      have hδ0 : δ (p.N k) 0 / p.B k γ = 1 / p.B k γ := by rw [delta_zero]
      unfold nativeCrossing
      rw [← hδ0]
      exact hcross
    · -- the velocity bin is pinned by the listed transverse label
      have hpinned := norm_sub_cramer_le (hnormal i) (hnormal j) hθ hsep
        (hspeed _ h1) (hspeed _ h2)
      have hclose : ‖v z.1 - cramer (normal i) (normal j) (speed i) (speed j)‖ ≤ δ (p.N k) u := by
        refine hpinned.trans ?_
        calc 4 * (ρ + ρ) / (g * H) = 8 * ρ / (g * H) := by ring
          _ ≤ δ (p.N k) u := hpin
      have hbin := binOf_mem_nbhd hδu hclose
      simp only [hbins, pinBins, Finset.mem_biUnion]
      refine ⟨j, hlst2, ?_⟩
      rw [if_pos hsep]
      exact hbin

end

end Submission.Obl.k4_raw_localized_native_systems.C
