-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2FirstJet, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2FirstJet.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2FirstJet.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2FirstJet.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2GridCovers
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2RangeFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetBridge
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetNumerics
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPrunedHierarchy
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

set_option autoImplicit false

/-!
# The first jet in version 2 at power-range dyadic levels

The `j = 2` counterparts of x0260's `ScalarFirstJetCommonRow.lean`, `ScalarFirstJetBudget.lean`,
`ScalarFirstJetOutput.lean` and `ScalarUniformFirstJet.lean` (o078, branch `x0260` at
`206ab988`), with the same proofs:

* `v2_first_jet_reading_transport`: changing the row of slopes by `C H^(7/32)` per component
  moves the first jet by at most `2 C Y H^((1-d)/32)` (`|y| ≤ Y`);
* `V2Hierarchy.exists_common_row_first_jet_restriction`: on a hierarchy over the bridge levels of
  the designated levels, one retained set carries the Taylor estimates of every designated level
  and the first-jet covers of the reading level, all against the row of the finest level;
* `v2FirstJetBudget`: one subpower budget for all losses;
* `V2FirstJetOutput`: the conclusion of the first jet (paper Prop. `prop:scalar-normal`, `j = 2`);
* `uniform_v2_first_jet_between_powers_all_labels`: the first jet at all designated levels in a
  power range `[N^-b, N^-a]`, given the range form of the planar kernel (`RangeFitStatement`).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

noncomputable section

/-- **Reading transport**: the bridge slope error is below the first-jet reading. -/
theorem v2_first_jet_reading_transport {d H C Y t v : ℝ} {c : Fin 7 → ℝ}
    {F A A' : ℝ → Fin 2 → ℝ} (hd : 0 ≤ d) (hH : 0 < H) (hH1 : H ≤ 1) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hread : |v2FirstJet c F A t - v| ≤ H ^ ((1 - d) / 32))
    (hslope : ∀ k, |A t k - A' t k| ≤ C * H ^ (7 / 32 : ℝ)) (hy : ∀ k, |zy c t k| ≤ Y) :
    |v2FirstJet c F A' t - v| ≤ (1 + 2 * C * Y) * H ^ ((1 - d) / 32) := by
  have hp : H ^ (7 / 32 : ℝ) ≤ H ^ ((1 - d) / 32) :=
    Real.rpow_le_rpow_of_exponent_ge hH hH1 (by linarith)
  have hterm : ∀ k, |(A t k - A' t k) * zy c t k| ≤ C * H ^ ((1 - d) / 32) * Y := by
    intro k
    rw [abs_mul]
    exact mul_le_mul ((hslope k).trans (mul_le_mul_of_nonneg_left hp hC)) (hy k) (abs_nonneg _)
      (by positivity)
  have he : v2FirstJet c F A' t - v = (v2FirstJet c F A t - v) +
      ((A t 0 - A' t 0) * zy c t 0 + (A t 1 - A' t 1) * zy c t 1) := by
    simp only [v2FirstJet, dot_two]; ring
  rw [he]
  calc _ ≤ |v2FirstJet c F A t - v| +
        (|(A t 0 - A' t 0) * zy c t 0| + |(A t 1 - A' t 1) * zy c t 1|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ H ^ ((1 - d) / 32) + (C * H ^ ((1 - d) / 32) * Y + C * H ^ ((1 - d) / 32) * Y) :=
        add_le_add hread (add_le_add (hterm 0) (hterm 1))
    _ = (1 + 2 * C * Y) * H ^ ((1 - d) / 32) := by ring

/-- **One common row for all designated levels** (version 2). -/
theorem V2Hierarchy.exists_common_row_first_jet_restriction {Λ : Type*} [MeasurableSpace Λ]
    {ν : Measure Λ} [IsProbabilityMeasure ν] {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ}
    {m steps top : ℕ} {start : Fin m → ℕ}
    (hstart : ∀ i, start i ≤ top)
    (hreach : ∀ i, scalarDyadicBridge top (start i) steps = top)
    {B P K ζ d duration : ℝ} (hB : 0 ≤ B)
    (G : V2Hierarchy ν E F
      (fun q : Fin (Fintype.card (ScalarBridgeLabels m steps)) =>
        2 ^ scalarBridgeHeight top start q)
      (fun _ => by positivity)
      (fun q => (1 / ((2 ^ scalarBridgeHeight top start q : ℕ) : ℝ)) ^ (1 / 4 : ℝ)) B)
    (read : Fin m)
    (h : UpperHyp ν c E F K ζ d) (hK : 1 ≤ K)
    (hζ : 0 < ζ) (hd0 : 0 ≤ d) (hd : d < 1)
    (hP : 1 ≤ P) (hKP : K ≤ P) (hBP : B ≤ P) (hduration : 0 ≤ duration)
    {R : Set (Λ × ℝ)} (hRm : MeasurableSet R) (hR : R ⊆ E ∩ (univ ×ˢ (G.comp 0).times))
    (hfloor : ∀ q ∈ R, ∀ i : Fin (Fintype.card (ScalarBridgeLabels m steps)),
      ENNReal.ofReal (scalarBridgeMesh top start i / P) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ timeCell (2 ^ scalarBridgeHeight top start i)
          (scalarTimeBlockCode (2 ^ scalarBridgeHeight top start i) (by positivity) q.2))))
    (hζH : ζ ≤ scalarDyadicLength (start read) ^ 2)
    (hconcentration : OriginalScalarResidualAt (d := d) (j := 2) Λ (Fin 2 → ℤ)
      (v2ResidualBound P) (scalarDyadicLength (start read) ^ (1 / 8 : ℝ)) duration) :
    ∃ R' : Set (Λ × ℝ), MeasurableSet R' ∧ R' ⊆ R ∧
      (duration / (400000 * P ^ 8)) * (ν.prod volume).real R ≤ (ν.prod volume).real R' ∧
      (∀ i : Fin m, ∀ q ∈ R', ∀ q' ∈ R',
        scalarTimeBlockCode (2 ^ start i) (by positivity) q.2 =
          scalarTimeBlockCode (2 ^ start i) (by positivity) q'.2 →
        ∀ k, |F q'.2 k - F q.2 k -
            (q'.2 - q.2) * G.slopeRow (scalarBridgeTopIndex m steps) q.2 k| ≤
          (4 * B + 32 * (steps + 1 : ℕ) * B * P) *
            scalarDyadicLength (start i) ^ (11 / 10 : ℝ)) ∧
      ∃ L : ℝ → ℤ → Finset ℝ,
        (∀ t z, ((L t z).card : ℝ) ≤ 1000 * v2ResidualBound P ^ 2) ∧
        ∀ q ∈ R', ∃ v ∈ L q.2 ⌊zS F (c q.1) q.2 / scalarDyadicLength (start read)⌋,
          |v2FirstJet (c q.1) F (G.slopeRow (scalarBridgeTopIndex m steps)) q.2 - v| ≤
            (1 + 128 * (steps + 1 : ℕ) * B * P * K) *
              scalarDyadicLength (start read) ^ ((1 - d) / 32) := by
  let idx := scalarBridgeStartIndex steps read
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hreadHeight : scalarBridgeHeight top start idx = start read :=
    scalarBridgeHeight_start top start hstart read
  have hreadMesh : 1 / ((2 ^ scalarBridgeHeight top start idx : ℕ) : ℝ) =
      scalarDyadicLength (start read) := by
    rw [← scalarDyadicLength_eq, hreadHeight]
  have hfloorRead : ∀ q ∈ R,
      ENNReal.ofReal ((1 / ((2 ^ scalarBridgeHeight top start idx : ℕ) : ℝ)) / P) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ timeCell (2 ^ scalarBridgeHeight top start idx)
          (scalarTimeBlockCode (2 ^ scalarBridgeHeight top start idx) (by positivity) q.2))) := by
    intro q hq
    simpa only [scalarBridgeMesh, scalarDyadicLength_eq] using hfloor q hq idx
  obtain ⟨R', hR'm, hR'R, hmass, hcover⟩ :=
    G.exists_v2_first_jet_cover_restriction idx h hζ hd0 hd hP hKP hBP hduration
      hRm hR (by simpa only [hreadMesh] using hζH) hfloorRead
      (by simpa only [hreadMesh] using hconcentration)
  have hRk : ∀ k, R ⊆ E ∩ (univ ×ˢ (G.comp k).times) := by
    intro k; rw [G.times_comp k]; exact hR
  have hbridge : ∀ k, ∀ i : Fin m,
      (∀ q ∈ R,
        |(G.comp k).slope (scalarBridgeStartIndex steps i) q.2 -
          (G.comp k).slope (scalarBridgeTopIndex m steps) q.2| ≤
          (32 * (steps + 1 : ℕ) * B * P) * scalarDyadicLength (start i) ^ (7 / 32 : ℝ)) ∧
      (∀ q ∈ R, ∀ q' ∈ R,
        scalarTimeBlockCode (2 ^ start i) (by positivity) q.2 =
          scalarTimeBlockCode (2 ^ start i) (by positivity) q'.2 →
        |F q'.2 k - F q.2 k - (q'.2 - q.2) * (G.comp k).slope (scalarBridgeTopIndex m steps) q.2| ≤
          (4 * B + 32 * (steps + 1 : ℕ) * B * P) *
            scalarDyadicLength (start i) ^ (11 / 10 : ℝ)) :=
    fun k => ScalarGridHierarchy.bridge_slopes_and_taylor hstart hreach hB hPpos (G.comp k)
      (hRk k) hfloor
  refine ⟨R', hR'm, hR'R, hmass, ?_, ?_⟩
  · intro i q hq q' hq' hcode k
    exact (hbridge k i).2 q (hR'R hq) q' (hR'R hq') hcode
  · have hcover' : ∃ L : ℝ → ℤ → Finset ℝ,
        (∀ t z, ((L t z).card : ℝ) ≤ 1000 * v2ResidualBound P ^ 2) ∧
        ∀ q ∈ R', ∃ v ∈ L q.2 ⌊zS F (c q.1) q.2 / scalarDyadicLength (start read)⌋,
          |v2FirstJet (c q.1) F (G.slopeRow idx) q.2 - v| ≤
            scalarDyadicLength (start read) ^ ((1 - d) / 32) := by
      simpa only [hreadMesh] using hcover
        (scalarDyadicLength (start read) ^ ((1 - d) / 32)) (by rw [hreadMesh])
    obtain ⟨L, hL, hLcover⟩ := hcover'
    refine ⟨L, hL, ?_⟩
    intro q hq
    obtain ⟨v, hv, hdist⟩ := hLcover q hq
    refine ⟨v, hv, ?_⟩
    have hy : ∀ k, |zy (c q.1) q.2 k| ≤ 2 * K :=
      fun k => (h.active_bounds (hR (hR'R hq)).1).2.1 k
    have htransport := v2_first_jet_reading_transport (A := G.slopeRow idx)
      (A' := G.slopeRow (scalarBridgeTopIndex m steps)) hd0
      (scalarDyadicLength_pos _) (scalarDyadicLength_le_one _)
      (by positivity : 0 ≤ 32 * (steps + 1 : ℕ) * B * P)
      (by linarith [hK] : 0 ≤ 2 * K) hdist (fun k => (hbridge k read).1 q (hR'R hq)) hy
    convert htransport using 2
    ring

/-- One subpower budget for the losses of the version-2 first jet. -/
def v2FirstJetBudget (steps : ℕ) (P Q : ℝ) : ℝ :=
  10000000000000000 * (steps + 2 : ℕ) * (P * Q) ^ 32

theorem v2FirstJetBudget_bounds {steps : ℕ} {B P Q K : ℝ}
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hB : 0 ≤ B) (hBP : B ≤ P)
    (hK : 0 ≤ K) (hKP : K ≤ P) :
    1 ≤ v2FirstJetBudget steps P Q ∧ B ≤ v2FirstJetBudget steps P Q ∧
      800000 * B * P ^ 8 * Q ≤ v2FirstJetBudget steps P Q ∧
      1000 * v2ResidualBound P ^ 2 ≤ v2FirstJetBudget steps P Q ∧
      4 * B + 32 * (steps + 1 : ℕ) * B * P ≤ v2FirstJetBudget steps P Q ∧
      1 + 128 * (steps + 1 : ℕ) * B * P * K ≤ v2FirstJetBudget steps P Q := by
  let Z := P * Q
  let C : ℝ := 10000000000000000 * (steps + 2 : ℕ)
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le hP hQ
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hPZ : P ≤ Z := by simp only [Z]; nlinarith
  have hQZ : Q ≤ Z := by simp only [Z]; nlinarith
  have hBZ : B ≤ Z := hBP.trans hPZ
  have hKZ : K ≤ Z := hKP.trans hPZ
  have hn : (0 : ℝ) ≤ steps := Nat.cast_nonneg _
  have hC : 1 ≤ C := by simp only [C]; push_cast; nlinarith
  have hdom (c : ℝ) (p : ℕ) (hc : c ≤ C) (hp : p ≤ 32) :
      c * Z ^ p ≤ v2FirstJetBudget steps P Q := by
    exact mul_le_mul hc (pow_le_pow_right₀ hZ hp) (pow_nonneg hZ0 _) (zero_le_one.trans hC)
  have hpow1 : Z ≤ Z ^ 32 := by
    simpa only [pow_one] using pow_le_pow_right₀ hZ (by norm_num : 1 ≤ 32)
  have hbase : 1 ≤ v2FirstJetBudget steps P Q := by
    have hh := hdom 1 0 hC (by norm_num)
    simpa only [pow_zero, mul_one] using hh
  refine ⟨hbase, ?_, ?_, ?_, ?_, ?_⟩
  · exact hBZ.trans (hpow1.trans (by simpa only [one_mul] using hdom 1 32 hC le_rfl))
  · calc
      _ ≤ 800000 * Z * Z ^ 8 * Z := by gcongr
      _ = 800000 * Z ^ 10 := by ring
      _ ≤ _ := hdom 800000 10 (by simp only [C]; push_cast; nlinarith) (by norm_num)
  · calc
      _ = 1000000000000000 * P ^ 20 := by simp only [v2ResidualBound]; ring
      _ ≤ 1000000000000000 * Z ^ 20 := by gcongr
      _ ≤ _ := hdom 1000000000000000 20 (by simp only [C]; push_cast; nlinarith) (by norm_num)
  · have hZ2 : Z ≤ Z ^ 2 := by
      simpa only [pow_one] using pow_le_pow_right₀ hZ (by norm_num : 1 ≤ 2)
    have hprod : B * P ≤ Z ^ 2 := by nlinarith [mul_le_mul hBZ hPZ hP0 hZ0]
    calc
      _ ≤ 4 * Z ^ 2 + 32 * (steps + 1 : ℕ) * Z ^ 2 := by nlinarith [hBZ.trans hZ2]
      _ = (4 + 32 * (steps + 1 : ℕ)) * Z ^ 2 := by ring
      _ ≤ _ := hdom _ 2 (by simp only [C]; push_cast; nlinarith) (by norm_num)
  · have hprod : B * P * K ≤ Z ^ 3 := by
      calc
        _ ≤ Z * Z * Z := by gcongr
        _ = _ := by ring
    have hZ3 : 1 ≤ Z ^ 3 := one_le_pow₀ hZ
    calc
      _ ≤ Z ^ 3 + 128 * (steps + 1 : ℕ) * Z ^ 3 := by nlinarith
      _ = (1 + 128 * (steps + 1 : ℕ)) * Z ^ 3 := by ring
      _ ≤ _ := hdom _ 3 (by simp only [C]; push_cast; nlinarith) (by norm_num)

theorem v2FirstJetBudget_subpower (N P Q : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hP : ∀ k, 1 ≤ P k) (hQ : ∀ k, 1 ≤ Q k)
    (hPsub : SubpowerBound N P) (hQsub : SubpowerBound N Q) (steps : ℕ) :
    (∀ k, 1 ≤ v2FirstJetBudget steps (P k) (Q k)) ∧
      SubpowerBound N (fun k => v2FirstJetBudget steps (P k) (Q k)) := by
  have hZ : Subpower N (fun k => P k * Q k) :=
    ⟨fun k => one_le_mul_of_one_le_of_one_le (hP k) (hQ k),
      subpower_mul (fun k => zero_lt_one.trans_le (hN k))
        (fun k => zero_le_one.trans (hP k)) (fun k => zero_le_one.trans (hQ k)) hPsub hQsub⟩
  exact subpower_polynomial hN hNt hZ (A := 10000000000000000 * (steps + 2 : ℕ)) (by
      have hn : (0 : ℝ) ≤ steps := Nat.cast_nonneg _
      push_cast
      nlinarith) 32

/-- **The conclusion of the first jet** (version 2), at designated dyadic levels `start` with
reading level `start read` and loss `H`. -/
def V2FirstJetOutput {Λ : Type*} [MeasurableSpace Λ] {m : ℕ} (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ)
    (start : Fin m → ℕ) (read : Fin m) (d H : ℝ) : Prop :=
  ∃ E₁ : Set (Λ × ℝ), E₁ ⊆ E ∧ MeasurableSet E₁ ∧
    ENNReal.ofReal H⁻¹ ≤ (ν.prod volume) E₁ ∧
    ∃ A : ℝ → Fin 2 → ℝ, Measurable A ∧ (∀ p ∈ E₁, ‖A p.2‖ ≤ H) ∧
      (∀ (i : Fin m) (j : ℤ), ∀ p ∈ E₁, ∀ q ∈ E₁,
        p.2 ∈ Ico ((j : ℝ) / (2 : ℝ) ^ start i) (((j : ℝ) + 1) / (2 : ℝ) ^ start i) →
        q.2 ∈ Ico ((j : ℝ) / (2 : ℝ) ^ start i) (((j : ℝ) + 1) / (2 : ℝ) ^ start i) →
        ‖F q.2 - F p.2 - (q.2 - p.2) • A p.2‖ ≤
          H * scalarDyadicLength (start i) ^ (11 / 10 : ℝ)) ∧
      ∃ L : ℝ → ℤ → Finset ℝ, (∀ t z, ((L t z).card : ℝ) ≤ H) ∧
        ∀ p ∈ E₁, ∃ v ∈ L p.2 ⌊zS F (c p.1) p.2 / scalarDyadicLength (start read)⌋,
          |v2FirstJet (c p.1) F A p.2 - v| ≤
            H * scalarDyadicLength (start read) ^ ((1 - d) / 32)

theorem V2FirstJetOutput.mono {Λ : Type*} [MeasurableSpace Λ] {m : ℕ} {ν : Measure Λ}
    {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ}
    {start : Fin m → ℕ} {read : Fin m} {d H H' : ℝ}
    (h : V2FirstJetOutput ν c E F start read d H) (hH : 0 < H) (hHH' : H ≤ H') :
    V2FirstJetOutput ν c E F start read d H' := by
  obtain ⟨E₁, hE₁E, hE₁m, hmass, A, hAm, hAb, hTaylor, L, hL, hcover⟩ := h
  refine ⟨E₁, hE₁E, hE₁m,
    (ENNReal.ofReal_le_ofReal (inv_anti₀ hH hHH')).trans hmass,
    A, hAm, fun p hp => (hAb p hp).trans hHH', ?_, L,
    fun t z => (hL t z).trans hHH', ?_⟩
  · intro i j p hp q hq hpi hqi
    exact (hTaylor i j p hp q hq hpi hqi).trans
      (mul_le_mul_of_nonneg_right hHH' (Real.rpow_nonneg (scalarDyadicLength_pos _).le _))
  · intro p hp
    obtain ⟨v, hv, hdist⟩ := hcover p hp
    exact ⟨v, hv, hdist.trans
      (mul_le_mul_of_nonneg_right hHH' (Real.rpow_nonneg (scalarDyadicLength_pos _).le _))⟩

/-- The subpower residual kernel for every trajectory type in `Type`. -/
theorem uniform_subpower_v2_residual_slopes_below_all_labels {ι : Type*}
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a d : ℝ} (ha : 0 < a) (hd0 : 0 ≤ d) (hd : d < 1) (j : ℝ) :
    ∃ Q : ℕ → ℝ, (∀ k, 1 ≤ Q k) ∧ SubpowerBound N Q ∧
      ∀ᶠ k in atTop, ∀ (Λ : Type) [MeasurableSpace Λ], ∀ p : ℝ, 0 < p → p ≤ N k ^ (-a) →
        OriginalScalarResidualAt (d := d) (j := j) Λ ι (K k) p (Q k)⁻¹ := by
  obtain ⟨ε, Q, _, _, hQeq, hQ, hQsub, hgood⟩ := exists_uniform_subpower_tolerance N hN
    (fun ε k => ∀ (Λ : Type) [MeasurableSpace Λ], ∀ p : ℝ, 0 < p → p ≤ N k ^ (-a) →
      OriginalScalarResidualAt (d := d) (j := j) Λ ι (K k) p (N k ^ (-ε)))
    (fun ε hε => uniform_original_residual_slopes_below_all_labels (ι := ι)
      N K hN hNt hK hsub ha hd0 hd hε j)
  refine ⟨Q, hQ, hQsub, ?_⟩
  filter_upwards [hgood] with k hk
  have he : N k ^ (-ε k) = (Q k)⁻¹ := by rw [hQeq k, Real.rpow_neg (zero_le_one.trans (hN k))]
  simpa only [he] using hk

/-- **The first jet at designated power-range levels** (version 2). -/
theorem uniform_v2_first_jet_between_powers_all_labels (hker : RangeFitStatement)
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) (m : ℕ) :
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧ SubpowerBound N H ∧
      ∀ᶠ k in atTop, ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsProbabilityMeasure ν]
        (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (ζ : ℝ)
        (start : Fin m → ℕ) (read : Fin m),
        UpperHyp ν c E F (K k) ζ d → 0 < ζ →
        (K k)⁻¹ ≤ (ν.prod volume).real E → ζ ≤ N k ^ (-(4 * b)) →
        (∀ i, N k ^ (-b) ≤ scalarDyadicLength (start i)) →
        (∀ i, scalarDyadicLength (start i) ≤ N k ^ (-a)) →
        V2FirstJetOutput ν c E F start read d (H k) := by
  obtain ⟨steps, hsteps⟩ := exists_uniform_scalar_dyadic_bridge_length ha hab
  let rows := Fintype.card (ScalarBridgeLabels m steps)
  have hrows : 0 < rows := Fintype.card_pos
  have hrows1 : (1 : ℝ) ≤ rows := by exact_mod_cast (Nat.succ_le_iff.mpr hrows : 1 ≤ rows)
  obtain ⟨B, hB, hKB, hBsub, hhierarchy⟩ :=
    uniform_v2_grid_hierarchy_between_powers hker N K hN hNt hK hsub ha hab hd0 hd rows
  let P : ℕ → ℝ := fun k => 4 * (rows : ℝ) * B k
  have hBP (k : ℕ) : B k ≤ P k := by
    simp only [P]
    have hb : 0 ≤ B k := zero_le_one.trans (hB k)
    have hh := mul_le_mul_of_nonneg_right hrows1 hb
    nlinarith
  have hP : ∀ k, 1 ≤ P k := fun k => (hB k).trans (hBP k)
  have hKP : ∀ k, K k ≤ P k := fun k => (hKB k).trans (hBP k)
  have hPsub : SubpowerBound N P :=
    subpower_mul (fun k => zero_lt_one.trans_le (hN k))
      (fun _ => by positivity) (fun k => zero_le_one.trans (hB k))
      (subpower_const hNt (4 * (rows : ℝ))) hBsub
  let W : ℕ → ℝ := fun k => v2ResidualBound (P k)
  have hW : ∀ k, 1 ≤ W k := fun k => (v2ResidualBound_bounds (hP k)).1
  have hWsub : SubpowerBound N W :=
    (subpower_polynomial hN hNt ⟨hP, hPsub⟩ (A := 1000000) (by norm_num) 10).2
  obtain ⟨Q, hQ, hQsub, hresidual⟩ :=
    uniform_subpower_v2_residual_slopes_below_all_labels (ι := Fin 2 → ℤ)
      N W hN hNt hW hWsub (a := a / 8) (by positivity) hd0 hd 2
  obtain ⟨hH, hHsub⟩ := v2FirstJetBudget_subpower N P Q hN hNt hP hQ hPsub hQsub steps
  refine ⟨fun k => v2FirstJetBudget steps (P k) (Q k), hH, hHsub, ?_⟩
  filter_upwards [hhierarchy, hresidual] with k hGk hRk
  intro Λ _ ν _ c E F ζ start read hnormal hζ hmass hζN hlow hhigh
  have hNpos : 0 < N k := zero_lt_one.trans_le (hN k)
  have hBpos : 0 < B k := zero_lt_one.trans_le (hB k)
  have hPpos : 0 < P k := zero_lt_one.trans_le (hP k)
  have hQpos : 0 < Q k := zero_lt_one.trans_le (hQ k)
  obtain ⟨imax, _, hmax⟩ := Finset.exists_max_image Finset.univ start ⟨read, Finset.mem_univ _⟩
  let top := start imax
  have hstart : ∀ i, start i ≤ top := fun i => hmax i (Finset.mem_univ _)
  have hweaklow : N k ^ (-(2 * b)) ≤ N k ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)
  have hweakhigh : N k ^ (-a) ≤ N k ^ (-(a / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)
  have hreach : ∀ i, scalarDyadicBridge top (start i) steps = top :=
    hsteps (N k) m top start (hN k) (hweaklow.trans (hlow imax))
      (fun i => (hhigh i).trans hweakhigh)
  let J : Fin rows → ℕ := fun i => 2 ^ scalarBridgeHeight top start i
  have hJ : ∀ i, 0 < J i := fun i => Nat.two_pow_pos _
  have hmeshrange (i : Fin rows) :
      N k ^ (-b) ≤ scalarBridgeMesh top start i ∧ scalarBridgeMesh top start i ≤ N k ^ (-a) :=
    scalarBridgeMesh_bounds top start hstart ⟨hlow imax, hhigh imax⟩ hhigh i
  have hJlow (i : Fin rows) : N k ^ (-b) ≤ 1 / (J i : ℝ) := by
    simpa only [J, scalarBridgeMesh, scalarDyadicLength_eq] using (hmeshrange i).1
  have hJhigh (i : Fin rows) : 1 / (J i : ℝ) ≤ N k ^ (-a) := by
    simpa only [J, scalarBridgeMesh, scalarDyadicLength_eq] using (hmeshrange i).2
  have hζJ (i : Fin rows) : ζ ≤ (1 / (J i : ℝ)) ^ 2 :=
    scalar_floor_square_of_power_range hNpos hζN (hweaklow.trans (hJlow i))
  obtain ⟨G⟩ := hGk Λ ν c E F ζ J hJ hnormal hζ hmass hJlow hJhigh hζJ
  obtain ⟨R, hRm, hRP, hmassR, hfloor⟩ :=
    (G.comp 0).exists_common_current_floor_set_of_pos hnormal.event_measurable hBpos hrows
  have hfloorR : ∀ q ∈ R, ∀ i : Fin rows,
      ENNReal.ofReal (scalarBridgeMesh top start i / P k) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ
          timeCell (2 ^ scalarBridgeHeight top start i)
            (scalarTimeBlockCode (2 ^ scalarBridgeHeight top start i) (by positivity) q.2))) := by
    intro q hq i
    simpa only [P, J, scalarBridgeMesh, scalarDyadicLength_eq] using hfloor q hq i
  have hζRead : ζ ≤ scalarDyadicLength (start read) ^ 2 :=
    scalar_floor_square_of_power_range hNpos hζN (hweaklow.trans (hlow read))
  have hreading : scalarDyadicLength (start read) ^ (1 / 8 : ℝ) ≤ N k ^ (-(a / 8)) := by
    calc
      _ ≤ (N k ^ (-a)) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow (scalarDyadicLength_pos _).le (hhigh read) (by norm_num)
      _ = _ := by
        rw [← Real.rpow_mul hNpos.le]
        congr 1
        ring
  have hconcentration := hRk Λ (scalarDyadicLength (start read) ^ (1 / 8 : ℝ))
    (Real.rpow_pos_of_pos (scalarDyadicLength_pos _) _) hreading
  obtain ⟨R', hR'm, hR'R, hmassR', htaylor, L, hL, hcover⟩ :=
    V2Hierarchy.exists_common_row_first_jet_restriction hstart hreach
      (zero_le_one.trans (hB k)) G read hnormal (hK k) hζ hd0 hd (hP k)
      (hKP k) (hBP k) (inv_nonneg.mpr hQpos.le) hRm hRP hfloorR hζRead hconcentration
  obtain ⟨hU1, hBU, hMassU, hCountU, hTaylorU, hReadU⟩ :=
    v2FirstJetBudget_bounds (steps := steps) (hP k) (hQ k)
      (zero_le_one.trans (hB k)) (hBP k) (zero_le_one.trans (hK k)) (hKP k)
  have hmassLower : (800000 * B k * P k ^ 8 * Q k)⁻¹ ≤ (ν.prod volume).real R' := by
    calc
      _ = (Q k)⁻¹ / (400000 * P k ^ 8) * (2 * B k)⁻¹ := by field_simp; ring
      _ ≤ (Q k)⁻¹ / (400000 * P k ^ 8) * (ν.prod volume).real R :=
        mul_le_mul_of_nonneg_left hmassR (by positivity)
      _ ≤ _ := hmassR'
  have hmassOutput : (v2FirstJetBudget steps (P k) (Q k))⁻¹ ≤ (ν.prod volume).real R' :=
    (inv_anti₀ (by positivity : 0 < 800000 * B k * P k ^ 8 * Q k) hMassU).trans hmassLower
  refine ⟨R', fun q hq => (hRP (hR'R hq)).1, hR'm,
    ENNReal.ofReal_le_of_le_toReal hmassOutput, G.slopeRow (scalarBridgeTopIndex m steps),
    G.measurable_slopeRow _, ?_, ?_, L, fun t z => (hL t z).trans hCountU, ?_⟩
  · intro q _
    refine norm_le_of_abs_le (zero_le_one.trans hU1) fun j => ?_
    exact ((G.comp j).bounded (scalarBridgeTopIndex m steps) q.2).1.trans hBU
  · intro i j q hq q' hq' hqi hq'i
    have hqtime := (G.comp 0).unit_time (hRP (hR'R hq)).2.2
    have hq'time := (G.comp 0).unit_time (hRP (hR'R hq')).2.2
    have hcode := scalarTimeBlockCode_eq_of_common_dyadic_interval hqtime hq'time hqi hq'i
    refine norm_le_of_abs_le (mul_nonneg (zero_le_one.trans hU1)
      (Real.rpow_nonneg (scalarDyadicLength_pos _).le _)) fun j' => ?_
    have hh := htaylor i q hq q' hq' hcode j'
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact hh.trans
      (mul_le_mul_of_nonneg_right hTaylorU (Real.rpow_nonneg (scalarDyadicLength_pos _).le _))
  · intro q hq
    obtain ⟨v, hv, hdist⟩ := hcover q hq
    exact ⟨v, hv, hdist.trans
      (mul_le_mul_of_nonneg_right hReadU (Real.rpow_nonneg (scalarDyadicLength_pos _).le _))⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
