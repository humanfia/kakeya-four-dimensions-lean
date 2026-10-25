/-
Adapted from this LOT tree, obligation o093, session x0535, commit b0d1e0aa,
Submission/Obl/k4_scalar_critical_path_terminal/GeometryPointStates.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TwoScaleDiameters

/-! Actual time, spatial and hidden coordinate diameters give finite
ambiguity of every tested point-state record. The estimate is explicit
before choosing a scale hierarchy or an entropy window. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GeometryPointStates

open Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

noncomputable section

def coordinates (z : Coeff × ℝ) : Fin 3 → ℝ :=
  ![z.2, spatial z.1 z.2, hidden z.1 z.2]

def pointStates {ι : Type*} (δ : ι → ℝ) : (Coeff × ℝ) → (ι × Fin 3 → ℤ) :=
  PointStateCounts.record (fun z i => coordinates z i.2) (fun i => δ i.1)

theorem measurable_pointStates {ι : Type*} (δ : ι → ℝ) : Measurable (pointStates δ) := by
  apply measurable_pi_iff.mpr
  rintro ⟨i, j⟩
  fin_cases j
  · change Measurable (fun z : Coeff × ℝ => (⌊z.2 / δ i⌋ : ℤ))
    exact (measurable_snd.div_const (δ i)).floor
  · change Measurable (fun z : Coeff × ℝ => (⌊spatial z.1 z.2 / δ i⌋ : ℤ))
    exact (measurable_spatial.div_const (δ i)).floor
  · change Measurable (fun z : Coeff × ℝ => (⌊hidden z.1 z.2 / δ i⌋ : ℤ))
    exact (measurable_hidden.div_const (δ i)).floor

def baseReadout {ι : Type*} (record : ι × Fin 3 → ℤ) (i : ι) : Fin 2 → ℤ :=
  ![record (i, 0), record (i, 1)]

def hiddenReadout {ι : Type*} (record : ι × Fin 3 → ℤ) (i : ι) : ℤ := record (i, 2)

def gridReadout {ι : Type*} (record : ι × Fin 3 → ℤ) :
    (ι → Fin 2 → ℤ) × (ι → ℤ) :=
  (fun i => baseReadout record i, fun i => hiddenReadout record i)

theorem baseReadout_pointStates {ι : Type*} (δ : ι → ℝ) (z : Coeff × ℝ) (i : ι) :
    baseReadout (pointStates δ z) i =
      fun e : Fin 2 => (⌊(![z.2, spatial z.1 z.2] : Fin 2 → ℝ) e / δ i⌋ : ℤ) := by
  funext e
  fin_cases e <;> rfl

theorem hiddenReadout_pointStates {ι : Type*} (δ : ι → ℝ) (z : Coeff × ℝ) (i : ι) :
    hiddenReadout (pointStates δ z) i = (⌊hidden z.1 z.2 / δ i⌋ : ℤ) := rfl

theorem gridReadout_pointStates {ι : Type*} (δ : ι → ℝ) (z : Coeff × ℝ) :
    gridReadout (pointStates δ z) =
      ((fun i (e : Fin 2) => (⌊(![z.2, spatial z.1 z.2] : Fin 2 → ℝ) e / δ i⌋ : ℤ)),
        fun i => (⌊hidden z.1 z.2 / δ i⌋ : ℤ)) := by
  apply Prod.ext
  · funext i e
    fin_cases e <;> rfl
  · rfl

/-- Any canonical encoding determined by the point record has the SAME
finite ambiguity bound. The returned finite range matches the measured
information-window hypothesis directly. -/
theorem finite_encoded_range {ι : Type*} (S : Set (Coeff × ℝ)) (δ : ι → ℝ)
    (hfinite : (pointStates δ '' S).Finite) (budget : ℕ)
    (hcard : (pointStates δ '' S).ncard ≤ budget)
    (Y : (Coeff × ℝ) → ℕ) (decode : (ι × Fin 3 → ℤ) → ℕ)
    (hY : ∀ z ∈ S, Y z = decode (pointStates δ z)) :
    ∃ U : Finset ℕ, U.card ≤ budget ∧ ∀ z ∈ S, Y z ∈ U := by
  classical
  let U := (hfinite.image decode).toFinset
  refine ⟨U, ?_, ?_⟩
  · have hle : (decode '' (pointStates δ '' S)).ncard ≤ (pointStates δ '' S).ncard :=
      Set.ncard_image_le hfinite
    rw [Set.ncard_eq_toFinset_card _ (hfinite.image decode)] at hle
    exact hle.trans hcard
  · intro z hz
    change Y z ∈ (hfinite.image decode).toFinset
    rw [(hfinite.image decode).mem_toFinset, hY z hz]
    exact ⟨pointStates δ z, ⟨z, hz, rfl⟩, rfl⟩

/-- Finite upper/lower block-count bounds give the actual duration
ratio required by the point-state ambiguity estimate. -/
theorem duration_ratio_le_rpow {N a b R : ℝ} {Tc Tf : ℕ} (hN : 1 ≤ N)
    (hcoarse : (2 : ℝ) ^ Tc ≤ N ^ a) (hfine : N ^ b ≤ (2 : ℝ) ^ Tf)
    (hgap : R ≤ b - a) :
    (((2 : ℝ) ^ Tf)⁻¹) / (((2 : ℝ) ^ Tc)⁻¹) ≤ N ^ (-R) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  rw [inv_div_inv]
  calc
    _ ≤ N ^ a / N ^ b := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ Tf)
        (Real.rpow_pos_of_pos hN0 b)).mpr
      exact mul_le_mul hcoarse hfine (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)
    _ = N ^ (a - b) := (Real.rpow_sub hN0 a b).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem finite_records_of_diameters {ι : Type*} [Fintype ι]
    (S : Set (Coeff × ℝ)) (δ : ι → ℝ) (A Dt Dy Dx : ℝ)
    (hδ : ∀ i, 0 < δ i) (hA : 0 ≤ A)
    (hdiam : ∀ z ∈ S, ∀ z' ∈ S,
      |z.2 - z'.2| ≤ Dt ∧
      |spatial z.1 z.2 - spatial z'.1 z'.2| ≤ Dy ∧
      |hidden z.1 z.2 - hidden z'.1 z'.2| ≤ Dx)
    (hscale : ∀ i, Dt ≤ A * δ i ∧ Dy ≤ A * δ i ∧ Dx ≤ A * δ i) :
    (pointStates δ '' S).Finite ∧
      ((pointStates δ '' S).ncard : ℝ) ≤ (2 * A + 2) ^ (3 * Fintype.card ι) := by
  have h := PointStateCounts.records_finite_card_of_relative_diameter S
    (fun z (i : ι × Fin 3) => coordinates z i.2) (fun i => δ i.1) A
    (fun i => hδ i.1) hA (by
      rintro ⟨i, j⟩ z hz z' hz'
      have hd := hdiam z hz z' hz'
      have hs := hscale i
      fin_cases j
      · change |z.2 - z'.2| ≤ A * δ i
        exact hd.1.trans hs.1
      · change |spatial z.1 z.2 - spatial z'.1 z'.2| ≤ A * δ i
        exact hd.2.1.trans hs.2.1
      · change |hidden z.1 z.2 - hidden z'.1 z'.2| ≤ A * δ i
        exact hd.2.2.trans hs.2.2)
  exact ⟨h.1, by simpa only [pointStates, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using h.2⟩

/-- Once the coarse fit and the actual duration ratio lie below the
finest tested mesh, appending ALL point states costs only a fixed power
of the common loss envelope. The number of tested depths is fixed first. -/
theorem two_scale_pointStates {ι : Type*} [Fintype ι]
    (S : Set (Coeff × ℝ)) (N K q q' rc R : ℝ) (s : ι → ℝ)
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hq : 0 < q) (hq1 : q ≤ 1) (hq' : 0 ≤ q')
    (hrc : R ≤ rc) (hs : ∀ i, s i ≤ R) (hratio : q' / q ≤ N ^ (-R))
    (hdiam : ∀ z ∈ S, ∀ z' ∈ S,
      |z.2 - z'.2| ≤ q' ∧
      |spatial z.1 z.2 - spatial z'.1 z'.2| ≤ 3 * K ^ 2 * q' ∧
      |hidden z.1 z.2 - hidden z'.1 z'.2| ≤
        2 * K * N ^ (-rc) + 47589120000000 * K ^ 26 * q' / q) :
    (pointStates (fun i => N ^ (-s i)) '' S).Finite ∧
      ((pointStates (fun i => N ^ (-s i)) '' S).ncard : ℝ) ≤
        (2 * (47589120000003 * K ^ 26) + 2) ^ (3 * Fintype.card ι) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hK0 : 0 ≤ K := by linarith
  have hK1 : K ≤ K ^ 26 := by simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ 26)
  have hK2 : K ^ 2 ≤ K ^ 26 := pow_le_pow_right₀ hK (by decide)
  have hK26 : 1 ≤ K ^ 26 := one_le_pow₀ hK
  have hA : 0 ≤ 47589120000003 * K ^ 26 := by positivity
  apply finite_records_of_diameters S (fun i => N ^ (-s i)) (47589120000003 * K ^ 26)
    q' (3 * K ^ 2 * q') (2 * K * N ^ (-rc) + 47589120000000 * K ^ 26 * q' / q)
    (fun _ => Real.rpow_pos_of_pos hN0 _) hA hdiam
  intro i
  have hδ : 0 ≤ N ^ (-s i) := Real.rpow_nonneg hN0.le _
  have hpowR : N ^ (-R) ≤ N ^ (-s i) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith [hs i])
  have hpowc : N ^ (-rc) ≤ N ^ (-s i) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith [hs i])
  have hqscale : q' ≤ N ^ (-s i) := by
    apply le_trans _ (hratio.trans hpowR)
    apply (le_div_iff₀ hq).mpr
    nlinarith
  have hA1 : 1 ≤ 47589120000003 * K ^ 26 := by nlinarith
  have hA2 : 3 * K ^ 2 ≤ 47589120000003 * K ^ 26 := by nlinarith
  have hA3 : 2 * K + 47589120000000 * K ^ 26 ≤ 47589120000003 * K ^ 26 := by nlinarith
  refine ⟨hqscale.trans ?_, ?_, ?_⟩
  · simpa using mul_le_mul_of_nonneg_right hA1 hδ
  · exact (mul_le_mul_of_nonneg_left hqscale (by positivity : 0 ≤ 3 * K ^ 2)).trans
      (mul_le_mul_of_nonneg_right hA2 hδ)
  · calc
      _ ≤ 2 * K * N ^ (-s i) + 47589120000000 * K ^ 26 * N ^ (-s i) := by
        apply add_le_add (mul_le_mul_of_nonneg_left hpowc (by positivity))
        have hmul := mul_le_mul_of_nonneg_left (hratio.trans hpowR)
          (show 0 ≤ 47589120000000 * K ^ 26 by positivity)
        convert hmul using 1
        ring
      _ = (2 * K + 47589120000000 * K ^ 26) * N ^ (-s i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hA3 hδ

/-- The tangent resolution is N0^scale. All chart fits and duration
comparisons stay in their ORIGINAL N0 units, with tested depths scale*s. -/
theorem two_scale_pointStates_powerScale {ι : Type*} [Fintype ι]
    (S : Set (Coeff × ℝ)) (N0 scale K q q' rc R : ℝ) (s : ι → ℝ)
    (hN : 1 ≤ N0) (hscale : 0 ≤ scale) (hK : 1 ≤ K)
    (hq : 0 < q) (hq1 : q ≤ 1) (hq' : 0 ≤ q')
    (hrc : scale * R ≤ rc) (hs : ∀ i, s i ≤ R)
    (hratio : q' / q ≤ N0 ^ (-(scale * R)))
    (hdiam : ∀ z ∈ S, ∀ z' ∈ S,
      |z.2 - z'.2| ≤ q' ∧
      |spatial z.1 z.2 - spatial z'.1 z'.2| ≤ 3 * K ^ 2 * q' ∧
      |hidden z.1 z.2 - hidden z'.1 z'.2| ≤
        2 * K * N0 ^ (-rc) + 47589120000000 * K ^ 26 * q' / q) :
    (pointStates (fun i => (N0 ^ scale) ^ (-s i)) '' S).Finite ∧
      ((pointStates (fun i => (N0 ^ scale) ^ (-s i)) '' S).ncard : ℝ) ≤
        (2 * (47589120000003 * K ^ 26) + 2) ^ (3 * Fintype.card ι) := by
  have h := two_scale_pointStates S N0 K q q' rc (scale * R) (fun i => scale * s i)
    hN hK hq hq1 hq' hrc (fun i => mul_le_mul_of_nonneg_left (hs i) hscale) hratio hdiam
  have heq : (fun i => (N0 ^ scale) ^ (-s i)) = (fun i => N0 ^ (-(scale * s i))) := by
    funext i
    rw [← Real.rpow_mul (zero_le_one.trans hN)]
    congr 1
    ring
  rw [heq]
  exact h

/-- A strict depth and duration margin absorbs the common polynomial loss
before counting point records. The resulting coordinate diameter is one
finest mesh, independent of the common loss envelope. -/
theorem two_scale_diameters_le_mesh {N K q q' rc a buffer : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hq : 0 < q) (hq1 : q ≤ 1) (hq' : 0 ≤ q')
    (hrc : a + buffer ≤ rc) (hratio : q' / q ≤ N ^ (-(a + buffer)))
    (hmargin : 47589120000003 * K ^ 26 ≤ N ^ buffer)
    {z z' : Coeff × ℝ}
    (hdiam : |z.2 - z'.2| ≤ q' ∧
      |spatial z.1 z.2 - spatial z'.1 z'.2| ≤ 3 * K ^ 2 * q' ∧
      |hidden z.1 z.2 - hidden z'.1 z'.2| ≤
        2 * K * N ^ (-rc) + 47589120000000 * K ^ 26 * q' / q) :
    |z.2 - z'.2| ≤ N ^ (-a) ∧
      |spatial z.1 z.2 - spatial z'.1 z'.2| ≤ N ^ (-a) ∧
      |hidden z.1 z.2 - hidden z'.1 z'.2| ≤ N ^ (-a) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hK0 : 0 ≤ K := by linarith
  have hK1 : K ≤ K ^ 26 := by simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ 26)
  have hK2 : K ^ 2 ≤ K ^ 26 := pow_le_pow_right₀ hK (by decide)
  have hK26 : 1 ≤ K ^ 26 := one_le_pow₀ hK
  have hA1 : 1 ≤ 47589120000003 * K ^ 26 := by nlinarith
  have hA2 : 3 * K ^ 2 ≤ 47589120000003 * K ^ 26 := by nlinarith
  have hA3 : 2 * K + 47589120000000 * K ^ 26 ≤ 47589120000003 * K ^ 26 := by nlinarith
  have hp0 : 0 ≤ N ^ (-(a + buffer)) := Real.rpow_nonneg hN0.le _
  have hqscale : q' ≤ N ^ (-(a + buffer)) := by
    apply le_trans _ hratio
    apply (le_div_iff₀ hq).mpr
    nlinarith
  have hpowc : N ^ (-rc) ≤ N ^ (-(a + buffer)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hfinish : (47589120000003 * K ^ 26) * N ^ (-(a + buffer)) ≤ N ^ (-a) := by
    calc
      _ ≤ N ^ buffer * N ^ (-(a + buffer)) := mul_le_mul_of_nonneg_right hmargin hp0
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  refine ⟨hdiam.1.trans (hqscale.trans ?_), hdiam.2.1.trans ?_, hdiam.2.2.trans ?_⟩
  · have hle : N ^ (-(a + buffer)) ≤
        (47589120000003 * K ^ 26) * N ^ (-(a + buffer)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA1 hp0
    exact hle.trans hfinish
  · exact ((mul_le_mul_of_nonneg_left hqscale (by positivity : 0 ≤ 3 * K ^ 2)).trans
      (mul_le_mul_of_nonneg_right hA2 hp0)).trans hfinish
  · calc
      _ ≤ 2 * K * N ^ (-(a + buffer)) +
          47589120000000 * K ^ 26 * N ^ (-(a + buffer)) := by
        apply add_le_add (mul_le_mul_of_nonneg_left hpowc (by positivity))
        convert mul_le_mul_of_nonneg_left hratio
          (show 0 ≤ 47589120000000 * K ^ 26 by positivity) using 1 <;> ring
      _ = (2 * K + 47589120000000 * K ^ 26) * N ^ (-(a + buffer)) := by ring
      _ ≤ (47589120000003 * K ^ 26) * N ^ (-(a + buffer)) :=
        mul_le_mul_of_nonneg_right hA3 hp0
      _ ≤ _ := hfinish

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GeometryPointStates
