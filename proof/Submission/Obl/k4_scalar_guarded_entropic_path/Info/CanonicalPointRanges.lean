import Submission.Obl.k4_scalar_guarded_entropic_path.Info.Canonical
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GeometryPointStates
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GeometryDiameters

/-! Explicit finite ranges for the canonical base/hidden record on an
actual fine original chart row, from the unchanged current coarse floor. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open MeasureTheory Set
open scoped ENNReal
open PathGeometry
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

noncomputable section

/-- The canonical grid part is the literal three-coordinate point record. -/
theorem gridReadout_pointStates_eq (N : ℝ) (m : ℕ) (z : Incidence) :
    GeometryPointStates.gridReadout
      (GeometryPointStates.pointStates (fun j : Fin (m ^ 2 + 1) =>
        N ^ (-((j : ℝ) / (m : ℝ)))) z) = gridPart N m z := by
  apply Prod.ext
  · funext j e
    fin_cases e <;> rfl
  · rfl

/-- Transfer a point-state ambiguity bound to the canonical Y record,
with exactly the integer budget expected by the measured window theorem. -/
theorem canonical_range_of_pointStates (N : ℝ) (m : ℕ) (Mb : ℤ)
    (A : Set Incidence)
    (hbox : ∀ z ∈ A, gridTuple N m z ∈ boxSet m Mb)
    (hfinite : (GeometryPointStates.pointStates
      (fun j : Fin (m ^ 2 + 1) => N ^ (-((j : ℝ) / (m : ℝ)))) '' A).Finite)
    (budget : ℕ)
    (hcard : (GeometryPointStates.pointStates
      (fun j : Fin (m ^ 2 + 1) => N ^ (-((j : ℝ) / (m : ℝ)))) '' A).ncard ≤ budget) :
    ∃ U : Finset ℕ, U.card ≤ budget ∧
      ∀ z ∈ A, canonY m Mb (canonX N m Mb z) ∈ U := by
  apply GeometryPointStates.finite_encoded_range A
    (fun j : Fin (m ^ 2 + 1) => N ^ (-((j : ℝ) / (m : ℝ)))) hfinite budget hcard
    (fun z => canonY m Mb (canonX N m Mb z))
    (fun record => gridEnc m (GeometryPointStates.gridReadout record))
  intro z hz
  rw [canonY_canonX (hbox z hz), gridReadout_pointStates_eq]

/-- The explicit geometric record cost, rounded once to a natural number. -/
def pointRangeBudget (K : ℝ) (m : ℕ) : ℕ :=
  ⌈(2 * (47589120000003 * K ^ 26) + 2) ^ (3 * (m ^ 2 + 1))⌉₊

/-- All tangent tests j/m lie below the finest test m. -/
theorem test_depth_le {m : ℕ} (hm : 1 ≤ m) (j : Fin (m ^ 2 + 1)) :
    (j : ℝ) / (m : ℝ) ≤ (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  apply (div_le_iff₀ hm0).mpr
  have hj : j.val ≤ m ^ 2 := by omega
  exact_mod_cast (by simpa only [pow_two] using hj)

/-- Actual original-unit diameters give the exact finite canonical range
at tangent resolution N0^scale. The same Mb is used by every window. -/
theorem canonical_range_of_two_scale_diameters (A : Set Incidence)
    (N0 scale K q q' rc : ℝ) (m : ℕ) (Mb : ℤ)
    (hN : 1 ≤ N0) (hscale : 0 ≤ scale) (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hq : 0 < q) (hq1 : q ≤ 1) (hq' : 0 ≤ q')
    (hrc : scale * (m : ℝ) ≤ rc)
    (hratio : q' / q ≤ N0 ^ (-(scale * (m : ℝ))))
    (hbox : ∀ z ∈ A, gridTuple (N0 ^ scale) m z ∈ boxSet m Mb)
    (hdiam : ∀ z ∈ A, ∀ z' ∈ A,
      |z.2 - z'.2| ≤ q' ∧
      |spatial z.1 z.2 - spatial z'.1 z'.2| ≤ 3 * K ^ 2 * q' ∧
      |hidden z.1 z.2 - hidden z'.1 z'.2| ≤
        2 * K * N0 ^ (-rc) + 47589120000000 * K ^ 26 * q' / q) :
    ∃ U : Finset ℕ, U.card ≤ pointRangeBudget K m ∧
      ∀ z ∈ A, canonY m Mb (canonX (N0 ^ scale) m Mb z) ∈ U := by
  obtain ⟨hfinite, hcard⟩ := GeometryPointStates.two_scale_pointStates_powerScale
    A N0 scale K q q' rc (m : ℝ) (fun j : Fin (m ^ 2 + 1) => (j : ℝ) / (m : ℝ))
    hN hscale hK hq hq1 hq' hrc (test_depth_le hm) hratio hdiam
  apply canonical_range_of_pointStates (N0 ^ scale) m Mb A hbox hfinite (pointRangeBudget K m)
  apply (Nat.cast_le (α := ℝ)).mp
  have hcard' : ((GeometryPointStates.pointStates
      (fun j : Fin (m ^ 2 + 1) => (N0 ^ scale) ^ (-((j : ℝ) / (m : ℝ)))) '' A).ncard : ℝ) ≤
      (2 * (47589120000003 * K ^ 26) + 2) ^ (3 * (m ^ 2 + 1)) := by
    simpa only [Fintype.card_fin] using hcard
  exact hcard'.trans (Nat.le_ceil _)

/-- A finest-mesh coordinate diameter costs four choices per tested
coordinate, regardless of the absolute position of the row. -/
theorem canonical_range_of_mesh_diameters (A : Set Incidence)
    (N : ℝ) (m : ℕ) (Mb : ℤ) (hN : 1 ≤ N) (hm : 1 ≤ m)
    (hbox : ∀ z ∈ A, gridTuple N m z ∈ boxSet m Mb)
    (hdiam : ∀ z ∈ A, ∀ z' ∈ A,
      |z.2 - z'.2| ≤ N ^ (-(m : ℝ)) ∧
      |spatial z.1 z.2 - spatial z'.1 z'.2| ≤ N ^ (-(m : ℝ)) ∧
      |hidden z.1 z.2 - hidden z'.1 z'.2| ≤ N ^ (-(m : ℝ))) :
    ∃ U : Finset ℕ, U.card ≤ 4 ^ (3 * (m ^ 2 + 1)) ∧
      ∀ z ∈ A, canonY m Mb (canonX N m Mb z) ∈ U := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  obtain ⟨hfinite, hcard⟩ := GeometryPointStates.finite_records_of_diameters A
    (fun j : Fin (m ^ 2 + 1) => N ^ (-((j : ℝ) / (m : ℝ))))
    1 (N ^ (-(m : ℝ))) (N ^ (-(m : ℝ))) (N ^ (-(m : ℝ)))
    (fun _ => Real.rpow_pos_of_pos hN0 _) (by norm_num) hdiam (by
      intro j
      have hj := Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (test_depth_le hm j))
      simpa only [one_mul] using And.intro hj (And.intro hj hj))
  apply canonical_range_of_pointStates N m Mb A hbox hfinite _
  have hbound : ((GeometryPointStates.pointStates
      (fun j : Fin (m ^ 2 + 1) => N ^ (-((j : ℝ) / (m : ℝ)))) '' A).ncard : ℝ) ≤
      (4 : ℝ) ^ (3 * (m ^ 2 + 1)) := by
    simpa only [Fintype.card_fin, mul_one, show (2 : ℝ) + 2 = 4 by norm_num] using hcard
  exact_mod_cast hbound

/-- A spare original depth and duration margin absorbs the polynomial
loss, leaving a constant finite ambiguity at the tangent grid. -/
theorem canonical_range_of_strict_two_scale_diameters (A : Set Incidence)
    (N0 scale K q q' rc : ℝ) (m : ℕ) (Mb : ℤ)
    (hN : 1 ≤ N0) (hscale : 0 ≤ scale) (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hq : 0 < q) (hq1 : q ≤ 1) (hq' : 0 ≤ q')
    (hrc : scale * ((m : ℝ) + 1) ≤ rc)
    (hratio : q' / q ≤ N0 ^ (-(scale * ((m : ℝ) + 1))))
    (hmargin : 47589120000003 * K ^ 26 ≤ N0 ^ scale)
    (hbox : ∀ z ∈ A, gridTuple (N0 ^ scale) m z ∈ boxSet m Mb)
    (hdiam : ∀ z ∈ A, ∀ z' ∈ A,
      |z.2 - z'.2| ≤ q' ∧
      |spatial z.1 z.2 - spatial z'.1 z'.2| ≤ 3 * K ^ 2 * q' ∧
      |hidden z.1 z.2 - hidden z'.1 z'.2| ≤
        2 * K * N0 ^ (-rc) + 47589120000000 * K ^ 26 * q' / q) :
    ∃ U : Finset ℕ, U.card ≤ 4 ^ (3 * (m ^ 2 + 1)) ∧
      ∀ z ∈ A, canonY m Mb (canonX (N0 ^ scale) m Mb z) ∈ U := by
  apply canonical_range_of_mesh_diameters A (N0 ^ scale) m Mb (Real.one_le_rpow hN hscale) hm hbox
  intro z hz z' hz'
  have hr : scale * (m : ℝ) + scale ≤ rc := by nlinarith [hrc]
  have hratio' : q' / q ≤ N0 ^ (-(scale * (m : ℝ) + scale)) := by
    simpa only [mul_add, mul_one] using hratio
  have hd := GeometryPointStates.two_scale_diameters_le_mesh hN hK hq hq1 hq' hr hratio'
    hmargin (hdiam z hz z' hz')
  have heq : (N0 ^ scale) ^ (-(m : ℝ)) = N0 ^ (-(scale * (m : ℝ))) := by
    rw [← Real.rpow_mul (zero_le_one.trans hN)]
    congr 1
    ring
  simpa only [heq] using hd

/-- The canonical range bound on ONE actual fine original row. Its coarse
packet uses the same full original assignment and current law. -/
theorem canonical_range_of_actual_rows {p : Code} (hp : Exact p)
    {k Bc Bf : ℕ} {rc bc hc εc rf bf hf εf : ℝ} {flag : Bool}
    (Qc : Submission.Obl.k4_scalar_true_terminal_lifting.ChartW p Bc rc bc hc εc true k)
    (Qf : Submission.Obl.k4_scalar_true_terminal_lifting.ChartW p Bf rf bf hf εf flag k)
    (π : ChartGeometry.RowProjection (ChartGeometry.ofChart Qc) (ChartGeometry.ofChart Qf))
    (d : Fin Qf.n) (scale B H K : ℝ) (m : ℕ)
    (hscale : 0 ≤ scale) (hB : 0 < B) (hH : 0 < H) (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hrc : 0 ≤ rc) (hεc : 0 ≤ εc)
    (hXc : N p k ^ εc ≤ K) (hXf : N p k ^ εf ≤ K) (hBK : B ≤ K) (hHK : H ≤ K)
    (hwidth : (K * (2 : ℝ) ^ Qc.T)⁻¹ ≤ Qc.J (π.row d))
    (ρ : Measure Incidence)
    (hcap : ρ.map (obsL (N p k ^ (-rc))) ≤
      ENNReal.ofReal (B * N p k ^ (-f p rc)) • (volume.prod Measure.count))
    (hfloor : (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ Qc.T)⁻¹) *
      ν p k (Qc.γ (π.row d)) (Qc.A (π.row d)) ≤
      ρ (Qc.A (π.row d) ×ˢ I Qc.T (Qc.j (π.row d))))
    (hrcm : scale * (m : ℝ) ≤ rc)
    (hratio : (((2 : ℝ) ^ Qf.T)⁻¹) / (((2 : ℝ) ^ Qc.T)⁻¹) ≤
      N p k ^ (-(scale * (m : ℝ)))) :
    ∃ U : Finset ℕ, U.card ≤ pointRangeBudget K m ∧
      ∀ z ∈ Qf.C d,
        canonY m (canonM ((N p k) ^ scale) K m)
          (canonX ((N p k) ^ scale) m (canonM ((N p k) ^ scale) K m) z) ∈ U := by
  have hN : 1 ≤ N p k := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 k)
  apply canonical_range_of_two_scale_diameters (Qf.C d) (N p k) scale K
    (((2 : ℝ) ^ Qc.T)⁻¹) (((2 : ℝ) ^ Qf.T)⁻¹) rc m
    (canonM ((N p k) ^ scale) K m) hN hscale hK hm (by positivity)
    (by exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
    (by positivity) hrcm hratio
  · intro z hz
    have hzA := ((Qf.hcd.2.2.2.2.1 d) hz).2
    have ht := Submission.Obl.k4_scalar_true_atlas_terminal_lists.I_subset_unit Qf.T (Qf.j d) hzA.2
    rcases Qf.hcd.2.2.2.2.2.1 d with
      ⟨_, _, _, _, _, _, _, hcoeff, _⟩
    have hl : ∀ e, |z.1.2 e| ≤ K := fun e => ((hcoeff z.1 hzA.1).2 e).trans hXf
    exact gridTuple_mem_boxSet (Real.one_le_rpow hN hscale) hK hm ht hl
  · intro z hz z' hz'
    exact ChartGeometry.incidence_diameters hp (ChartGeometry.ofChart Qc)
      (ChartGeometry.ofChart Qf) Qc.Λ Qf.Λ Qc.hcd Qf.hcd π d hrc hεc
      ρ B H K hB hH hK hXc hXf hBK hHK hwidth hcap hfloor z z' hz hz'

/-- The strict-margin constant-cost version on the actual original rows. -/
theorem canonical_range_of_strict_actual_rows {p : Code} (hp : Exact p)
    {k Bc Bf : ℕ} {rc bc hc εc rf bf hf εf : ℝ} {flag : Bool}
    (Qc : Submission.Obl.k4_scalar_true_terminal_lifting.ChartW p Bc rc bc hc εc true k)
    (Qf : Submission.Obl.k4_scalar_true_terminal_lifting.ChartW p Bf rf bf hf εf flag k)
    (π : ChartGeometry.RowProjection (ChartGeometry.ofChart Qc) (ChartGeometry.ofChart Qf))
    (d : Fin Qf.n) (scale B H K : ℝ) (m : ℕ)
    (hscale : 0 ≤ scale) (hB : 0 < B) (hH : 0 < H) (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hrc : 0 ≤ rc) (hεc : 0 ≤ εc)
    (hXc : N p k ^ εc ≤ K) (hXf : N p k ^ εf ≤ K) (hBK : B ≤ K) (hHK : H ≤ K)
    (hwidth : (K * (2 : ℝ) ^ Qc.T)⁻¹ ≤ Qc.J (π.row d))
    (ρ : Measure Incidence)
    (hcap : ρ.map (obsL (N p k ^ (-rc))) ≤
      ENNReal.ofReal (B * N p k ^ (-f p rc)) • (volume.prod Measure.count))
    (hfloor : (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ Qc.T)⁻¹) *
      ν p k (Qc.γ (π.row d)) (Qc.A (π.row d)) ≤
      ρ (Qc.A (π.row d) ×ˢ I Qc.T (Qc.j (π.row d))))
    (hrcm : scale * ((m : ℝ) + 1) ≤ rc)
    (hratio : (((2 : ℝ) ^ Qf.T)⁻¹) / (((2 : ℝ) ^ Qc.T)⁻¹) ≤
      N p k ^ (-(scale * ((m : ℝ) + 1))))
    (hmargin : 47589120000003 * K ^ 26 ≤ N p k ^ scale) :
    ∃ U : Finset ℕ, U.card ≤ 4 ^ (3 * (m ^ 2 + 1)) ∧
      ∀ z ∈ Qf.C d,
        canonY m (canonM ((N p k) ^ scale) K m)
          (canonX ((N p k) ^ scale) m (canonM ((N p k) ^ scale) K m) z) ∈ U := by
  have hN : 1 ≤ N p k := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 k)
  apply canonical_range_of_strict_two_scale_diameters (Qf.C d) (N p k) scale K
    (((2 : ℝ) ^ Qc.T)⁻¹) (((2 : ℝ) ^ Qf.T)⁻¹) rc m
    (canonM ((N p k) ^ scale) K m) hN hscale hK hm (by positivity)
    (by exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
    (by positivity) hrcm hratio hmargin
  · intro z hz
    have hzA := ((Qf.hcd.2.2.2.2.1 d) hz).2
    have ht := Submission.Obl.k4_scalar_true_atlas_terminal_lists.I_subset_unit Qf.T (Qf.j d) hzA.2
    rcases Qf.hcd.2.2.2.2.2.1 d with
      ⟨_, _, _, _, _, _, _, hcoeff, _⟩
    have hl : ∀ e, |z.1.2 e| ≤ K := fun e => ((hcoeff z.1 hzA.1).2 e).trans hXf
    exact gridTuple_mem_boxSet (Real.one_le_rpow hN hscale) hK hm ht hl
  · intro z hz z' hz'
    exact ChartGeometry.incidence_diameters hp (ChartGeometry.ofChart Qc)
      (ChartGeometry.ofChart Qf) Qc.Λ Qf.Λ Qc.hcd Qf.hcd π d hrc hεc
      ρ B H K hB hH hK hXc hXf hBK hHK hwidth hcap hfloor z z' hz hz'

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
