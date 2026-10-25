import Submission.Obl.k4_raw_localized_native_systems.Assembly
import Submission.Obl.k4_raw_localized_native_systems.Choice
import Submission.Obl.k4_raw_localized_native_systems.C.OneSample
import Submission.Obl.k4_raw_localized_native_systems.C.ForestLevel

/-!
# The per-sequence assembly

Glue between the C construction (adapted from o178/x0596 under `C/`), the
certificate side `DSide` (the raw earlier-witness certificate along one
homogeneous source sequence) and the top layer `SourceSamples`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_raw_critical_segment_forests

noncomputable section

/-- The generic native sample of the C construction is the sample of the
frozen statement for the same certificate. -/
theorem nativeSampleWith_of_cert {cert : CertificateType} {N K : ℝ} {W : ℕ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {P : Fin W → MvPolynomial (Fin 4) ℝ}
    {B : Fin W → ℝ} {M D : ℕ} {a₀ w loss h χ d s m S U : ℝ}
    (hs : C.NativeSampleCert cert N K W ω ν E P B M D a₀ w loss h χ d s m S U) :
    NativeSampleWith cert false N K W ω ν E P B M D a₀ w loss h χ d s m S U := by
  obtain ⟨T, C', γ, j, c, u, Q, A, F, lst, α, v, law, Y, X, hs⟩ := hs
  exact ⟨T, C', γ, j, c, u, Q, A, F, lst, α, v, law, Y, X, hs⟩

/-- Eventual properties along a strictly increasing index are frequent. -/
theorem frequently_of_eventually_index {φ : ℕ → ℕ} (hφ : StrictMono φ) {P : ℕ → Prop}
    (h : ∀ᶠ n in atTop, P (φ n)) : ∃ᶠ k in atTop, P k :=
  hφ.tendsto_atTop.frequently h.frequently

/-- **The certificate side along one homogeneous source sequence.**  One
omission exponent `a₀` and one loss threshold `ℓ` are fixed first; for every
smaller positive loss, at all late samples, every family of full-time charts
delivered by the C construction from the later level (`C.CFam`, at any format
and lists, at a common strip width `g` that is at most `N^(-ϑ)` times the minor
width of every earlier chart divided by its block length) has good sets of
omission at most `N^(-a₀)` and a raw certificate on every positive re-indexing
(`C.DStep`). -/
def DSide (p : Data) {kr w' ε q band : ℝ} {M D : ℕ} {sd r : ℕ → ℝ}
    (src : HomogeneousSourceSequence p kr w' ε q band 2 M D sd r)
    (χ d s m ϑ : ℝ) : Prop :=
  ∃ a₀ ℓ : ℝ, 0 < a₀ ∧ 0 < ℓ ∧ ∀ loss : ℝ, 0 < loss → loss ≤ ℓ → ∀ᶠ n in atTop,
    ∀ (MC DC : ℕ)
      (Λ : Fin (p.W (src.index n)) → Observation →
        Finset (Fin (C.levelSet (src.forest n) 1).card)) (g : ℝ),
      0 < g → g ≤ 1 →
      (∀ b : Fin (src.forest n).C, (src.forest n).lev b = 0 →
        g ≤ p.N (src.index n) ^ (-ϑ) * C.minorWidth ((src.forest n).Q b) /
          (2 : ℝ) ^ (src.forest n).T 0) →
      C.DStep RawSupport p (src.index n) (C.levelAtlas (src.forest n) 1 Λ) MC DC loss g a₀
        χ d s m


/-- A column of a planar matrix is at most the sum of the absolute entries. -/
theorem norm_longCol_le_sum (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖C.longCol Q‖ ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| := by
  have hsum : ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| =
      |Q 0 0| + |Q 0 1| + (|Q 1 0| + |Q 1 1|) := by
    simp [Fin.sum_univ_two]
  rw [hsum]
  have hcol : ∀ a : EuclideanSpace ℝ (Fin 2), ‖a‖ ≤ |a 0| + |a 1| := by
    intro a
    have h := C.norm_sq_fin2' a
    have hn : 0 ≤ ‖a‖ := norm_nonneg a
    have h0 : 0 ≤ |a 0| + |a 1| := by positivity
    rw [← abs_of_nonneg hn, ← abs_of_nonneg h0]
    apply sq_le_sq.mp
    rw [h]
    have h0' : a 0 ^ 2 = |a 0| ^ 2 := (sq_abs _).symm
    have h1' : a 1 ^ 2 = |a 1| ^ 2 := (sq_abs _).symm
    rw [h0', h1']
    nlinarith [abs_nonneg (a 0), abs_nonneg (a 1)]
  unfold C.longCol
  split_ifs
  · refine (hcol _).trans ?_
    simp only [C.col0_apply0, C.col0_apply1]
    linarith [abs_nonneg (Q 0 1), abs_nonneg (Q 1 1)]
  · refine (hcol _).trans ?_
    simp only [C.col1_apply0, C.col1_apply1]
    linarith [abs_nonneg (Q 0 0), abs_nonneg (Q 1 0)]

/-- **The relative width of the full-time charts.**  A common strip width below
`N^(-(nw 1 - band) + A)` is at most `N^(-ϑ)` times the minor width of every
earlier chart over its block length, once the homogeneous later width exceeds
the earlier one by the gap `2 band + ϑ + 2 h + e + A`. -/
theorem relative_width_at {p : Data} (hp : Valid p) {k M D : ℕ} {r : ℕ → ℝ}
    {F : Forest p k} (hcore : F.Core M D 2 r) {width : Fin F.C → ℝ} {nw : ℕ → ℝ}
    {band g A h e ϑ : ℝ}
    (hexact : ∀ b, p.N k ^ (-width b) = |(F.Q b).det| * (4 : ℝ) ^ F.T (F.lev b))
    (hband : ∀ b, |width b - nw (F.lev b)| ≤ band)
    (hT : (2 : ℝ) ^ F.T 0 ≤ p.N k ^ h) (hκ : F.κ ≤ p.N k ^ e)
    (hg : g ≤ p.N k ^ (-(nw 1 - band) + A))
    (hgap : nw 0 + 2 * band + ϑ + 2 * h + e + A ≤ nw 1) :
    ∀ b, F.lev b = 0 → g ≤ p.N k ^ (-ϑ) * C.minorWidth (F.Q b) / (2 : ℝ) ^ F.T 0 := by
  intro b hb
  have hN1 : 1 ≤ p.N k := hp.scale_ge_one k
  have hN0 : 0 < p.N k := hp.scale_pos k
  obtain ⟨-, hbT, hchart, -⟩ := hcore.2.2.2.2.2 b
  rw [hb] at hchart
  have hdet : (F.Q b).det ≠ 0 := hchart.1
  have hdetpos : 0 < |(F.Q b).det| := abs_pos.mpr hdet
  have hsumQ : ∑ e : Fin 2, ∑ e' : Fin 2, |F.Q b e e'| ≤ F.κ / (2 : ℝ) ^ F.T 0 :=
    hchart.2.2.2.1
  have hlong := norm_longCol_le_sum (F.Q b)
  have hlongpos : 0 < ‖C.longCol (F.Q b)‖ := C.longCol_norm_pos hdet
  have hκpos : 0 < F.κ := by linarith [hcore.1]
  have h2T : (0 : ℝ) < (2 : ℝ) ^ F.T 0 := by positivity
  -- the determinant from the exact width and the band
  have hwb : width b ≤ nw 0 + band := by
    have := hband b; rw [hb] at this; rw [abs_le] at this; linarith
  have hdet_lower : p.N k ^ (-(nw 0 + band)) * ((4 : ℝ) ^ F.T 0)⁻¹ ≤ |(F.Q b).det| := by
    have hex := hexact b
    rw [hb] at hex
    have h4 : (0 : ℝ) < (4 : ℝ) ^ F.T 0 := by positivity
    have hmono : p.N k ^ (-(nw 0 + band)) ≤ p.N k ^ (-width b) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [hex] at hmono
    calc p.N k ^ (-(nw 0 + band)) * ((4 : ℝ) ^ F.T 0)⁻¹
        ≤ |(F.Q b).det| * (4 : ℝ) ^ F.T 0 * ((4 : ℝ) ^ F.T 0)⁻¹ :=
          mul_le_mul_of_nonneg_right hmono (by positivity)
      _ = |(F.Q b).det| := by field_simp
  -- the minor width
  have hminor : p.N k ^ (-(nw 0 + band)) * ((4 : ℝ) ^ F.T 0)⁻¹ * ((2 : ℝ) ^ F.T 0 / F.κ) ≤
      C.minorWidth (F.Q b) := by
    unfold C.minorWidth
    rw [le_div_iff₀ hlongpos]
    calc p.N k ^ (-(nw 0 + band)) * ((4 : ℝ) ^ F.T 0)⁻¹ * ((2 : ℝ) ^ F.T 0 / F.κ) *
          ‖C.longCol (F.Q b)‖
        ≤ p.N k ^ (-(nw 0 + band)) * ((4 : ℝ) ^ F.T 0)⁻¹ * ((2 : ℝ) ^ F.T 0 / F.κ) *
          (F.κ / (2 : ℝ) ^ F.T 0) :=
          mul_le_mul_of_nonneg_left (hlong.trans hsumQ) (by positivity)
      _ = p.N k ^ (-(nw 0 + band)) * ((4 : ℝ) ^ F.T 0)⁻¹ := by field_simp
      _ ≤ |(F.Q b).det| := hdet_lower
  -- the right side dominates one explicit power
  have h4eq : (4 : ℝ) ^ F.T 0 = (2 : ℝ) ^ F.T 0 * (2 : ℝ) ^ F.T 0 := by
    rw [← mul_pow]; norm_num
  have hrhs : p.N k ^ (-ϑ) * (p.N k ^ (-(nw 0 + band)) * (p.N k ^ (2 * h))⁻¹ * (p.N k ^ e)⁻¹) ≤
      p.N k ^ (-ϑ) * C.minorWidth (F.Q b) / (2 : ℝ) ^ F.T 0 := by
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [le_div_iff₀ h2T]
    refine le_trans ?_ hminor
    have hT2 : (2 : ℝ) ^ F.T 0 * (2 : ℝ) ^ F.T 0 ≤ p.N k ^ (2 * h) := by
      rw [show (2 : ℝ) * h = h + h by ring, Real.rpow_add hN0]
      exact mul_le_mul hT hT (by positivity) (by positivity)
    have hinvT : (p.N k ^ (2 * h))⁻¹ ≤ ((4 : ℝ) ^ F.T 0)⁻¹ := by
      rw [h4eq]; exact inv_anti₀ (by positivity) hT2
    have hinvκ : (p.N k ^ e)⁻¹ ≤ F.κ⁻¹ := inv_anti₀ hκpos hκ
    calc p.N k ^ (-(nw 0 + band)) * (p.N k ^ (2 * h))⁻¹ * (p.N k ^ e)⁻¹ * (2 : ℝ) ^ F.T 0
        ≤ p.N k ^ (-(nw 0 + band)) * ((4 : ℝ) ^ F.T 0)⁻¹ * F.κ⁻¹ * (2 : ℝ) ^ F.T 0 := by
          gcongr
      _ = p.N k ^ (-(nw 0 + band)) * ((4 : ℝ) ^ F.T 0)⁻¹ * ((2 : ℝ) ^ F.T 0 / F.κ) := by
          ring
  refine le_trans hg (le_trans ?_ hrhs)
  have hpow : p.N k ^ (-(nw 1 - band) + A) ≤
      p.N k ^ (-ϑ + (-(nw 0 + band) - 2 * h - e)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  refine hpow.trans (le_of_eq ?_)
  rw [Real.rpow_add hN0, Real.rpow_sub hN0, Real.rpow_sub hN0]
  field_simp

end
end Submission.Obl.k4_raw_localized_native_systems
